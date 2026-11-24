-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Lemmas.Protocol.TmaUnits
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ring
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The full barriers of the loader's TMA copies

The Q and bias full barriers (0, 8, 320, 328) are updated by one lane of warp 14, the one that wins
the warp's elections: expect-tx arrivals of 32768 bytes and tensor copies of 16384 (`TmaBytes`). So
each is a `MbarRing.TmaUnits.Obj` of that lane (`tmaFull`), and its items follow the lane's polls of
the empty barrier 16 bytes past it (`tmaFull_pol`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Every tensor copy moves 16384 bytes (the descriptors of the kernel's fourteen copies). -/
def TmaBytes (X : Execution) : Prop :=
  ∀ i pc a s, X.get i = some ⟨pc, .tensorIssue a s⟩ → TensorTransfer.bytes s.descriptor = 16384

open Classical in
/-- The lane that won an election of warp 14 of lane `g`'s CTA (the warp's first lane when none
did). -/
def tmaLane (L : Launch) (X : Execution) (g : Nat) : Nat :=
  if h : ∃ y j pc inst, y / L.block = g / L.block ∧ Prologue.warpIndex L y = 14 ∧
      X.get (y, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst (laneOf L y)⟩
  then Classical.choose h else g / L.block * L.block + 448

theorem tma_init {o : Nat} (ho : LdTmaOff o) : ∃ q, initOff q = o ∧ initCnt q = 1 := by
  rcases ho with rfl | rfl | rfl | rfl <;> decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)

include hX in
theorem tmaLane_eq {y j pc inst : Nat} (hc : y / L.block = g / L.block)
    (hw : Prologue.warpIndex L y = 14)
    (he : X.get (y, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst (laneOf L y)⟩) :
    y = tmaLane L X g := by
  have hex : ∃ y j pc inst, y / L.block = g / L.block ∧ Prologue.warpIndex L y = 14 ∧
      X.get (y, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst (laneOf L y)⟩ :=
    ⟨y, j, pc, inst, hc, hw, he⟩
  unfold tmaLane
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨j', pc', i', hc', hw', he'⟩ := Classical.choose_spec hex
  refine won_unique hX ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he', hc.trans hc'.symm⟩, ?_⟩
    he he'
  simp only [Prologue.warpIndex] at hw hw' ⊢
  omega

include hp in
theorem tmaLane_in (g : Nat) : tmaLane L X g / L.block = g / L.block ∧
    Prologue.warpIndex L (tmaLane L X g) = 14 := by
  by_cases hex : ∃ y j pc inst, y / L.block = g / L.block ∧ Prologue.warpIndex L y = 14 ∧
      X.get (y, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst (laneOf L y)⟩
  · have hs : tmaLane L X g = Classical.choose hex := by
      unfold tmaLane
      rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨j', pc', i', hc', hw', -⟩ := Classical.choose_spec hex
    rw [hs]
    exact ⟨hc', hw'⟩
  · have he : tmaLane L X g = g / L.block * L.block + 448 := by
      unfold tmaLane
      rw [dite_eq_right_of_eq_false (eq_false hex)]
    have hb := hp.block
    rw [he]
    simp only [Prologue.warpIndex, hb]
    omega

include hp hX hFw

/-- An expect-tx arrival on a TMA full barrier. -/
theorem tma_arr {o h k pc tx cnt : Nat} {rel : Bool} {sc : MbarScope} (ho : LdTmaOff o)
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L g o) tx cnt rel sc⟩) :
    h = tmaLane L X g ∧ tx = 32768 ∧ cnt = 1 ∧
      arrivals (obj L g o) ((X.tr h).take k) + 1 ≤
        okPolls (obj L g (o + 16)) ((X.tr h).take k) := by
  obtain ⟨hc, hu⟩ := bar_use (o := o) hp hX hFw he rfl (fun _ h => by cases h)
  cases hu with
  | epiPoll _ _ _ _ hk | corrPoll _ _ _ hk | softPoll _ _ _ _ _ hk | mmaPoll _ _ _ hk
  | mmaCommit _ _ _ hk | ldPoll _ _ _ _ hk | ldAsync _ _ hk | ldCopy _ _ _ _ hk => cases hk
  | epiArr _ _ ho' | corrArr _ ho' | softArr _ _ _ ho' =>
    unfold LdTmaOff at ho
    omega
  | ldArr tx' hw _ hk =>
    simp only [Kind.arrive.injEq] at hk
    obtain ⟨-, -, rfl, rfl, rfl⟩ := hk
    rw [← obj_cta hc] at he
    obtain ⟨h14, htx, hb, j, pcj, mask, inst, -, hj⟩ := ld_tma_arr hp hX hFw hw ho he
    rw [obj_cta hc, obj_cta hc] at hb
    exact ⟨tmaLane_eq hX hc h14 (elect_full hX hj ▸ hj), htx, rfl, hb⟩

/-- A tensor copy on a TMA full barrier. -/
theorem tma_copy {o h k pc a : Nat} {sp : TensorCopy.Spec} (ho : LdTmaOff o)
    (he : X.get (h, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L g o) :
    h = tmaLane L X g ∧ ((X.tr h).take k).countP (issuesTo (obj L g o)) + 1 ≤
      2 * okPolls (obj L g (o + 16)) ((X.tr h).take k) := by
  obtain ⟨hc, hu⟩ := bar_use (o := o) hp hX hFw he hm (fun _ h => by cases h)
  cases hu with
  | epiPoll _ _ _ _ hk | corrPoll _ _ _ hk | softPoll _ _ _ _ _ hk | mmaPoll _ _ _ hk
  | mmaCommit _ _ _ hk | ldPoll _ _ _ _ hk | ldAsync _ _ hk | ldArr _ _ _ hk
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk => cases hk
  | ldCopy a' sp' hw _ hk hb' =>
    cases hk
    rw [← obj_cta hc] at hm
    obtain ⟨h14, hb, j, pcj, mask, inst, -, hj⟩ := ld_tma_copy hp hX hFw hw ho he hm
    rw [obj_cta hc, obj_cta hc] at hb
    exact ⟨tmaLane_eq hX hc h14 (elect_full hX hj ▸ hj), hb⟩

/-- **A TMA full barrier's updates are one lane's.** -/
theorem tmaFull (hB : TmaBytes X) (g : Nat) {o : Nat} (ho : LdTmaOff o) :
    TmaUnits.Obj X (obj L g o) (tmaLane L X g) 2 16384 := by
  obtain ⟨q, hq, hcn⟩ := tma_init ho
  have hno : ∀ {h k pc : Nat} {kd : Kind}, X.get (h, k) = some ⟨pc, kd⟩ →
      MbarOf ⟨pc, kd⟩ (obj L g o) → (∃ noinc, kd = .asyncArrive (obj L g o) noinc) ∨
      (∃ s, kd = .copy s) ∨ (∃ s, kd = .tc (.commit s)) → False := by
    intro h k pc kd he hm hk
    obtain ⟨-, hu⟩ := bar_use (o := o) hp hX hFw he hm
      (fun c h => by rcases hk with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases h)
    cases hu with
    | mmaCommit _ _ ho' => unfold MmaCommitOff at ho'; unfold LdTmaOff at ho; omega
    | ldAsync _ ho' => unfold LdTmaOff at ho; omega
    | epiPoll _ _ _ _ hk' | corrPoll _ _ _ hk' | softPoll _ _ _ _ _ hk' | mmaPoll _ _ _ hk'
    | ldPoll _ _ _ _ hk' | ldArr _ _ _ hk' | epiArr _ _ _ hk' | corrArr _ _ hk'
    | softArr _ _ _ _ hk' | ldCopy _ _ _ _ hk' =>
      simp only at hk'
      rcases hk with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases hk'
  refine ⟨?_, AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _, ?_, ?_, ?_⟩
  · have := obj_initFirst hp hX hFw g q
    rwa [hq, hcn] at this
  · intro r hr ha
    cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | tensor _ _ _ ha'
    | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha' | clc _ _ _ _ ha' =>
      rw [ha] at ha'; cases ha'
    | increment hid he _ => exact hno he rfl (.inl ⟨_, rfl⟩)
  · intro k c tx r hr ha
    cases AsyncCopy.record_source hX.tma.2.2.1 (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | increment _ _ ha'
    | bulk _ _ _ _ ha' => rw [ha] at ha'; cases ha'
    | @arrive h j pc tx' cnt rel sc hid he ha' =>
      rw [ha] at ha'
      simp only [MBarrier.Action.arrive.injEq] at ha'
      obtain ⟨rfl, rfl⟩ := ha'
      obtain ⟨rfl, rfl, rfl, -⟩ := tma_arr hp hX hFw ho he
      exact ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩
    | arriveOn hid he hm _ _ =>
      subst hm
      exact (hno he rfl (.inl ⟨_, rfl⟩)).elim
    | commit hid he ht _ => exact (hno he ⟨_, ht⟩ (.inr (.inr ⟨_, rfl⟩))).elim
    | clc hid he _ _ _ => exact (no_clc hp hX hFw _ _ _ _ _ he).elim
  · intro k b r hr ha
    cases AsyncCopy.record_source hX.tma.2.2.1 (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | increment _ _ ha'
    | arriveOn _ _ _ _ ha' | commit _ _ _ ha' => rw [ha] at ha'; cases ha'
    | clc hid he _ _ _ => exact (no_clc hp hX hFw _ _ _ _ _ he).elim
    | bulk hid he hc _ _ => exact (hno he hc (.inr (.inl ⟨_, rfl⟩))).elim
    | @tensor i pc a sp hid he hm ha' =>
      rw [ha] at ha'
      simp only [MBarrier.Action.completeTx.injEq] at ha'
      rw [hB i pc a sp he] at ha'
      obtain ⟨h, j⟩ := i
      obtain ⟨rfl, -⟩ := tma_copy hp hX hFw ho he hm
      exact ⟨ha', j, pc, a, sp, hid, he, hm⟩

/-- **An item of use `t` follows `t + 1` polls of the empty barrier.** -/
theorem tmaFull_pol (hB : TmaBytes X) (g : Nat) {o : Nat} (ho : LdTmaOff o)
    {x : Fin 3 × Nat} (hx : x ∈ TmaUnits.S X (obj L g o) (tmaLane L X g) 2 16384) :
    ∃ i, TmaUnits.op X (obj L g o) (tmaLane L X g) 2 x.1 x.2 = (tmaLane L X g, i) ∧
      i < (X.tr (tmaLane L X g)).length ∧
      x.2 + 1 ≤ okPolls (obj L g (o + 16)) ((X.tr (tmaLane L X g)).take i) := by
  obtain ⟨-, h0, h1⟩ := (tmaFull hp hX hFw hB g ho).source hx
  refine ⟨_, rfl, ?_⟩
  have hx3 := x.1.isLt
  by_cases hk : x.1.val = 0
  · obtain ⟨⟨pc, rel, sc, he⟩, hcnt⟩ := h0 hk
    refine ⟨len_of_get he, ?_⟩
    obtain ⟨-, -, -, hb⟩ := tma_arr hp hX hFw ho
      (h := tmaLane L X g) (k := (TmaUnits.op X (obj L g o) (tmaLane L X g) 2 x.1 x.2).2) he
    rw [hcnt] at hb
    exact hb
  · obtain ⟨⟨pc, al, sp, he, hm⟩, hcnt⟩ := h1 hk
    refine ⟨len_of_get he, ?_⟩
    obtain ⟨-, hb⟩ := tma_copy hp hX hFw ho
      (h := tmaLane L X g) (k := (TmaUnits.op X (obj L g o) (tmaLane L X g) 2 x.1 x.2).2) he hm
    rw [hcnt] at hb
    change x.2 + 1 ≤ okPolls _ ((X.tr (tmaLane L X g)).take
      (TmaUnits.op X (obj L g o) (tmaLane L X g) 2 x.1 x.2).2)
    generalize okPolls (obj L g (o + 16)) _ = u at hb ⊢
    omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
