-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Lemmas.Protocol.UnitObject
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ring
import Lemmas.Kernel.ElectSource
import Lemmas.Protocol.ObjectSource
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The P barriers are unit objects

Stage `st`'s P-full barrier (shared offset `96 + 8 st`, count 256) is arrived on by the stage's 128
softmax lanes and the 128 correction lanes of the CTA (`pLane`), its second P barrier (`112 + 8 st`,
count 4) by one lane of each of the stage's four softmax warps: the one that wins the warp's
elections (`p2Prod`). The MMA warp polls both, with the parity of its earlier polls (`pObj`,
`p2Obj`: `MbarRing.Unit.Obj` with offset 0). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The lanes of the MMA warp of lane `g`'s CTA. -/
def MmaIn (L : Launch) (g h : Nat) : Prop :=
  h < L.threads ∧ h / L.block = g / L.block ∧ Prologue.warpIndex L h = 12

/-- Producer `a` of stage `st`'s P-full barrier of CTA `c`: softmax lane `a` of the stage, or
correction lane `a - 128`. -/
def pLane (L : Launch) (c st : Nat) (a : Fin 256) : Nat :=
  if a.val < 128 then c * L.block + 128 * st + a.val else c * L.block + 128 + a.val

theorem pLane_inj (c : Nat) {st : Nat} (hst : st < 2) : Function.Injective (pLane L c st) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  unfold pLane at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- A softmax lane of the stage, or a correction lane, of CTA `c` is a producer. -/
theorem pLane_of (hp : Pre p L m) {c st h : Nat} (hc : h / L.block = c)
    (hw : (Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st) ∨
      (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11)) : ∃ a, h = pLane L c st a := by
  have hb := hp.block
  have hm := Nat.div_add_mod h L.block
  rw [hc] at hm
  simp only [Prologue.warpIndex, hb] at hw hm
  rcases hw with ⟨h8, hs⟩ | ⟨h8, h11⟩
  · refine ⟨⟨h % 512 - 128 * st, by omega⟩, ?_⟩
    simp only [pLane, hb]
    split_ifs <;> omega
  · refine ⟨⟨h % 512 - 128, by omega⟩, ?_⟩
    simp only [pLane, hb]
    split_ifs <;> omega

theorem pLane_facts (hp : Pre p L m) (c : Nat) {st : Nat} (hst : st < 2) (a : Fin 256) :
    pLane L c st a / L.block = c ∧
      ((Prologue.warpIndex L (pLane L c st a) < 8 ∧
          Prologue.warpIndex L (pLane L c st a) / 4 = st) ∨
        (8 ≤ Prologue.warpIndex L (pLane L c st a) ∧
          Prologue.warpIndex L (pLane L c st a) ≤ 11)) := by
  have hb := hp.block
  have ha := a.isLt
  unfold pLane Prologue.warpIndex
  rw [hb]
  split_ifs <;> constructor <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Who names a P-full barrier**: an MMA lane's poll, or a producer's unit release arrival. -/
theorem p_use (st : Fin 2) {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (96 + 8 * st.val)))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g (96 + 8 * st.val)) c) :
    h / L.block = g / L.block ∧
      ((∃ ok, Prologue.warpIndex L h = 12 ∧ e.kind = .wait (obj L g (96 + 8 * st.val))
          (okPolls (obj L g (96 + 8 * st.val)) ((X.tr h).take k) % 2) ok true .cta) ∨
        e.kind = .arrive (obj L g (96 + 8 * st.val)) 0 1 true .cta ∧
          ((Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st.val) ∨
            (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11))) := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  refine ⟨hc, ?_⟩
  cases hu with
  | mmaPoll ok hw _ hk => exact .inl ⟨ok, hw, hk⟩
  | corrArr hw _ hk => exact .inr ⟨hk, .inr hw⟩
  | softArr a hw ha ho hk => exact .inr ⟨hk, .inl ⟨hw, by omega⟩⟩
  | epiPoll _ _ _ ho | epiArr _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho
  | ldAsync _ ho => omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega

/-- **Who names a second P barrier**: an MMA lane's poll, or a softmax lane's unit release
arrival. -/
theorem p2_use (st : Fin 2) {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hm : MbarOf e (obj L g (112 + 8 * st.val)))
    (hni : ∀ c, e.kind ≠ .mbInit (obj L g (112 + 8 * st.val)) c) :
    h / L.block = g / L.block ∧
      ((∃ ok, Prologue.warpIndex L h = 12 ∧ e.kind = .wait (obj L g (112 + 8 * st.val))
          (okPolls (obj L g (112 + 8 * st.val)) ((X.tr h).take k) % 2) ok true .cta) ∨
        e.kind = .arrive (obj L g (112 + 8 * st.val)) 0 1 true .cta ∧
          Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st.val) := by
  obtain ⟨hc, hu⟩ := bar_use hp hX hFw he hm hni
  refine ⟨hc, ?_⟩
  cases hu with
  | mmaPoll ok hw _ hk => exact .inl ⟨ok, hw, hk⟩
  | softArr a hw ha ho hk => exact .inr ⟨hk, hw, by omega⟩
  | epiPoll _ _ _ ho | epiArr _ _ ho | corrPoll _ _ ho | softPoll _ _ _ _ ho
  | corrArr _ ho | ldAsync _ ho => omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega

end

theorem p_init (st : Fin 2) : initOff ⟨12 + st.val, by omega⟩ = 96 + 8 * st.val ∧
    initCnt ⟨12 + st.val, by omega⟩ = 256 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

theorem p2_init (st : Fin 2) : initOff ⟨14 + st.val, by omega⟩ = 112 + 8 * st.val ∧
    initCnt ⟨14 + st.val, by omega⟩ = 4 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Stage `st`'s P-full barrier is a unit object** of its 256 producers. -/
theorem pObj (g : Nat) (st : Fin 2) :
    PTX.MbarRing.Unit.Obj X (obj L g (96 + 8 * st.val)) 256 (pLane L (g / L.block) st.val) 0 := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (96 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (96 + 8 * st.val)) c) =>
    p_use hp hX hFw st he hm hni
  obtain ⟨hloc, hcnt⟩ := p_init st
  refine ⟨by decide, pLane_inj _ st.isLt, fun r hr => ?_, ?_, ?_,
    fun {h k pc par acq sc} he => ?_, Nat.zero_le _⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨hc, ⟨_, _, hk⟩ | ⟨hk, hw⟩⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        obtain ⟨a, ha'⟩ := pLane_of hp hc hw
        exact .arrive hid ⟨a, ha'⟩ he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with
        ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
  · rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  · rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      omega
    · cases hk

/-! ### The second P barrier -/

/-- Thread `h` arrives on stage `st`'s second P barrier of lane `g`'s CTA. -/
def P2Arrives (L : Launch) (X : Execution) (g st h : Nat) : Prop :=
  ∃ k pc tx cnt rel sc, X.get (h, k) = some ⟨pc, .arrive (obj L g (112 + 8 * st)) tx cnt rel sc⟩

/-- Thread `h` is of warp `a` of stage `st`'s softmax warps of lane `g`'s CTA. -/
def InP2Warp (L : Launch) (g st : Nat) (a : Fin 4) (h : Nat) : Prop :=
  h / L.block = g / L.block ∧ Prologue.warpIndex L h = 4 * st + a.val

open Classical in
/-- Producer `a` of stage `st`'s second P barrier: the thread of warp `a` that arrives on it, or the
warp's first thread when none does. -/
def p2Prod (L : Launch) (X : Execution) (g st : Nat) (a : Fin 4) : Nat :=
  if h : ∃ y, InP2Warp L g st a y ∧ P2Arrives L X g st y then Classical.choose h
  else g / L.block * L.block + 32 * (4 * st + a.val)

omit hX hFw in
theorem p2Prod_spec {st : Nat} (hst : st < 2) (a : Fin 4) :
    InP2Warp L g st a (p2Prod L X g st a) := by
  unfold p2Prod
  split
  · next h => exact (Classical.choose_spec h).1
  · have ha := a.isLt
    unfold InP2Warp Prologue.warpIndex
    rw [hp.block]
    constructor <;> omega

omit hX hFw in
theorem p2Prod_inj {st : Nat} (hst : st < 2) : Function.Injective (p2Prod L X g st) := by
  intro a b h
  have ha := p2Prod_spec (X := X) (g := g) hp hst a
  have hb := p2Prod_spec (X := X) (g := g) hp hst b
  rw [h] at ha
  have h1 := ha.2
  have h2 := hb.2
  exact Fin.ext (by omega)

/-- A second P arrival is a softmax lane's of the stage, with the stage's objects its own. -/
theorem p2_arr {st : Nat} (hst : st < 2) {h k pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L g (112 + 8 * st)) tx c rel sc⟩) :
    h / L.block = g / L.block ∧ Prologue.warpIndex L h < 8 ∧ Prologue.warpIndex L h / 4 = st ∧
      ∀ a, sobj L h a = obj L g (a + 8 * st) := by
  rcases p2_use hp hX hFw ⟨st, hst⟩ he rfl (fun _ h => by cases h) with
    ⟨hc, ⟨_, _, hk⟩ | ⟨-, hw, hs⟩⟩
  · cases hk
  · simp only at hs
    refine ⟨hc, hw, hs, fun a => ?_⟩
    rw [sobj, hs, obj_cta hc, Nat.add_comm]

/-- **The threads of a warp that arrive on a second P barrier are one thread.** -/
theorem p2_arrive_unique {st h h' : Nat} (hst : st < 2) (hs : SameWarp L h h')
    (ha : P2Arrives L X g st h) (ha' : P2Arrives L X g st h') : h = h' := by
  obtain ⟨k, pc, tx, cnt, rel, sc, hk⟩ := ha
  obtain ⟨k', pc', tx', cnt', rel', sc', hk'⟩ := ha'
  obtain ⟨-, hw, -, ho⟩ := p2_arr hp hX hFw hst hk
  obtain ⟨-, hw', -, ho'⟩ := p2_arr hp hX hFw hst hk'
  rw [← ho] at hk
  rw [← ho'] at hk'
  obtain ⟨j, pcj, ij, -, hj⟩ := soft_p2_won hp hX hFw hw hk
  obtain ⟨j', pcj', ij', -, hj'⟩ := soft_p2_won hp hX hFw hw' hk'
  exact won_unique hX hs hj hj'

/-- **An arriving thread is a producer.** -/
theorem p2Prod_of {st h : Nat} (hst : st < 2) (ha : P2Arrives L X g st h) :
    ∃ a, h = p2Prod L X g st a := by
  obtain ⟨k, pc, tx, cnt, rel, sc, hk⟩ := id ha
  obtain ⟨hc, hw, hs, -⟩ := p2_arr hp hX hFw hst hk
  refine ⟨⟨Prologue.warpIndex L h % 4, by omega⟩, ?_⟩
  have hin : InP2Warp L g st ⟨Prologue.warpIndex L h % 4, by omega⟩ h :=
    ⟨hc, by simp only; omega⟩
  have hex : ∃ y, InP2Warp L g st ⟨Prologue.warpIndex L h % 4, by omega⟩ y ∧
      P2Arrives L X g st y := ⟨h, hin, ha⟩
  unfold p2Prod
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨⟨hc', hw'⟩, harr⟩ := Classical.choose_spec hex
  have hlt : Classical.choose hex < L.threads := by
    obtain ⟨_, _, _, _, _, _, hg⟩ := id harr
    exact Frame.lt_of_get hX hg
  refine p2_arrive_unique hp hX hFw hst ⟨⟨Frame.lt_of_get hX hk, hlt, hc.trans hc'.symm⟩, ?_⟩
    ha harr
  have h1 := hin.2
  simp only [Prologue.warpIndex] at h1 hw'
  simp only [Prologue.warpIndex]
  omega

/-- **The second P arrivals of the elected lane are one per round**: a lane that arrives wins every
election of its warp (one leader per warp), so its arrival follows one more S-full poll than its
earlier arrivals. -/
theorem p2_round {st : Nat} (hst : st < 2) {h k pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L g (112 + 8 * st)) tx c rel sc⟩) :
    arrivals (obj L g (112 + 8 * st)) ((X.tr h).take k) + 1 =
      okPolls (obj L g (80 + 8 * st)) ((X.tr h).take k) := by
  obtain ⟨-, hw, -, ho⟩ := p2_arr hp hX hFw hst he
  rw [← ho] at he
  rw [← ho, ← ho]
  obtain ⟨j, pcj, ij, -, hj⟩ := soft_p2_won hp hX hFw hw he
  refine (soft_p2_arr hp hX hFw hw he).2 fun i pci mask inst ld hi => ?_
  have hm := elect_full hX (show X.Elect (h, i) pci mask inst ld from hi)
  subst hm
  have hh := Frame.lt_of_get hX hi
  exact elect_leader hX (e := (h, i)) (f := (h, j)) hi hj ⟨⟨hh, hh, rfl⟩, rfl⟩

/-- **Stage `st`'s second P barrier is a unit object** of its 4 producers. -/
theorem p2Obj (g : Nat) (st : Fin 2) :
    PTX.MbarRing.Unit.Obj X (obj L g (112 + 8 * st.val)) 4 (p2Prod L X g st.val) 0 := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (obj L g (112 + 8 * st.val)))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g (112 + 8 * st.val)) c) =>
    p2_use hp hX hFw st he hm hni
  obtain ⟨hloc, hcnt⟩ := p2_init st
  refine ⟨by decide, p2Prod_inj hp st.isLt, fun r hr => ?_, ?_, ?_,
    fun {h k pc par acq sc} he => ?_, Nat.zero_le _⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨hc, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        exact .arrive hid (p2Prod_of hp hX hFw st.isLt ⟨j, pc, 0, 1, true, _, he⟩) he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with
        ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩ <;> cases hk
  · rw [← hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  · rcases hU he rfl (fun _ h => by cases h) with ⟨-, ⟨_, _, hk⟩ | ⟨hk, -⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      omega
    · cases hk

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
