-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact

@[expose] public section

/-! # The loader's successful polls of the Q stages' empty barriers

Standalone fact (following does not read it). Warp 14 polls the Q stages' empty barriers (offset
16 or 24) once at TMA group 0's wait (offset 16) or group 2's (offset 24) in the first block, and
once more at the drain's wait (offset 24); at the drain and the second pass it has polled the
first block's only with a tile (some commit). Warp 15 polls neither barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Scan)

noncomputable section

/-- The successful polls of the Q stage at offset `o` before a state of warp `w`, after `A`
commits (`A` is read only at the second pass and the drain, as `A = 0`). -/
def qAcq (w : Nat) (s : Site) (A o : Nat) : Nat :=
  if w = 14 then
    match s with
    | .tw t => if (if o = 16 then 0 else 2) < t.val then 1 else 0
    | .te t _ | .ta t | .tc t _ => if (if o = 16 then 0 else 2) ≤ t.val then 1 else 0
    | .pgLd per _ | .pgSt per _ | .rwSt per _ => match per with | .prime => 0 | _ => 1
    | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
    | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
      match per with | .prime => if v then 1 else 0 | _ => 1
    | .dw _ | .dq => if A = 0 then 0 else 1
    | .de | .da | .exit => (if A = 0 then 0 else 1) + if o = 24 then 1 else 0
    | .word sk | .down sk | .up sk _ | .total sk => if sk.late ∧ A ≠ 0 then 1 else 0
    | .vote l | .pre l | .tiles l => if l ∧ A ≠ 0 then 1 else 0
    | _ => 0
  else 0

/-- `qAcq` reads the commits only as zero or not. -/
theorem qAcq_one (w : Nat) (s : Site) (A o : Nat) :
    qAcq w s A o = qAcq w s (if A = 0 then 0 else 1) o := by
  by_cases hA : A = 0
  · subst hA; rfl
  · simp only [hA, ↓reduceIte]
    cases s <;> simp [qAcq, hA]

/-- The commits are zero (`z`) only where the commits before the block are and no warm or steady
packet is current, and they are those
before the block at a site that reads neither position. -/
def zOk (s : Site) (z : Bool) : Bool :=
  (!z || (kOff s == 0 && !s.readsK)) && (s.readsK || s.readsA || z == (kOff s == 0))

/-- The edge check for both warps, both offsets and both cases of the commits. -/
def qChk (b : Bool) (s s' : Site) : Bool :=
  [16, 24].all fun o => [false, true].all fun z => !zOk s z ||
    qAcq (if b then 15 else 14) s' (if z && tag s s' != .commit then 0 else 1) o ==
      qAcq (if b then 15 else 14) s (if z then 0 else 1) o + if tag s s' = .acq o then 1 else 0

theorem q_edges : Edges qChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state of warp `w`. -/
def QAcq (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ o ∈ [16, 24], dn.2 (.acquire (bl L g o)) = qAcq w dn.1.site (dn.2 .commit) o

variable {p : Params} {L : Launch} {g w : Nat}

/-- The published packets read `k` and `A` only upwards. -/
theorem kOff_le (s : Site) (k A : Nat) : kOff s ≤ arrAt s k A + (inPkt s).2 := by
  unfold kOff
  by_cases hk : s.readsK = true
  · rw [arrAt_readsK hk k A]; omega
  by_cases hA : s.readsA = true
  · rw [(arrAt_readsA hA 0 0).1]; omega
  · rw [(forms_pos (k := k) (A := A) (k' := 0) (A' := 0) (fun h => absurd h hk)
      (fun h => absurd h hA)).1]

/-- A site that reads `k` is of a warm or steady class. -/
theorem cls_of_readsK {s : Site} (h : s.readsK = true) :
    ringCls s = .later ∨ ∃ f, ringCls s = .warm f := by
  cases s
  case tw t | te t _ | ta t | tc t _ =>
    have h4 : ¬ t.val < 4 := by simpa [Site.readsK] using h
    simp only [ringCls, h4, ↓reduceIte]
    split <;> simp
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | ptP per _ _ | ptR per _ _
    | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _ | cp per _ _ _ | commit per _
    | arrive per _ => cases per <;> simp_all [ringCls, Site.readsK]
  all_goals simp [Site.readsK] at h

theorem z_ok {dn : D × (Cnt → Nat)} (hJ : Ref p L g w dn) :
    zOk dn.1.site (decide (dn.2 .commit = 0)) = true := by
  have hc := hJ.commit
  have h1 := kOff_le dn.1.site (posK dn) (posA dn)
  have hk2 : dn.1.site.readsK = true → dn.2 .commit ≠ 0 := fun hs => by
    have hW := hJ.words
    have h2 : 2 ≤ posK dn := by
      rcases cls_of_readsK hs with h | ⟨f, h⟩ <;> rw [h] at hW
      · exact hW.2
      · exact hW.1.2
    simp only [posK] at h2
    omega
  by_cases h : dn.2 .commit = 0
  · have hk : dn.1.site.readsK = false := by
      cases hs : dn.1.site.readsK
      · rfl
      · exact absurd h (hk2 hs)
    have h0 : kOff dn.1.site = 0 := by omega
    simp [zOk, h, hk, h0]
  by_cases hk : dn.1.site.readsK = true
  · simp [zOk, h, hk]
  by_cases hA : dn.1.site.readsA = true
  · simp [zOk, h, hA]
  have := (forms_pos (k := posK dn) (A := posA dn) (k' := 0) (A' := 0) (fun h => absurd h hk)
    (fun h => absurd h hA)).1
  have hk0 : dn.2 .commit = kOff dn.1.site := by rw [hc, kOff, this]
  have h0 : kOff dn.1.site ≠ 0 := by omega
  simp [zOk, h, h0]

theorem q_step (hw : w = 14 ∨ w = 15) {dn : D × (Cnt → Nat)} {e : Event} {d' : D}
    (hJ : Ref p L g w dn) (hm : Move L g w dn e d') (h : QAcq L g w dn) :
    QAcq L g w (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  have hz := z_ok hJ
  have hc : qChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · simp [qChk, h', tag_self]
    · exact q_edges.ok h'
  have hw' : (if not14 w then 15 else 14) = w := by rcases hw with rfl | rfl <;> rfl
  intro o ho
  have hco := List.all_eq_true.mp (List.all_eq_true.mp hc o ho) (decide (n .commit = 0))
    (by cases decide (n .commit = 0) <;> simp)
  simp only [hz, hw', Bool.not_true, Bool.false_or, beq_iff_eq] at hco
  simp only [bump_tag hm]
  have h0 := h o ho
  simp only at h0
  rw [h0, qAcq_one w d'.site, qAcq_one w d.site]
  revert hco
  cases tag d.site d'.site <;>
    simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, bl, Loc.mk.injEq,
      true_and, ↓reduceIte, Nat.add_zero, Tag.acq.injEq, Nat.add_left_cancel_iff] <;> intro hco
  case acq o' => by_cases hx : o' = o <;> by_cases h0 : n .commit = 0 <;> simp_all
  case acqRing δ =>
    have hne : ¬ L.sharedBase + 56 + 8 * ((n .commit + δ) % 3) = L.sharedBase + o := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      omega
    have hne' : ¬ 56 + 8 * ((n .commit + δ) % 3) = o := fun h => hne (by omega)
    by_cases h0 : n .commit = 0
    · simp only [h0, Nat.zero_add] at hne'
      simp_all
    · simp_all
  all_goals (by_cases h0 : n .commit = 0 <;> simp_all)

/-- **The successful polls of the Q stages' empty barriers** at every state of a loader lane. -/
theorem q_acq {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : QAcq L g (wOf b) (d, LdWarp.lcn n) :=
  LdWarp.fact_at (I := QAcq L g)
    (fun b o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp [qAcq])
    (fun _ _ _ _ hw hJ hm h => q_step hw hJ hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
