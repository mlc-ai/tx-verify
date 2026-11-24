-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk2Bar0
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Role
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Pro

@[expose] public section

/-!
# Warp lockstep: the agreement premise, split into the softmax's and the rest

`LaneAgree` (`LkMachine.lean`) is the agreement of two lanes of a warp at their synchronizing
events on what steers the branch to the next synchronizing event. Its rows belong to two groups:
the softmax region's lazy-rescale decision (`SmAgree`, a value chain through shared memory), and
every other row (`ProAgree`, `WAgree`: the prologue's guards, the worker dispatch, the loader's
and the MMA warp's loop ends). `LaneAgreeSm` and `LaneAgreeRest` are the two groups, as the same
statement as `LaneAgree` with the group's relation, and `laneAgree_of` is the adapter.
`laneAgreeRest_of` proves the second group.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (SmAgree ProAgree WAgree proSy roleIdx exL exM exW)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The agreement of the softmax region's lanes (`SmAgree`). -/
def tAgreeSm (L : Launch) (g h : Nat) : TSt → TSt → Event → Event → Prop
  | .d (.sm d), .d (.sm d'), e, e' => SmAgree L g h d d' e e'
  | _, _, _, _ => True

/-- The agreement of the other lanes: the prologue's guards and the workers'. -/
def tAgreeRest (L : Launch) (g h : Nat) : TSt → TSt → Event → Event → Prop
  | .d (.pro d), .d (.pro d'), _, _ => ProAgree L g h d d'
  | .w s, .w s', e, e' => WAgree L g h s s' e e'
  | _, _, _, _ => True

theorem tAgree_of {g h : Nat} {s s' : TSt} {e e' : Event} (h1 : tAgreeSm L g h s s' e e')
    (h2 : tAgreeRest L g h s s' e e') : tAgree L g h s s' e e' := by
  cases s with
  | d a => cases s' with
    | d b => cases a <;> cases b <;> first | exact h1 | exact h2
    | w b => trivial
  | w a => cases s' with
    | d b => trivial
    | w b => exact h2

/-- **The agreement premise for a relation on the lanes' states.** -/
def LaneAgreeWith (Q : Params) (L : Launch) (X : Execution)
    (R : Nat → Nat → TSt → TSt → Event → Event → Prop) : Prop :=
  ∀ n, (∀ m, m ≤ n → Lock (kernelSkel Q L) X m) → ∀ {g h a b : Nat} {s s' : TSt} {e e' : Event},
    SameWarp L g h → (X.tr g)[a]? = some e → (X.tr h)[b]? = some e' →
    St Q L X g a = some (some s) → St Q L X h b = some (some s') →
    (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' → syN (kernelSkel Q L) X g a = n →
    syN (kernelSkel Q L) X h b = n →
    (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → R g h s s' e e'

/-- The softmax region's half of `LaneAgree`: both lanes take the lazy-rescale branch or neither. -/
def LaneAgreeSm (Q : Params) (L : Launch) (X : Execution) : Prop :=
  LaneAgreeWith Q L X (tAgreeSm L)

/-- The other half of `LaneAgree`. -/
def LaneAgreeRest (Q : Params) (L : Launch) (X : Execution) : Prop :=
  LaneAgreeWith Q L X (tAgreeRest L)

/-- **The adapter**: `LaneAgree` follows from its two halves. -/
theorem laneAgree_of (hs : LaneAgreeSm Q L X) (hr : LaneAgreeRest Q L X) : LaneAgree Q L X := by
  intro n hL g h a b s s' e e' hw he he' hsa hsb hsy hsy' hna hnb hk
  exact tAgree_of (hs n hL hw he he' hsa hsb hsy hsy' hna hnb hk)
    (hr n hL hw he he' hsa hsb hsy hsy' hna hnb hk)

/-- **The non-softmax rows of the agreement premise.** -/
theorem laneAgreeRest_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hRR : RoleReads L X) (hb : Bar0Counters Q L X)
    (hns : NoSkip Q L X) : LaneAgreeRest Q L X := by
  intro n hL g h a b s s' e e' hw he he' hsa hsb hsy hsy' hna hnb hk
  have ha : a ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hb' : b ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1.le
  have hpc : TSt.pc s = TSt.pc s' := by
    rw [← (kernelSkel Q L).pc_key (g := g) hsy, ← (kernelSkel Q L).pc_key (g := h) hsy', hk]
  have hcnt := counters_lock hf.tracked hb hns n hL hw ha hb' hsa hsb hsy hsy' hna hnb
  cases s with
  | d s0 =>
    cases s' with
    | w s1 => cases s0 <;> exact trivial
    | d s1 =>
      cases s0 <;> cases s1 <;> try exact trivial
      rename_i d0 d1
      have hsy0 : proSy d0 = true := hsy
      have hsy1 : proSy d1 = true := hsy'
      have hsite := PTX.Kernels.InklingRelDecode.Proof.Lk.pro_site_eq hsy0 hsy1 hpc
      exact proAgree_of hpre hX hf hw hsa hsb hsy0 hsite
  | w s0 =>
    cases s' with
    | d s1 => cases s0 <;> exact trivial
    | w s1 =>
      have hs0 : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s0 = true := hsy
      have hs1 : PTX.Kernels.InklingRelDecode.Proof.Lk.wSy s1 = true := hsy'
      have hpc' : WComp.pc s0 = WComp.pc s1 := hpc
      cases s0 with
      | worker d0 =>
        cases s1 <;> try exact trivial
        rename_i d1
        intro hd
        obtain ⟨site, P⟩ := d0
        obtain ⟨site', P'⟩ := d1
        simp only at hd
        subst hd
        have hsite : site' = .ldRole := by
          revert hpc' hs1
          cases site' <;> simp [WComp.pc, PTX.Kernels.InklingRelDecode.Proof.Lk.wSy,
            PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole, Worker.Site.pc]
        subst hsite
        exact ldRole_agree hpre hX hf hRR hL hw he he' hsa hsb hna hnb
      | idle d0 => cases s1 <;> exact trivial
      | exit d0 => cases s1 <;> exact trivial
      | loader d0 P0 =>
        cases s1 <;> try exact trivial
        rename_i d1 P1
        have hd := loader_site_eq (PTX.Kernels.InklingRelDecode.Proof.Lk.sy_loader hs0)
          (PTX.Kernels.InklingRelDecode.Proof.Lk.sy_loader hs1) hpc'
        refine ⟨fun h0 => ?_, fun h0 => ?_⟩
        · have h1 : d1.site = .bar0 := hd ▸ h0
          obtain ⟨c1, c2⟩ := hb.loader hw hsa hsb h0 h1
          rw [c1, c2]
        · have h1 : d1.site = .el3 := hd ▸ h0
          simp only [exT, exW, exL, h0, h1, Prod.mk.injEq] at hcnt
          rw [hcnt.1, hcnt.2]
      | mma d0 P0 =>
        cases s1 <;> try exact trivial
        rename_i d1 P1
        have hk0 := hns hw.1.1 hsa
        have hk1 := hns hw.1.2.1 hsb
        have hd := Mma.Site.eq_of_pc hk0 hk1 hpc'
        refine ⟨hk0, hk1, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
        · have h1 : d1.site = .bar0 := hd ▸ h0
          obtain ⟨c1, c2⟩ := hb.mma hw hsa hsb h0 h1
          simp only [Mma.start, c2]
          by_cases hn0 : d1.n = 0 ∨ 2147483646 < d1.n <;> simp [hn0]
        · have h1 : d1.site = .qkElect := hd ▸ h0
          simp only [exT, exW, exM, h0, h1, Prod.mk.injEq] at hcnt
          simp only [Mma.afterQk, Mma.iterNext, hcnt.1, hcnt.2]
          by_cases hi0 : d1.i = 0 <;> simp [hi0]
        · have h1 : d1.site = .pvElect := hd ▸ h0
          simp only [exT, exW, exM, h0, h1, Prod.mk.injEq] at hcnt
          simp only [Mma.iterNext, hcnt.1, hcnt.2]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
