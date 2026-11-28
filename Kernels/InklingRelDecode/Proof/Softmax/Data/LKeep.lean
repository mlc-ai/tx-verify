-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsMid
import Kernels.InklingRelDecode.Proof.Lib.Havoc

@[expose] public section

/-! # The running sum kept by the sites of the loop

The sum (register 1915) and, between its addition and the update, the round's row sum (register
1531) are written at pcs 944, 950 and 2235 only. The sites that neither start nor leave the round
keep them: their events write neither and the code up to the next event is in a region that
writes neither (`lIvs`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The sites whose data step keeps the running sum's facts. -/
def keepL : Site → Bool
  | .waitS | .shfl4 | .ldS | .waitLd | .shfl5 | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9
  | .shfl10 | .store10 | .bar23 | .ldL | .shfl11 | .ldO | .waitLdO | .bar24 | .stO | .bar20
  | .tmemSt | .tmemWait | .bar21 | .arrive | .nxt _ => true
  | _ => false

/-- The registers of the running sum's facts of a site. -/
def lK : Site → List Nat
  | .setMaxReg | .bar0 | .pre _ | .epilogue => []
  | s => if psB s then [1915, 1531] else [1915]

theorem lFS_keys (s : Site) (v : Vals) : (lFS s v).map Prod.fst = lK s := by
  cases s <;> simp [lFS, lK] <;> split <;> simp

theorem lK_cases {s : Site} (h : keepL s = true) : lK s = [1915, 1531] ∨ lK s = [1915] := by
  cases s <;> simp [keepL, lK] at h ⊢

/-- The region the code after a site of the loop runs in: no write of the sum or the row sum. -/
def lIvs : List (Nat × Nat) := [(951, 1284), (2239, 17), (2259, 71), (2560, 6)]

theorem region_L1 : regionH kernel Lib.hooks lIvs [1915] = true := by decide +kernel
theorem region_L2 : regionH kernel Lib.hooks lIvs [1915, 1531] = true := by decide +kernel

/-- The checks of a site: its position and the next lie in the region, no segment starts there,
and its event writes none of the registers. -/
def siteL (s : Site) : Bool :=
  inIvs lIvs s.pc && inIvs lIvs (s.pc + 1) && !Assumptions.emuSites.contains s.pc &&
  (match kernel.code[s.pc]? with
    | some ins => (lK s).all fun r => !(eventWrites ins.op).contains r
    | none => true)

/-- The facts of the successors are among the site's. -/
def subL (s : Site) : Bool :=
  (succs s).all fun z => (!psB z || psB s) && (match z with | .pre _ => false | _ => true)

theorem keepL_ok (s : Site) (h : keepL s = true) : siteL s = true ∧ subL s = true := by
  cases s with
  | pre j => simp [keepL] at h
  | nxt j => revert j; decide +kernel
  | _ => revert h; decide +kernel

theorem record_keepL {d : D} (ev : Event) (z : Site) (h : keepL d.c.site = true) :
    (record L d ev z).l = d.v.l ∧ (record L d ev z).ps = d.v.ps := by
  unfold record
  revert h
  cases hs : d.c.site <;> simp [keepL] <;> split <;> simp_all

theorem lFS_loop {s : Site} (h : lK s ≠ []) (v : Vals) :
    lFS s v = (1915, v.l) :: if psB s then [(1531, v.ps)] else [] := by
  cases s <;> simp_all [lFS, lK]

theorem lFS_sub {s z : Site} (hk : keepL s = true) (hz : z ∈ succs s) (v w : Vals)
    (h1 : w.l = v.l) (h2 : w.ps = v.ps) : ∀ x ∈ lFS z w, x ∈ lFS s v := by
  obtain ⟨-, hb⟩ := keepL_ok s hk
  simp only [subL, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨h3, -⟩ := hb z hz
  have hs : lK s ≠ [] := by
    cases s <;> simp [keepL, lK] at hk ⊢ <;> split <;> simp
  intro x hx
  by_cases hz0 : lK z = []
  · have : lFS z w = [] := by
      cases z <;> simp [lFS, lK] at hz0 ⊢ <;> split at hz0 <;> simp at hz0
    simp [this] at hx
  · rw [lFS_loop hz0] at hx
    rw [lFS_loop hs]
    simp only [List.mem_cons, List.mem_ite_nil_right, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with hx | ⟨hp, hx⟩
    · exact .inl (by rw [hx, h1])
    · exact .inr ⟨h3.resolve_left (by simp [hp]), by rw [hx, h2]⟩

/-- **The running sum's facts are kept** by a site of the loop. -/
theorem l_keep {d : D} (hk : keepL d.c.site = true) : DataStep (codeS e L g) lF d := by
  obtain ⟨hw, hb⟩ := keepL_ok d.c.site hk
  simp only [siteL, Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
  have key : DataStep (codeS e L g) lF d :=
    DataStep.constAny (C := codeS e L g) (sF := lF) (d := d)
      (A := Assumptions.all) (tab := Lib.hooks) (ivs := lIvs)
      Lib.rulesFrame hooks_any (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩
      (fun R h => atS_lF h) (fun ins hc => ?_)
      (by
        rw [lF, lFS_keys]
        rcases lK_cases hk with h | h <;> rw [h]
        exacts [region_L2, region_L1]) ?_
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    simpa only [lF, lFS_keys] using h4
  · intro ev d' hn x hx
    obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
    obtain ⟨hl, hp⟩ := record_keepL (L := L) (d := d) ev c'.site hk
    exact lFS_sub hk (next_mem (e := e) (L := L) (g := g) (ev := ev) hnc) d.v _ hl hp x hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
