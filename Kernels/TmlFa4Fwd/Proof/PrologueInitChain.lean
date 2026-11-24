-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueInitGroup
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Local address setup after an election group, in group order. -/
def initJoin : Fin 16 → Option (Fin 8) := fun i =>
  (#v[some 0, none, some 1, none, some 2, none, some 3, none,
    some 4, none, some 5, none, some 6, none, some 7, none] : Vector _ 16)[i]

/-- Addresses that have been produced by the local joins before group `j`. -/
def initAddresses (j : Nat) : List (Nat × Nat) :=
  (2535, 0) :: ((List.finRange 16).take j).flatMap (fun i =>
    ((initJoin i).map (fun k => (warp0Join k).addresses)).getD [])

def initFacts (l : Launch) (j : Nat) : List (Nat × Value) :=
  (1062, b32 0) :: (initAddresses j).map (fun (r, off) => (r, b32 (l.sharedBase + off)))

private theorem initBases (j : Fin 16) :
    (initGroup j).all (fun i => (initAddresses j.val).contains
      ((initSite i).baseReg, (initSite i).baseOffset)) = true := by
  fin_cases j <;> decide

theorem initGroupBases {l : Launch} {t : TState} {j : Fin 16}
    (h : Holds t.regs (initFacts l j.val)) :
    ∀ i ∈ initGroup j,
      t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)) := by
  intro i hi
  have hmem := List.contains_iff_mem.mp (List.all_eq_true.mp (initBases j) i hi)
  exact holds_mem h (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hmem, rfl⟩))

private theorem electionPreservesAddresses (j : Fin 16) :
    ([1062] ++ (initAddresses j.val).map Prod.fst).all (fun r =>
      !([(electSite j).laneReg, (electSite j).chosenReg, (electSite j).skipReg,
        (electSite j).countReg].contains r)) = true := by
  fin_cases j <;> decide

private theorem initJoinEntry (j : Fin 16) :
    ((initJoin j).map (fun k => (warp0Join k).entry)).getD (electSite j).skipPc =
      (electSite j).skipPc := by
  fin_cases j <;> decide

private theorem initJoinExit (j : Fin 16) :
    ((initJoin j).map (fun k => (warp0Join k).exit)).getD (electSite j).skipPc =
      if h : j.val + 1 < 16 then (electSite ⟨j.val + 1, h⟩).pc else 172 := by
  fin_cases j <;> decide

private theorem initJoinFrame (j : Fin 16) :
    ([1062] ++ (initAddresses j.val).map Prod.fst).all (fun r =>
      !((((initJoin j).map (fun k => (warp0Join k).writes)).getD []).contains r)) = true := by
  fin_cases j <;> decide

private theorem initAddresses_succ (j : Fin 16) :
    initAddresses (j.val + 1) =
      initAddresses j.val ++ ((initJoin j).map (fun k => (warp0Join k).addresses)).getD [] := by
  fin_cases j <;> decide

private theorem holdsInitFacts {R : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ (r : Nat) (v : Value), (r, v) ∈ F → R r = some v) : Holds R F := by
  induction F with
  | nil => trivial
  | cons a as ih => exact ⟨h a.1 a.2 (by simp), ih (fun r v hm => h r v (by simp [hm]))⟩

private theorem frameInitFacts {l : Launch} {t u : TState} {j : Nat} {writes : List Nat}
    (h : Holds t.regs (initFacts l j))
    (hFrame : ∀ r ∉ writes, u.regs r = t.regs r)
    (hWrites : ([1062] ++ (initAddresses j).map Prod.fst).all
      (fun r => !writes.contains r) = true) : Holds u.regs (initFacts l j) := by
  apply holdsInitFacts
  intro r v hm
  have hReg : r ∈ [1062] ++ (initAddresses j).map Prod.fst := by
    rcases (List.mem_cons.mp hm) with hEq | hTail
    · cases hEq
      simp
    obtain ⟨⟨s, off⟩, hs, he⟩ := List.mem_map.mp hTail
    cases he
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hs, rfl⟩)
  have hNot : r ∉ writes := by
    have hb := List.all_eq_true.mp hWrites r hReg
    intro hw
    rw [List.contains_iff_mem.mpr hw] at hb
    cases hb
  rw [hFrame r hNot]
  exact holds_mem h hm

/-- An election and its selected initialization records preserve all shared base registers. -/
theorem electionInitFacts {l : Launch} {t u : TState} {j : Fin 16}
    (h : Holds t.regs (initFacts l j.val))
    (hFrame : ∀ r ∉ [(electSite j).laneReg, (electSite j).chosenReg, (electSite j).skipReg,
      (electSite j).countReg], u.regs r = t.regs r) : Holds u.regs (initFacts l j.val) :=
  frameInitFacts h hFrame (electionPreservesAddresses j)

/-- After the election group, the actual local path enters the next group or the final fence. -/
theorem initNext {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} (j : Fin 16)
    {t : TState} (h : At t (electSite j).skipPc (initFacts l j.val)) :
    ∃ u, Relation.ReflTransGen (Tau kernel A l g) t u ∧
      At u (if h : j.val + 1 < 16 then (electSite ⟨j.val + 1, h⟩).pc else 172)
        (initFacts l (j.val + 1)) := by
  have hEntry := initJoinEntry j
  have hExit := initJoinExit j
  have hFrame := initJoinFrame j
  have hAddrs := initAddresses_succ j
  cases hj : initJoin j with
  | none =>
    simp only [hj, Option.map_none, Option.getD_none] at hExit hAddrs
    exact ⟨t, .refl, hExit ▸ (show At t (electSite j).skipPc (initFacts l (j.val + 1)) from by
      simpa only [initFacts, hAddrs, List.append_nil] using h)⟩
  | some k =>
    simp only [hj, Option.map_some, Option.getD_some] at hEntry hExit hFrame hAddrs
    obtain ⟨hpc, hs, ha, hf, hFacts⟩ := h
    have hw := holds_mem hFacts (List.mem_cons_self)
    have hb : t.regs 2535 = some (b32 l.sharedBase) := by
      apply holds_mem hFacts
      simp [initFacts, initAddresses]
    obtain ⟨u, hu, ⟨hpc', hs', ha', hf', hNew⟩, hRegs⟩ :=
      warp0JoinRunWith (A := A) hp k g t (hEntry.symm ▸ hpc) hf hs ha hw hb
    have hOld := frameInitFacts hFacts hRegs hFrame
    refine ⟨u, run_rtg hu, hpc'.trans hExit, hs', ha', hf', ?_⟩
    apply holdsInitFacts
    intro r v hr
    simp only [initFacts, hAddrs, List.map_append, ← List.cons_append, List.mem_append] at hr
    exact hr.elim (holds_mem hOld) (holds_mem hNew)

end
end PTX.Kernels.TmlFa4Fwd.Prologue
