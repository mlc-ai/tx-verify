-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLinearRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

structure RoleRegion where
  lo : Nat
  hi : Nat
  exits : List Nat

def roleRegion : Fin 12 → RoleRegion
  | 0 => ⟨1907, 1985, [1985, 2042]⟩
  | 1 => ⟨1988, 2042, [2042]⟩
  | 2 => ⟨2042, 2286, [2286, 2534, 2763]⟩
  | 3 => ⟨2291, 2534, [2534]⟩
  | 4 => ⟨2534, 2647, [2647]⟩
  | 5 => ⟨2648, 2693, [2693, 2750]⟩
  | 6 => ⟨2696, 2750, [2750]⟩
  | 7 => ⟨2750, 2768, [2768, 3099]⟩
  | 8 => ⟨1985, 1988, [1988]⟩
  | 9 => ⟨2286, 2291, [2291]⟩
  | 10 => ⟨2693, 2696, [2696]⟩
  | 11 => ⟨2647, 2648, [2648]⟩

/-- The allocation's store is the only nonzero sub-step of the MMA warp. -/
def RoleShape (s : TState) : Prop :=
  s.sub ≤ 1 ∧ s.acc = [] ∧ (s.pc ≠ 1909 → s.sub = 0)

private def roleRegionCode (site : RoleRegion) (pc : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || linearEventOp ins.op) &&
    (if allocationOp ins.op then pc == 1909 else true) &&
    (match ins.op with
      | .bra dest _ => site.lo ≤ dest && (dest < site.hi || site.exits.contains dest)
      | .brx .. => false
      | _ => true)

private theorem roleRegionCodeOk (region : Fin 12) {pc : Nat} {ins : Instr}
    (hLo : (roleRegion region).lo ≤ pc) (hHi : pc < (roleRegion region).hi)
    (hc : kernel.code[pc]? = some ins) : roleRegionCode (roleRegion region) pc ins = true := by
  let site := roleRegion region
  let code := ((kernel.code.drop site.lo).take (site.hi - site.lo)).zipIdx site.lo
  have hAll : code.all (fun pair => roleRegionCode site pair.2 pair.1) = true := by
    fin_cases region <;> set_option maxRecDepth 100000 in kernel_rfl
  have hMem : (ins, pc) ∈ code := by
    have hp : site.lo ≤ pc := hLo
    have ht : pc < site.hi := hHi
    apply List.mem_of_getElem? (i := pc - site.lo)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hp, hc]
    rfl
  exact List.all_eq_true.mp hAll (ins, pc) hMem

private theorem regionNext (region : Fin 12) {pc : Nat} (hp : (roleRegion region).lo ≤ pc)
    (hq : pc < (roleRegion region).hi) : (roleRegion region).lo ≤ pc + 1 ∧
      (pc + 1 < (roleRegion region).hi ∨ pc + 1 ∈ (roleRegion region).exits) := by
  refine ⟨by omega, ?_⟩
  by_cases hi : pc + 1 < (roleRegion region).hi
  · exact .inl hi
  · have he : pc + 1 = (roleRegion region).hi := by omega
    right
    rw [he]
    fin_cases region <;> decide

private theorem roleAllocAt {l : Launch} {g : Nat} {s u : TState} (hPc : s.pc = 1909)
    (ht : Tau kernel [] l g s u) : False := by
  have hCode := Flow.code_1909
  rw [← hPc] at hCode
  exact tau_core_not_event hCode rfl ht

/-- All returning transitions stay in the region or take one of its decoded exits. -/
theorem roleRegionStep (region : Fin 12) {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : (roleRegion region).lo ≤ s.pc) (hHi : s.pc < (roleRegion region).hi)
    (hShape : RoleShape s) (h : WStep kernel Assumptions.all l g s ev u) :
    ((roleRegion region).lo ≤ u.pc ∧ u.pc < (roleRegion region).hi ∨
      u.pc ∈ (roleRegion region).exits ∧ u.fault = none) ∧ RoleShape u := by
  have hlo : 1904 ≤ s.pc := by fin_cases region <;> simp [roleRegion] at hLo <;> omega
  have hhi : s.pc < 2768 := by fin_cases region <;> simp [roleRegion] at hHi <;> omega
  let site := roleRegion region
  have hNext := regionNext region hLo hHi
  have hN (hPc : u.pc = s.pc + 1) (hf : u.fault = none) :
      (site.lo ≤ u.pc ∧ u.pc < site.hi ∨ u.pc ∈ site.exits ∧ u.fault = none) := by
    rw [hPc]
    exact hNext.2.elim (fun h => .inl ⟨hNext.1, h⟩) (fun hx => .inr ⟨hx, hf⟩)
  rcases h with ⟨-, ht⟩ | ⟨e, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core hlo hhi]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hFault : s.fault = none := by
      cases h : s.fault
      · rfl
      · simp [Tau, out, h] at ht'
    have hCode := roleRegionCodeOk region hLo hHi hc
    simp only [roleRegionCode, Bool.and_eq_true] at hCode
    rcases tau_core_frame hc ht' with rfl | hR
    · exact ⟨hN rfl hFault, Nat.zero_le 1, rfl, fun _ => rfl⟩
    · have hSource : s.pc ≠ 1909 := fun h => roleAllocAt h ht'
      refine ⟨?_, hR.sub ▸ hShape.1, hR.acc.trans hShape.2.1,
        fun _ => hR.sub.trans (hShape.2.2 hSource)⟩
      have hPc := hR.pc
      cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dest aligned =>
        have hDst : site.lo ≤ dest ∧ (dest < site.hi ∨ dest ∈ site.exits) := by
          simpa [ho] using hCode.2
        rw [hPc]
        exact hDst.2.elim (fun h => .inl ⟨hDst.1, h⟩)
          (fun hx => .inr ⟨hx, hR.fault.trans hFault⟩)
      case brx => simp [ho] at hCode
      all_goals exact hN hPc (hR.fault.trans hFault)
  · obtain ⟨ins, hc, hloc, _⟩ := estep_event_source he
    have hFault : s.fault = none := by
      cases h : s.fault
      · rfl
      · obtain ⟨m, hm, hf⟩ := he
        simp only [out, h, Out.ev.injEq] at hm
        subst m
        cases hf.2
    have hCode := roleRegionCodeOk region hLo hHi hc
    simp only [roleRegionCode, Bool.and_eq_true, hloc, Bool.false_or] at hCode
    obtain ⟨hSub, hAcc, hAdv | hAlloc | hFault⟩ :=
      linearEventProgressWithSub hc hCode.1.1 hShape.1 hShape.2.1 he
    · have hZero : u.sub = 0 := by
        rcases hAdv.2.2 with hZ | ⟨hEq, hNo⟩
        · exact hZ
        · refine hEq.trans (hShape.2.2 ?_)
          intro hp
          rw [hp, Flow.code_1909] at hc
          obtain rfl := Option.some.inj hc
          cases hNo
      exact ⟨hN hAdv.1 (hAdv.2.1.trans hFault), hSub, hAcc, fun _ => hZero⟩
    · have hPC : s.pc = 1909 := by simpa [hAlloc.2.2.2] using hCode.1.2
      exact ⟨.inl ⟨hAlloc.1 ▸ hLo, hAlloc.1 ▸ hHi⟩, hSub, hAcc,
        fun h => (h (hAlloc.1.trans hPC)).elim⟩
    · exact ⟨.inl ⟨hFault.1 ▸ hLo, hFault.1 ▸ hHi⟩, hSub, hAcc,
        fun h => hFault.2.1.trans (hShape.2.2 (fun hs => h (hFault.1.trans hs)))⟩

/-- Split the actual walk at its first decoded exit from one region, transporting any
invariant preserved by its returning transitions. -/
theorem cutWalkInterval {lo hi cutoff : Nat} {exits : List Nat} {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {P : TState → Prop}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hl : lo ≤ s.pc) (hh : s.pc < hi)
    (hp : P s) (hHi : hi ≤ cutoff)
    (hStep : ∀ {t u : TState} {e : Option Event}, lo ≤ t.pc → t.pc < hi →
      WStep kernel Assumptions.all l g t e u → P t →
      (lo ≤ u.pc ∧ u.pc < hi ∨ u.pc ∈ exits ∧ u.fault = none) ∧ P u) :
    countedUntil cutoff visits ≤ countedUntil hi visits ∨
      ∃ u rest tail, u.pc ∈ exits ∧ u.fault = none ∧
        P u ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff visits ≤ countedUntil hi visits +
          countedUntil cutoff tail := by
  induction hw with
  | stop => exact .inl (by simp [countedUntil])
  | @tau s u es vs ht hw ih =>
    have he : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, ht⟩
    obtain ⟨⟨hL, hH⟩ | hExit, hu⟩ := hStep hl hh he hp
    · rcases ih hL hH hu with h | ⟨v, rest, tail, hV, hF, hP, hW, hb⟩
      · exact .inl (by
          simpa [countedUntil, hh, Nat.lt_of_lt_of_le hh hHi, visit_pc, visit_ev,
            List.filterMap_cons] using h)
      · exact .inr ⟨v, rest, tail, hV, hF, hP, hW, by
          simpa [countedUntil, hh, Nat.lt_of_lt_of_le hh hHi, visit_pc, visit_ev,
            List.filterMap_cons] using hb⟩
    · refine .inr ⟨u, es, vs, hExit.1, hExit.2, hu, hw, ?_⟩
      simp only [countedUntil, List.takeWhile_cons, visit_pc, Nat.lt_of_lt_of_le hh hHi,
        decide_true, ↓reduceIte, List.filterMap_cons, visit_ev]
      exact Nat.le_add_left _ _
  | @ev s u e es vs he hw ih =>
    have hE : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨e, rfl, he⟩
    have p₁ : decide ((visit kernel l g s (some e)).pc < cutoff) = true :=
      decide_eq_true (Nat.lt_of_lt_of_le hh hHi)
    have p₂ : decide ((visit kernel l g s (some e)).pc < hi) = true :=
      decide_eq_true hh
    obtain ⟨⟨hL, hH⟩ | hExit, hu⟩ := hStep hl hh hE hp
    · rcases ih hL hH hu with h | ⟨v, rest, tail, hV, hF, hP, hW, hb⟩
      · left
        rw [countedUntil, List.takeWhile_cons, ite_eq_left p₁, countedUntil,
          List.takeWhile_cons, ite_eq_left p₂]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons]
        exact Nat.add_le_add_right h _
      · refine .inr ⟨v, rest, tail, hV, hF, hP, hW, ?_⟩
        rw [countedUntil, List.takeWhile_cons, ite_eq_left p₁, countedUntil,
          List.takeWhile_cons, ite_eq_left p₂]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons]
        change countedUntil cutoff vs + (if e.counts then 1 else 0) ≤
          countedUntil hi vs +
            (if e.counts then 1 else 0) + countedUntil cutoff tail
        omega
    · refine .inr ⟨u, es, vs, hExit.1, hExit.2, hu, hw, ?_⟩
      rw [countedUntil, List.takeWhile_cons, ite_eq_left p₁]
      simp only [List.filterMap_cons, visit_ev, List.countP_cons]
      have hTerm : countedUntil hi (visit kernel l g s (some e) :: vs) =
          countedUntil hi vs + (if e.counts then 1 else 0) := by
        rw [countedUntil, List.takeWhile_cons, ite_eq_left p₂]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons, countedUntil]
      rw [hTerm]
      change countedUntil cutoff vs + (if e.counts then 1 else 0) ≤
        countedUntil hi vs + (if e.counts then 1 else 0) + countedUntil cutoff vs
      omega
  | @last s e he =>
    exact .inl (by simp [countedUntil, hh, Nat.lt_of_lt_of_le hh hHi, visit_pc])


/-- Split the actual walk at its first decoded exit from one region, transporting any
invariant preserved by its returning transitions. -/
theorem cutMmaRegion (region : Fin 12) {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {P : TState → Prop}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hl : (roleRegion region).lo ≤ s.pc) (hh : s.pc < (roleRegion region).hi)
    (hs : RoleShape s) (hp : P s)
    (hKeep : ∀ {t u : TState} {e : Option Event},
      (roleRegion region).lo ≤ t.pc → t.pc < (roleRegion region).hi →
      WStep kernel Assumptions.all l g t e u → P t → P u) :
    countedUntil 2768 visits ≤ countedUntil (roleRegion region).hi visits ∨
      ∃ u rest tail, u.pc ∈ (roleRegion region).exits ∧ u.fault = none ∧
        RoleShape u ∧ P u ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil 2768 visits ≤ countedUntil (roleRegion region).hi visits +
          countedUntil 2768 tail := by
  have hc : (roleRegion region).hi ≤ 2768 := by fin_cases region <;> decide
  have hStep {t u : TState} {e : Option Event} (hl : (roleRegion region).lo ≤ t.pc)
      (hh : t.pc < (roleRegion region).hi) (he : WStep kernel Assumptions.all l g t e u)
      (ht : RoleShape t ∧ P t) :
      ((roleRegion region).lo ≤ u.pc ∧ u.pc < (roleRegion region).hi ∨
        u.pc ∈ (roleRegion region).exits ∧ u.fault = none) ∧ (RoleShape u ∧ P u) := by
    obtain ⟨hu, hS⟩ := roleRegionStep region hl hh ht.1 he
    exact ⟨hu, hS, hKeep hl hh he ht.2⟩
  rcases cutWalkInterval hw hl hh ⟨hs, hp⟩ hc hStep with h | ⟨u, es, vs, hP, hF, hS, hW, hC⟩
  · exact .inl h
  · exact .inr ⟨u, es, vs, hP, hF, hS.1, hS.2, hW, hC⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
