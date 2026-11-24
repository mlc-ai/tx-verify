-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RunFrame
public import Lemmas.Register.EventRegFrame
public import Lemmas.Flow.Code

@[expose] public section

/-! # Facts a machine's step does not touch

A proof tool, generic over the kernel (promoted from tml-fa4's `Proof2/Lib/RegionFrame.lean`). A
site machine whose facts are those of a smaller machine plus facts on registers `R` that neither the
event nor the local code after it writes has the smaller machine's steps (`StepAt.lift`): the event
writes no register of `R` (`eventWrites`), and every local step from the event's continuation stays
in a range of positions whose instructions write no register of `R` (`regionB`, a Boolean check on
the code, `region_frame`). The facts of the successor are then given by the facts of the smaller
machine at the successor and the facts of `R` before the event (`hland`). This is how the steps of
control sites, proved on the control facts only, carry the data facts of a state. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Every local step from a position in `[lo, hi]` stays in `[lo, hi]` and writes no register of
`R`: a local instruction writes none of `R`, continues inside (a jump's target inside, the next
position at most `hi`), a guarded event may be skipped to the next position (at most `hi`), and an
unguarded event performs no local step. -/
def regionB (K : Kernel) (lo hi : Nat) (R : List Nat) : Bool :=
  (List.range (hi + 1 - lo)).all fun i =>
    match K.code[lo + i]? with
    | none => true
    | some ins =>
      if ins.op.isLocal then
        R.all (fun r => !(writesRegs ins.op).contains r) && Nat.blt (lo + i) hi &&
          (match ins.op with
            | .bra tgt _ => Nat.ble lo tgt && Nat.ble tgt hi
            | .brx .. => false
            | _ => true)
      else ins.guard.isNone || Nat.blt (lo + i) hi

theorem regionB_at {lo hi : Nat} {R : List Nat} (h : regionB K lo hi R = true) {pc : Nat}
    (h1 : lo ≤ pc) (h2 : pc ≤ hi) {ins : Instr} (hc : K.code[pc]? = some ins) :
    (if ins.op.isLocal then
        R.all (fun r => !(writesRegs ins.op).contains r) && Nat.blt pc hi &&
          (match ins.op with
            | .bra tgt _ => Nat.ble lo tgt && Nat.ble tgt hi
            | .brx .. => false
            | _ => true)
      else ins.guard.isNone || Nat.blt pc hi) = true := by
  have := List.all_eq_true.mp h (pc - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (pc - lo) = pc by omega, hc] at this
  exact this

/-- **One local step inside a region** stays inside and keeps the registers of `R`. -/
theorem tau_region (hA : RulesFrame A) {lo hi : Nat} {R : List Nat} (hB : regionB K lo hi R = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) {u u1 : TState}
    (ht : Tau K A L g u u1) (h1 : lo ≤ u.pc) (h2 : u.pc ≤ hi) :
    lo ≤ u1.pc ∧ u1.pc ≤ hi ∧ ∀ r ∈ R, u1.regs r = u.regs r := by
  unfold Tau out at ht
  cases hf : u.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : K.code[u.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      have hb := regionB_at hB h1 h2 hc
      simp only [hc] at ht
      cases hg : guardHolds u ins.guard with
      | error e => simp [hg] at ht
      | ok b =>
        simp only [hg] at ht
        cases b with
        | false =>
          simp only [Out.tau.injEq] at ht
          subst ht
          have hgd : ins.guard.isSome := by
            cases hgi : ins.guard with
            | none => rw [hgi] at hg; simp [guardHolds, pure, Except.pure] at hg
            | some _ => rfl
          refine ⟨by simp [skip]; omega, ?_, fun _ _ => rfl⟩
          simp only [skip]
          split at hb
          · simp only [Bool.and_eq_true, Nat.blt_eq] at hb
            omega
          · simp only [Bool.or_eq_true, Nat.blt_eq, Option.isNone_iff_eq_none] at hb
            rcases hb with hb | hb
            · rw [hb] at hgd; cases hgd
            · omega
        | true =>
          by_cases hl : ins.op.isLocal = true
          · simp only [hl, ↓reduceIte] at ht
            cases he : execLocalA A L g u ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              have fr := execLocalA_frame hA he (hS u.pc h1 h2)
              simp only [hl, ↓reduceIte, Bool.and_eq_true, Nat.blt_eq] at hb
              obtain ⟨⟨hw, hlt⟩, hj⟩ := hb
              have key : ∀ (op : Op), (match op with
                  | .bra tgt _ => Nat.ble lo tgt && Nat.ble tgt hi
                  | .brx .. => false
                  | _ => true) = true →
                  (t'.pc = nextPc op u.pc ∨ BrxTarget op t'.pc) → lo ≤ t'.pc ∧ t'.pc ≤ hi := by
                intro op hj hp
                cases op <;> simp only [nextPc, BrxTarget, Bool.and_eq_true, Nat.ble_eq,
                  or_false, reduceCtorEq] at hj hp ⊢ <;> omega
              obtain ⟨k1, k2⟩ := key ins.op hj fr.pc
              exact ⟨k1, k2, fun r hr => fr.regs r (by
                have := List.all_eq_true.mp hw r hr; simpa using this)⟩
          · simp [hl] at ht

/-- **Local steps inside a region** keep the registers of `R`. -/
theorem region_frame (hA : RulesFrame A) {lo hi : Nat} {R : List Nat}
    (hB : regionB K lo hi R = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) {u t' : TState}
    (h : Relation.ReflTransGen (Tau K A L g) u t') (h1 : lo ≤ u.pc) (h2 : u.pc ≤ hi) :
    ∀ r ∈ R, t'.regs r = u.regs r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intros; rfl
  | head ht _ ih =>
    obtain ⟨a1, a2, a3⟩ := tau_region hA hB hS ht h1 h2
    intro r hr
    rw [ih a1 a2 r hr, a3 r hr]

/-- **A piece with facts on registers its region does not write** (`SegD.frame` for code with
branches): the facts `H` hold at both ends when local steps from the piece's start stay in a
region whose instructions write no register of `H`. -/
theorem SegD.frameR (hA : RulesFrame A) {n s b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F b G C) {lo hi : Nat} (hB : regionB K lo hi (H.map Prod.fst) = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) (hlo : lo ≤ s) (hhi : s ≤ hi) :
    SegD K A L g n s (F ++ H) b (G ++ H) C := by
  intro t ht
  have hF : At t s F := At.mono ht ((holds_append _ _ _).mp ht.2.2.2.2).1
  refine ⟨fun hc => ?_, (h t hF).2⟩
  obtain ⟨t', hr, ht'⟩ := (h t hF).1 hc
  refine ⟨t', hr, ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1,
    (holds_append _ _ _).mpr ⟨ht'.2.2.2.2, ?_⟩⟩
  have hH := ((holds_append _ _ _).mp ht.2.2.2.2).2
  have hfr := region_frame hA hB hS (run_rtg hr) (by rw [ht.1]; exact hlo) (by rw [ht.1]; exact hhi)
  refine holds_of_mem fun r v hrv => ?_
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) hrv)]
  exact holds_mem hH hrv

/-! ### Where an event leaves the thread -/

theorem localSreg_frame_at {t : TState} {r : RuleId} {op : Op}
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c)
    (hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    ReturnedFrame t.pc (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl] <;> first
    | exact True.intro
    | (unfold sregTmpl
       intro vs
       dsimp only
       cases h : execLocalA A L g t (op.withSregValues vs) with
       | error f => exact Or.inl rfl
       | ok u =>
         rcases (hloc _ _ h).pc with hpc | hpc
         · rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
             exact Or.inr (by simpa [Op.withSregValues, nextPc] using hpc)
         · rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
             exact absurd hpc (by simp [Op.withSregValues, BrxTarget]))

/-- Every returning callback of an event leaves the thread at its position or the next one, when
the local rules at the thread's state keep their frame (`eventTmpl_return_frame` at one state). -/
theorem eventTmpl_return_frame_at {t : TState} {op : Op}
    (hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    ReturnedFrame t.pc (eventTmpl A L g t op) := by
  cases op <;> simp only [eventTmpl]
  case mem => exact mem_frame
  case warp => exact warp_frame
  case matrix => exact matrix_frame
  case barSync | barSyncN | barArrive => exact bar_frame
  case cluster => exact Or.inr rfl
  case setMaxReg => exact setMaxNReg_frame
  case cpTensor => exact tensor_frame
  case prefetchTensor | prefetchBulk => exact tensorPrefetch_frame
  case cpAsync | cpAsyncCommit | cpAsyncWait | cpAsyncArrive => exact cpAsync_frame
  case asyncStore => exact asyncStore_frame
  case cpTensorStore | bulkCommit | bulkWait => exact tensorStore_frame
  case clcTryCancel | clcQuery => exact clc_frame
  case fence => exact fence_frame
  case mbarInit | mbarInval | fenceMbarInit | mbarArrive | mbarWait | cpBulk =>
    exact widen_frame tma_frame
  case tcCommit => exact tcCommit_frame
  case tcLd => exact tcLd_frame
  case tcSt => exact tcSt_frame
  case tcAlloc | tcDealloc | tcRelinquish | tcMma | tcFenceBefore | tcFenceAfter |
      tcWaitLd | tcWaitSt | tcCp | tcShift => exact tc_frame
  case int i =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame_at (.inl ⟨i, rfl⟩) hloc
  case move m =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame_at (.inr (.inl ⟨m, rfl⟩)) hloc
  case cvt c =>
    simp only [Op.rule]
    split <;> first | exact True.intro | exact localSreg_frame_at (.inr (.inr ⟨c, rfl⟩)) hloc
  all_goals exact True.intro

/-- The registers of an event's instruction it may write, and the local rules' frame at an event
of a changing special register. -/
theorem eventTmpl_kept_at {t : TState} {op : Op}
    (hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u) :
    CallbackFrame (RegsKept (eventWrites op) t) (eventTmpl A L g t op) :=
  eventTmpl_regsKept fun hop vs u h => by
    have fr := hloc _ _ h
    intro r hr
    refine fr.regs r fun hm => hr ?_
    rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
      simpa [eventWrites, writesRegs, Op.withSregValues] using hm

/-! ### The lift -/

namespace Code

/-- **A step of a machine with more facts**, from the step of the machine with fewer: the event and
the local code after it (inside `[lo, hi]`) write no register of `R`, and the successor's extra
facts follow from its smaller facts and the facts of `R` before the event (`hland`). -/
theorem StepAt.lift (hA : RulesFrame A) {C : Code K A L g} {F' : C.D → List (Nat × Value)}
    {d : C.D} (h : C.StepAt d)
    (hsub : ∀ R, Holds R (F' d) → Holds R (C.facts d))
    (hmem : ∀ q, q ∈ C.facts d → q ∈ F' d)
    {lo hi : Nat} {R : List Nat} (hB : regionB K lo hi R = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc)
    (hlo : lo ≤ C.pc d) (hhi : C.pc d + 1 ≤ hi)
    (hev : ∀ ins, K.code[C.pc d]? = some ins → R.all (fun r => !(eventWrites ins.op).contains r))
    (hland : ∀ e d', C.next d e = some (some d') → ∀ (S T : Nat → Option Value),
      Holds S (F' d) → Holds T (C.facts d') → (∀ r ∈ R, T r = S r) → Holds T (F' d')) :
    ({ C with facts := F' } : Code K A L g).StepAt d := by
  refine ⟨fun hi => ?_, ?_⟩
  · obtain ⟨ins, hc, hl, hg⟩ := h.site hi
    refine ⟨ins, hc, hl, ?_⟩
    revert hg
    cases ins.guard with
    | none => exact id
    | some pn => exact hmem _
  · intro t e u ins hat hi hc hfire
    have hat' : C.AtD d t := ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hsub _ hat.2.2.2.2⟩
    have hres := h.step ins hat' hi hc hfire
    rcases hres with (hn | hex) | hn
    · exact .inl (.inl hn)
    · obtain ⟨d', t', hn, hr, hgood⟩ := hex
      refine .inl (.inr ⟨d', t', hn, hr, ⟨hgood.1.1, hgood.1.2.1, hgood.1.2.2.1,
        hgood.1.2.2.2.1, ?_⟩, hgood.2⟩)
      have hpc : t.pc = C.pc d := hat.1
      have hS0 : Assumption.SegFreePc A t.pc := hS _ (by omega) (by omega)
      have hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u :=
        fun op u h => execLocalA_frame hA h hS0
      rw [← hpc] at hfire
      have hup := callbackFrame_fires (eventTmpl_return_frame_at (op := ins.op) hloc) hfire
      have hkept := callbackFrame_fires (eventTmpl_kept_at (op := ins.op) hloc) hfire
      have hfr := region_frame hA hB hS hr (by omega) (by omega)
      refine hland e d' hn t.regs t'.regs hat.2.2.2.2 hgood.1.2.2.2.2 fun r hr' => ?_
      rw [hfr r hr', hkept r]
      have := List.all_eq_true.mp (hev ins hc) r hr'
      simpa using this
    · exact .inr hn

end Code

end
end PTX.Flow
