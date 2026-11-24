-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeCode
public import Kernels.TmlFa4Fwd.Proof.CorrectionReciprocal
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part137

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def finalizePollPc (stage : Fin 2) (free : Bool) : Nat :=
  8473 + 296 * stage.val + if free then 3 else 0

def finalizePollPred (stage : Fin 2) (free : Bool) : Nat :=
  9888 + 2 * stage.val + free.toNat

def finalizePollBase (stage : Fin 2) (free : Bool) : Nat :=
  if free then if stage.val = 0 then 6497 else 7131 else 6495 + 4 * stage.val

def finalizePollPhase (free : Bool) : Nat := if free then 6498 else 6496

def finalizePollLoc (l : Launch) (g : Nat) (stage : Fin 2) (free : Bool) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + (if free then 224 else 144) + 8 * stage.val⟩

private theorem finalizePollCode (stage : Fin 2) (free : Bool) :
    kernel.code[finalizePollPc stage free]? =
      some ⟨none, .mbarWait (finalizePollPred stage free) (finalizePollBase stage free) 0
        (.reg (finalizePollPhase free)) true .cta⟩ ∧
    kernel.code[finalizePollPc stage free + 1]? =
      some ⟨some (finalizePollPred stage free, false), .bra (finalizePollPc stage free + 3) true⟩ ∧
    kernel.code[finalizePollPc stage free + 2]? =
      some ⟨none, .bra (finalizePollPc stage free) true⟩ := by
  fin_cases stage <;> cases free
  · exact ⟨Flow.code_8473, Flow.code_8474, Flow.code_8475⟩
  · exact ⟨Flow.code_8476, Flow.code_8477, Flow.code_8478⟩
  · exact ⟨Flow.code_8769, Flow.code_8770, Flow.code_8771⟩
  · exact ⟨Flow.code_8772, Flow.code_8773, Flow.code_8774⟩

private theorem afterPollCore {l : Launch} {g pc : Nat} {t : TState} {ins : Instr}
    (hPc : t.pc = pc) (hLo : 8473 ≤ pc)
    (hCode : kernel.code[pc]? = some ins) (hCore : Assumptions.coreOp ins.op = true) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  apply Assumptions.out_all_eq_nil _ _ _ (hPc.symm ▸ hCode) hCore
  all_goals
    rw [hPc]
    simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
      Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem afterCorrectionPoll {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    {pc dst : Nat} (hLo : 8473 ≤ pc) (ok : Bool)
    (hBranch : kernel.code[pc + 1]? = some ⟨some (dst, false), .bra (pc + 3) true⟩)
    (hRetry : kernel.code[pc + 2]? = some ⟨none, .bra pc true⟩)
    (ht : At t (pc + 1) ((dst, .pred ok) :: F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if ok then pc + 3 else pc) F := by
  obtain ⟨s, hStep, hS⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    hBranch ok ht ht.2.2.2.2.1 (by simp)
  have hAll : run kernel Assumptions.all l g 1 t = some s := by
    simpa only [run, tauStep, afterPollCore ht.1 (by omega) hBranch rfl]
      using hStep
  cases ok
  · have hs : s.pc = pc + 2 := hS.1
    let u := { s with pc := pc }
    have hBack : run kernel [] l g 1 s = some u := by
      apply run_local hRetry rfl hS
      rw [execLocalA_nil]
      rfl
    have hBackAll : run kernel Assumptions.all l g 1 s = some u := by
      simpa only [run, tauStep,
        afterPollCore hs (by omega) hRetry rfl] using hBack
    exact ⟨u, run_rtg (run_comp hAll hBackAll), rfl, hS.2.1, hS.2.2.1,
      hS.2.2.2.1, hS.2.2.2.2.2⟩
  · exact ⟨s, run_rtg hAll, hS.mono hS.2.2.2.2.2⟩

/-- Any decoded correction acquire spin consists of a finite number of retries followed
by one successful acquire on a terminated suffix. -/
theorem correctionAcquireSpin {l : Launch} {g pc dst baseReg phaseReg addr phase : Nat}
    {t : TState} {F : List (Nat × Value)} {events : List Event}
    (hLo : 8473 ≤ pc) (hBaseBound : addr < 2 ^ 32) (hBaseAlign : addr % 8 = 0)
    (hPhaseBound : phase < 2)
    (hCode : kernel.code[pc]? =
      some ⟨none, .mbarWait dst baseReg 0 (.reg phaseReg) true .cta⟩)
    (hBranch : kernel.code[pc + 1]? = some ⟨some (dst, false), .bra (pc + 3) true⟩)
    (hRetry : kernel.code[pc + 2]? = some ⟨none, .bra pc true⟩)
    (ht : At t pc F) (hFresh : ∀ pair ∈ F, pair.1 ≠ dst)
    (hBase : (baseReg, b32 addr) ∈ F) (hPhase : (phaseReg, b32 phase) ∈ F)
    (hr : Run kernel Assumptions.all l g t events none) :
    let loc : Loc := ⟨.shared, g / l.block, addr⟩
    let ev : Bool → Event := fun ok => ⟨pc, .wait loc phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u (pc + 3) F ∧ Run kernel Assumptions.all l g u rest none := by
  dsimp only
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  induction events generalizing t with
  | nil => cases hr
  | cons e tail ih =>
    let cont := fun ok => next (setReg t dst (.pred ok))
    let tmpl := Tmpl.wait loc phase cont true .cta
    have hAddr : mbarLoc l g t baseReg 0 = .ok loc := by
      have hLoc : loc = ⟨.shared, g / l.block, loc.addr⟩ := rfl
      conv_rhs => rw [hLoc]
      exact Flow.mbarLoc_b32 (holds_mem ht.2.2.2.2 hBase) hBaseBound hBaseAlign
    have hBits : readBits l g t 32 (.reg phaseReg) =
        .ok (BitVec.ofNat 64 phase) :=
      readBits_b32 (holds_mem ht.2.2.2.2 hPhase) (by omega)
    have hNext : Next kernel Assumptions.all l g t t tmpl := by
      refine ⟨.refl, ?_⟩
      rw [afterPollCore ht.1 hLo hCode rfl,
        out_event ht.2.2.2.1 (ht.1.symm ▸ hCode) rfl rfl]
      change Out.ev (tmaTmpl l g t (.mbarWait dst baseReg 0
        (.reg phaseReg) true .cta)) = _
      simp [tmaTmpl, hAddr, hBits, toNat_ofNat_lt (show phase < 2 ^ 64 by omega),
        hPhaseBound, bind, Except.bind, pure, Except.pure, ofExec, tmpl, cont]
    obtain ⟨v, hf, hNext⟩ := hNext.continuing_event (by
      rintro ⟨ok, _, hEq⟩
      cases hEq) hr
    obtain ⟨ok, rfl, hEq⟩ := hf
    obtain rfl := Option.some.inj hEq
    have hAt : At (cont ok) (pc + 1) ((dst, .pred ok) :: F) := ht.set hFresh
    obtain ⟨u, hu, hU⟩ := afterCorrectionPoll hLo ok hBranch hRetry hAt
    have hSuffix := hNext.after_local hu
    cases ok
    · obtain ⟨n, w, rest, he, hW, hRest⟩ := ih hU hSuffix
      exact ⟨n + 1, w, rest, by simp only [ht.1, he, List.replicate_succ, List.cons_append, loc],
        hW, hRest⟩
    · exact ⟨0, u, tail, by simp [ht.1, loc], hU, hSuffix⟩

/-- A terminated suffix at either normalization wait contains a finite sequence of failed
polls followed by a successful acquire, preserving the local operands and frame. -/
theorem finalizePollTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {F : List (Nat × Value)} {events : List Event}
    (stage : Fin 2) (free : Bool)
    (ht : At t (finalizePollPc stage free) F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ finalizePollPred stage free)
    (hBase : (finalizePollBase stage free, b32 (finalizePollLoc l g stage free).addr) ∈ F)
    (hPhase : (finalizePollPhase free, b32 free.toNat) ∈ F)
    (hr : Run kernel Assumptions.all l g t events none) :
    let ev : Bool → Event := fun ok =>
      ⟨finalizePollPc stage free, .wait (finalizePollLoc l g stage free) free.toNat ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u (finalizePollPc stage free + 3) F ∧
      Run kernel Assumptions.all l g u rest none := by
  have hLo : 8473 ≤ finalizePollPc stage free := by unfold finalizePollPc; omega
  have hBaseBound : (finalizePollLoc l g stage free).addr < 2 ^ 32 := by
    have hl := hp.shared.2.1
    have hs := stage.isLt
    cases free <;> simp only [finalizePollLoc, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hBaseAlign : (finalizePollLoc l g stage free).addr % 8 = 0 := by
    have hl := hp.shared.1
    cases free <;> simp only [finalizePollLoc, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hPhaseBound : free.toNat < 2 := by cases free <;> decide
  exact correctionAcquireSpin hLo hBaseBound hBaseAlign hPhaseBound
    (finalizePollCode stage free).1 (finalizePollCode stage free).2.1
    (finalizePollCode stage free).2.2 ht hFresh hBase hPhase hr

private theorem finalReciprocalPackCode (stage : Fin 2) :
    PackCode kernel (finalizePollPc stage true + 3)
      [(finalizeReciprocalPair stage, reciprocalReg stage, reciprocalReg stage)] := by
  fin_cases stage
  · exact ⟨Flow.code_8479, trivial⟩
  · exact ⟨Flow.code_8775, trivial⟩

/-- The word computed by the reciprocal instruction is duplicated into the packed operand
before the first x8 load. This local instruction leaves the remaining trace untouched. -/
theorem packFinalReciprocalLocal {l : Launch} {g : Nat} {t : TState}
    {F : List (Nat × Value)} (stage : Fin 2) (reciprocal : ℝ)
    (ht : At t (finalizePollPc stage true + 3) F)
    (hv : t.regs (reciprocalReg stage) = some (fl reciprocal))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ finalizeReciprocalPair stage) :
    ∃ u, At u (finalizeLoadPc stage 0)
      ((finalizeReciprocalPair stage, .pair (fl reciprocal) (fl reciprocal)) :: F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  let d := finalizeReciprocalPair stage
  let r := reciprocalReg stage
  let v : Nat → Value := fun _ => fl reciprocal
  let u := next (setReg t d (.pair (fl reciprocal) (fl reciprocal)))
  have hFreshSrc : d ≠ r := by fin_cases stage <;> decide
  have hPC : 8012 ≤ t.pc := by rw [ht.1]; unfold finalizePollPc; omega
  have hRun : run kernel Assumptions.all l g 1 t = some u := by
    rw [Assumptions.run_all_eq_numeric]
    apply (packs_run numericPack v [(d, r, r)] t (ht.1.symm ▸ finalReciprocalPackCode stage)
      ht.2.2.2.1 ?_ ?_ (fun i _ => correctionSegFree (by omega))).1 rfl
    · intro q hq
      rw [List.mem_singleton] at hq
      subst q
      exact ⟨hv, hv⟩
    · intro q hq q' hq'
      rw [List.mem_singleton] at hq hq'
      subst q q'
      exact ⟨hFreshSrc, hFreshSrc⟩
  have hPc : finalizePollPc stage true + 3 + 1 = finalizeLoadPc stage 0 := by
    fin_cases stage <;> decide
  exact ⟨u, hPc ▸ ht.set hFresh, run_rtg hRun⟩

theorem packFinalReciprocal {l : Launch} {g : Nat} {t : TState}
    {F : List (Nat × Value)} {events : List Event} (stage : Fin 2) (reciprocal : ℝ)
    (ht : At t (finalizePollPc stage true + 3) F)
    (hv : t.regs (reciprocalReg stage) = some (fl reciprocal))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ finalizeReciprocalPair stage)
    (hr : Run kernel Assumptions.all l g t events none) :
    ∃ u, At u (finalizeLoadPc stage 0)
      ((finalizeReciprocalPair stage, .pair (fl reciprocal) (fl reciprocal)) :: F) ∧
      Run kernel Assumptions.all l g u events none := by
  obtain ⟨u,hu,hLocal⟩ := packFinalReciprocalLocal (l := l) (g := g) stage reciprocal ht hv hFresh
  exact ⟨u,hu,hr.after_local hLocal⟩

/-- Both acquire spins and the reciprocal pack lead to the actual first x8 load. -/
theorem finalizePollAndPack {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {F : List (Nat × Value)} {events : List Event}
    (stage : Fin 2) (reciprocal : ℝ)
    (ht : At t (finalizePollPc stage false) F)
    (hFresh : ∀ pair ∈ F, (∀ free, pair.1 ≠ finalizePollPred stage free) ∧
      pair.1 ≠ finalizeReciprocalPair stage)
    (hBase : ∀ free, (finalizePollBase stage free, b32 (finalizePollLoc l g stage free).addr) ∈ F)
    (hPhase : ∀ free, (finalizePollPhase free, b32 free.toNat) ∈ F)
    (hRecip : (reciprocalReg stage, fl reciprocal) ∈ F)
    (hr : Run kernel Assumptions.all l g t events none) :
    let ev : Bool → Bool → Event := fun free ok =>
      ⟨finalizePollPc stage free, .wait (finalizePollLoc l g stage free) free.toNat ok true .cta⟩
    ∃ n k u rest,
      events = List.replicate n (ev false false) ++
        (ev false true :: List.replicate k (ev true false) ++ (ev true true :: rest)) ∧
      At u (finalizeLoadPc stage 0)
        ((finalizeReciprocalPair stage, .pair (fl reciprocal) (fl reciprocal)) :: F) ∧
      Run kernel Assumptions.all l g u rest none := by
  dsimp only
  obtain ⟨n, s, rest1, hEvents1, hAt1, hRun1⟩ := finalizePollTrace hp stage false ht
    (fun rv h => (hFresh rv h).1 false) (hBase false) (hPhase false) hr
  have hPc : finalizePollPc stage false + 3 = finalizePollPc stage true := by
    fin_cases stage <;> decide
  obtain ⟨k, v, rest, hEvents2, hAt2, hRun2⟩ := finalizePollTrace hp stage true (hPc ▸ hAt1)
    (fun rv h => (hFresh rv h).1 true) (hBase true) (hPhase true) hRun1
  obtain ⟨u, hu, hTail⟩ := packFinalReciprocal stage reciprocal hAt2
    (holds_mem hAt2.2.2.2.2 hRecip) (fun rv hm => (hFresh rv hm).2) hRun2
  refine ⟨n, k, u, rest, ?_, hu, hTail⟩
  rw [hEvents1, hEvents2]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Correction
