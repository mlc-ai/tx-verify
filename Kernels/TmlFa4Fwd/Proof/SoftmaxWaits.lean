-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part053
public import Kernels.TmlFa4Fwd.Flow.Code.Part054
public import Kernels.TmlFa4Fwd.Flow.Code.Part076
public import Kernels.TmlFa4Fwd.Flow.Code.Part079
public import Kernels.TmlFa4Fwd.Flow.Code.Part080
public import Kernels.TmlFa4Fwd.Flow.Code.Part102
public import Kernels.TmlFa4Fwd.Flow.Code.Part104
public import Kernels.TmlFa4Fwd.Flow.Code.Part116
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Lemmas.Flow.Events
public import Mathlib.Tactic.FinCases

import Lemmas.Step.PollProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The ten polls in the two-stage softmax body, in instruction order. -/
structure WaitSite where
  pc : Nat
  result : Nat
  base : Nat
  phase : Nat
  offset : Nat

def waitSite : Fin 10 → WaitSite
  | 0 => ⟨3420, 9750, 2767, 2768, 192⟩
  | 1 => ⟨3425, 9751, 2769, 2770, 80⟩
  | 2 => ⟨3498, 9752, 2771, 2770, 320⟩
  | 3 => ⟨4874, 9753, 3948, 3949, 192⟩
  | 4 => ⟨5109, 9754, 3964, 7253, 80⟩
  | 5 => ⟨5181, 9755, 3965, 7250, 320⟩
  | 6 => ⟨6558, 9820, 5119, 7258, 192⟩
  | 7 => ⟨6676, 9821, 5126, 7253, 80⟩
  | 8 => ⟨7463, 9886, 5802, 7258, 192⟩
  | 9 => ⟨7738, 9887, 5864, 7258, 192⟩
/-- The decoded poll, success branch and retry branch of each softmax poll. -/
theorem waitCode (i : Fin 10) :
    let s := waitSite i
    kernel.code[s.pc]? = some ⟨none, .mbarWait s.result s.base 0 (.reg s.phase) true .cta⟩ ∧
      kernel.code[s.pc + 1]? = some ⟨some (s.result, false), .bra (s.pc + 3) true⟩ ∧
      kernel.code[s.pc + 2]? = some ⟨none, .bra s.pc true⟩ := by
  fin_cases i
  · exact ⟨Flow.code_3420, Flow.code_3421, Flow.code_3422⟩
  · exact ⟨Flow.code_3425, Flow.code_3426, Flow.code_3427⟩
  · exact ⟨Flow.code_3498, Flow.code_3499, Flow.code_3500⟩
  · exact ⟨Flow.code_4874, Flow.code_4875, Flow.code_4876⟩
  · exact ⟨Flow.code_5109, Flow.code_5110, Flow.code_5111⟩
  · exact ⟨Flow.code_5181, Flow.code_5182, Flow.code_5183⟩
  · exact ⟨Flow.code_6558, Flow.code_6559, Flow.code_6560⟩
  · exact ⟨Flow.code_6676, Flow.code_6677, Flow.code_6678⟩
  · exact ⟨Flow.code_7463, Flow.code_7464, Flow.code_7465⟩
  · exact ⟨Flow.code_7738, Flow.code_7739, Flow.code_7740⟩

private theorem waitOffExp2 (i : Fin 10) (b : Fin 3) :
    (waitSite i).pc + b.val ∉ Assumptions.swExp2Sites := by
  fin_cases i <;> fin_cases b <;> decide

/-- Both softmax groups use consecutive barrier positions for the same operation. -/
def waitLoc (l : Launch) (g : Nat) (stage : Fin 2) (i : Fin 10) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + ((waitSite i).offset + 8 * stage.val)⟩

private theorem waitAlign (i : Fin 10) : (waitSite i).offset % 8 = 0 := by
  fin_cases i <;> decide

private theorem waitRange (i : Fin 10) : (waitSite i).offset ≤ 320 := by
  fin_cases i <;> decide

section
variable {p : Params} {l : Launch}

/-- The softmax poll reads the per-stage barrier and returns the predicate for its own branch. -/
theorem waitTemplate {m : Mem0} (hp : Pre p l m) (stage : Fin 2) (i : Fin 10) (g : Nat) (t : TState)
    (phase : Nat) (hpc : t.pc = (waitSite i).pc) (hf : t.fault = none) (hPhase : phase < 2)
    (hb : t.regs (waitSite i).base = some (b32 (waitLoc l g stage i).addr))
    (hr : t.regs (waitSite i).phase = some (b32 phase)) :
    out kernel Assumptions.all l g t = .ev (.wait (waitLoc l g stage i) phase
      (fun ok => next (setReg t (waitSite i).result (.pred ok))) true .cta) := by
  have hs := hp.shared.2.1
  have hStage := stage.isLt
  have haddr : (waitLoc l g stage i).addr < 2 ^ 32 := by
    change l.sharedBase + ((waitSite i).offset + 8 * stage.val) < 2 ^ 32
    have := waitRange i
    omega
  have hAlign : (waitLoc l g stage i).addr % 8 = 0 := by
    change (l.sharedBase + ((waitSite i).offset + 8 * stage.val)) % 8 = 0
    have hA := hp.shared.1
    have hO := waitAlign i
    omega
  have hLoc := mbarLoc_b32 (L := l) (g := g) hb haddr hAlign
  have hBits : readBits l g t 32 (.reg (waitSite i).phase) = .ok (BitVec.ofNat 64 phase) := by
    simp [readBits, readReg, hr, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat (show phase < 2 ^ 32 by omega) (by decide)]
  have hc := (waitCode i).1
  rw [← hpc] at hc
  rw [out_event hf hc rfl rfl]
  change Out.ev (eventTmpl Assumptions.all l g t
    (.mbarWait (waitSite i).result (waitSite i).base 0 (.reg (waitSite i).phase) true .cta)) = _
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp [eventTmpl, widenMbarScope, hScope, tmaTmpl, hLoc, hBits, bind, Except.bind, pure,
    Except.pure, ofExec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPhase, waitLoc]

/-- The decoded parity branch either retries the same poll or continues past it. -/
theorem waitBranch {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (i : Fin 10) (ok : Bool) (ht : At t ((waitSite i).pc + 1) F)
    (hp : t.regs (waitSite i).result = some (.pred ok)) :
    ∃ u, run kernel Assumptions.all l g (if ok then 1 else 2) t = some u ∧
      At u (if ok then (waitSite i).pc + 3 else (waitSite i).pc) F := by
  obtain ⟨u, hu, hAt⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    (waitCode i).2.1 ok ht hp (by simp)
  have eqTau : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t := by
    apply Assumptions.tauStep_all_eq_nil (by rw [ht.1]; exact waitOffExp2 i 1)
      (by rw [ht.1]; exact (waitCode i).2.1) rfl
  have hu' : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run, eqTau] using hu
  cases ok
  · have huPc : u.pc = (waitSite i).pc + 2 := hAt.1
    have hCode := (waitCode i).2.2
    rw [← huPc] at hCode
    have hzCore : tauStep kernel [] l g u = some {u with pc := (waitSite i).pc} := by
      simp [tauStep, out, hAt.2.2.2.1, hCode, guardHolds, Op.isLocal, execLocalA,
        execLocalRule, execLocal, Op.rule, execBranch, pure, Except.pure]
    have hz : tauStep kernel Assumptions.all l g u = some {u with pc := (waitSite i).pc} := by
      rw [Assumptions.tauStep_all_eq_nil (by rw [huPc]; exact waitOffExp2 i 2) hCode rfl]
      exact hzCore
    have hStep : run kernel Assumptions.all l g 1 u = some {u with pc := (waitSite i).pc} :=
      by simp only [run, hz, Option.bind_some]
    exact ⟨_, run_comp hu' hStep, rfl, hAt.2⟩
  · exact ⟨u, hu', hAt⟩

/-- A terminated suffix that begins at a softmax wait contains zero or more failed polls,
one successful poll, and the actual continuation at the decoded success target. -/
theorem waitTraceWithPathInPrefix {m : Mem0} (hp : Pre p l m) (stage : Fin 2) (i : Fin 10)
    (g phase : Nat) (hPhase : phase < 2) {F : List (Nat × Value)} {t : TState} {events : List Event}
    {ending : Option TState} (hBase : ((waitSite i).base, b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (hFresh : ∀ x ∈ F, x.1 ≠ (waitSite i).result)
    (ht : At t (waitSite i).pc F) (hRun : Run kernel Assumptions.all l g t events ending)
    (hPresent : ending = none ∨ ∃ later ∈ events, later.pc ≠ (waitSite i).pc) :
    ∃ failed u suffix,
      events = List.replicate failed
        ⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase false true .cta⟩ ++
        (⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase true true .cta⟩ :: suffix) ∧
      At u ((waitSite i).pc + 3) F ∧ Run kernel Assumptions.all l g u suffix ending ∧
      (∃ pre, At pre (waitSite i).pc F ∧
        TraceReach kernel Assumptions.all l g t (List.replicate failed
          ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true .cta⟩) pre ∧
        Stops kernel Assumptions.all l g pre) ∧
      TraceReach kernel Assumptions.all l g t
        (List.replicate failed ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true
          .cta⟩ ++
          [⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase true true .cta⟩]) u := by
  induction events generalizing t with
  | nil =>
    rcases hPresent with rfl | ⟨e,he,_⟩
    · cases hRun
    · cases he
  | cons e es ih =>
    have hn : Next kernel Assumptions.all l g t t
        (.wait (waitLoc l g stage i) phase
          (fun ok => next (setReg t (waitSite i).result (.pred ok))) true .cta) :=
      ⟨.refl, waitTemplate hp stage i g t phase ht.1 ht.2.2.2.1 hPhase
        (holds_mem ht.2.2.2.2 hBase) (holds_mem ht.2.2.2.2 hPar)⟩
    obtain ⟨_, ⟨ok, hEvent, hState⟩, hr⟩ := hn.continuing_event (by
      rintro ⟨_, _, hBad⟩
      cases hBad) hRun
    obtain rfl := Option.some.inj hState
    have hAt := ht.set (v := .pred ok) hFresh
    obtain ⟨u, hLocal, hU⟩ := waitBranch i ok (hAt.mono hAt.2.2.2.2.2) hAt.2.2.2.2.1
    have hLater : ending = none ∨ ∃ later ∈ es, later.pc ≠ (waitSite i).pc := by
      refine hPresent.imp_right ?_
      rintro ⟨later,hMem,hDifferent⟩
      refine ⟨later,(List.mem_cons.mp hMem).resolve_left ?_,hDifferent⟩
      intro hEq
      exact hDifferent ((congrArg Event.pc (hEq.trans hEvent)).trans ht.1)
    have hMore : es ≠ [] := by
      intro hEmpty
      subst es
      cases hr
      rcases hLater with h | ⟨e,he,_⟩
      · cases h
      · cases he
    have hTail := hr.after_local_nonempty (run_rtg hLocal) hMore
    have hStep : EStep kernel Assumptions.all l g t
        ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase ok true .cta⟩
        (some (next (setReg t (waitSite i).result (.pred ok)))) := by
      refine ⟨_,hn.stop,ok,?_,rfl⟩
      rw [ht.1]
    rw [ht.1] at hEvent
    cases ok
    · obtain ⟨failed,v,suffix,hEs,hV,hRest,⟨pre,hPre,hReach,hStop⟩,hTotal⟩ := ih hU hTail hLater
      have hPath := (TraceReach.of_local (run_rtg hLocal)).append hReach
      refine ⟨failed+1,v,suffix,by rw [hEvent,hEs,List.replicate_succ]; rfl,
        hV,hRest,⟨pre,hPre,?_,hStop⟩,?_⟩
      · rw [List.replicate_succ]
        exact .event hStep hPath
      · rw [List.replicate_succ,List.cons_append]
        exact .event hStep ((TraceReach.of_local (run_rtg hLocal)).append hTotal)
    · exact ⟨0,u,es,by rw [hEvent]; rfl,hU,hTail,
        ⟨t,ht,.refl _,stops_of_estep hStep⟩,.event hStep (.of_local (run_rtg hLocal))⟩

theorem waitTraceWithSourceInPrefix {m : Mem0} (hp : Pre p l m) (stage : Fin 2) (i : Fin 10)
    (g phase : Nat) (hPhase : phase < 2) {F : List (Nat × Value)} {t : TState} {events : List Event}
    {ending : Option TState} (hBase : ((waitSite i).base, b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (hFresh : ∀ x ∈ F, x.1 ≠ (waitSite i).result)
    (ht : At t (waitSite i).pc F) (hRun : Run kernel Assumptions.all l g t events ending)
    (hPresent : ending = none ∨ ∃ later ∈ events, later.pc ≠ (waitSite i).pc) :
    ∃ failed u suffix,
      events = List.replicate failed
        ⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase false true .cta⟩ ++
        (⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase true true .cta⟩ :: suffix) ∧
      At u ((waitSite i).pc + 3) F ∧ Run kernel Assumptions.all l g u suffix ending ∧
      ∃ pre, At pre (waitSite i).pc F ∧
        TraceReach kernel Assumptions.all l g t (List.replicate failed
          ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true .cta⟩) pre ∧
        Stops kernel Assumptions.all l g pre := by
  obtain ⟨failed,u,suffix,hEvents,hu,hTail,hSource,_⟩ :=
    waitTraceWithPathInPrefix hp stage i g phase hPhase hBase hPar hFresh ht hRun hPresent
  exact ⟨failed,u,suffix,hEvents,hu,hTail,hSource⟩

/-- The success continuation's cursor advances by the failed-poll count plus its one
successful wait, all on the actual thread trace. -/
theorem waitTraceAtWithPath {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2) (i : Fin 10)
    (g phase : Nat) (hPhase : phase < 2) {j : Nat} {F : List (Nat × Value)} {t : TState}
    (hBase : ((waitSite i).base, b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (hFresh : ∀ x ∈ F, x.1 ≠ (waitSite i).result)
    (ht : At t (waitSite i).pc F) (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ failed u,
      (X.tr g).drop j = List.replicate failed
        ⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase false true .cta⟩ ++
        (⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase true true .cta⟩ ::
          (X.tr g).drop (j + failed + 1)) ∧
      At u ((waitSite i).pc + 3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + failed + 1)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (failed+1)) u := by
  obtain ⟨failed,u,suffix,hPrefix,hU,hTail,_,hPath⟩ :=
    waitTraceWithPathInPrefix hp stage i g phase hPhase hBase hPar hFresh ht hRun (.inl rfl)
  have hDrop : (X.tr g).drop (j + failed + 1) = suffix := by
    rw [Nat.add_assoc, ← List.drop_drop, hPrefix, ← List.drop_drop]
    have hSkip (a b : Event) : (List.replicate failed a ++ b :: suffix).drop failed =
        b :: suffix := by
      have h := List.drop_append_length (l₁ := List.replicate failed a) (l₂ := b :: suffix)
      rwa [List.length_replicate] at h
    rw [hSkip]
    rfl
  refine ⟨failed,u,hDrop.symm ▸ hPrefix,hU,hDrop.symm ▸ hTail,?_⟩
  rw [hPrefix,List.take_append]
  simp only [List.length_replicate, List.take_of_length_le (by simp : (List.replicate failed _ :
    List Event).length ≤ failed+1),
    Nat.add_sub_cancel_left, List.take_succ_cons,List.take_zero]
  exact hPath

theorem waitTraceAt {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2) (i : Fin 10)
    (g phase : Nat) (hPhase : phase < 2) {j : Nat} {F : List (Nat × Value)} {t : TState}
    (hBase : ((waitSite i).base, b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (hFresh : ∀ x ∈ F, x.1 ≠ (waitSite i).result)
    (ht : At t (waitSite i).pc F) (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ failed u,
      (X.tr g).drop j = List.replicate failed
        ⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase false true .cta⟩ ++
        (⟨(waitSite i).pc, .wait (waitLoc l g stage i) phase true true .cta⟩ ::
          (X.tr g).drop (j + failed + 1)) ∧
      At u ((waitSite i).pc + 3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + failed + 1)) none := by
  obtain ⟨failed,u,hPolls,hu,hTail,_⟩ :=
    waitTraceAtWithPath hp stage i g phase hPhase hBase hPar hFresh ht hRun
  exact ⟨failed,u,hPolls,hu,hTail⟩

/-- A maximal softmax cursor completes its decoded acquire if a stopped poll has opposite parity. -/
theorem waitAtCountOfMaximalWithTrace {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    (i : Fin 10) {phase : Nat} (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result)
    (hBase : ((waitSite i).base,b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase,b32 phase) ∈ F) (mark : Event → Bool)
    (hFail : mark ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true .cta⟩ = false)
    (ordinal : Nat)
    (hReady : (X.tr g).countP mark = ordinal →
      ∀ {t u}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → At u (waitSite i).pc F →
      let log := X.objects (waitLoc l g stage i)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) {pos : Nat}
    {t u : TState} {ending : Option TState} (hCount : ((X.tr g).take pos).countP mark = ordinal)
    (hPositive : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Step.Released l X g) (hAt : At u (waitSite i).pc F)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait (waitLoc l g stage i) phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F ∧
      (X.tr g).drop pos = List.replicate n
        ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true .cta⟩ ++
        ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase true true .cta⟩ ::
          (X.tr g).drop (pos+n+1) := by
  let resume := fun t ok => next (setReg t (waitSite i).result (.pred ok))
  have hOut (v : TState) (hv : At v (waitSite i).pc F) :
      v.pc = (waitSite i).pc ∧ out kernel Assumptions.all l g v = .ev
        (.wait (waitLoc l g stage i) phase (resume v) true .cta) :=
    ⟨hv.1, waitTemplate hp stage i g v phase hv.1 hv.2.2.2.1 hPhase
      (holds_mem hv.2.2.2.2 hBase) (holds_mem hv.2.2.2.2 hPar)⟩
  have hAfter (v : TState) (hv : At v (waitSite i).pc F) (ok : Bool) :
      ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume v ok) w ∧
        At w (if ok then (waitSite i).pc+3 else (waitSite i).pc) F := by
    have hSet := hv.set (v := .pred ok) hFresh
    have hAt : At (resume v ok) ((waitSite i).pc+1) F := hSet.mono hSet.2.2.2.2.2
    have hResult : (resume v ok).regs (waitSite i).result = some (.pred ok) := by
      simp [resume, next, setReg]
    obtain ⟨w, hr, hw⟩ := waitBranch i ok hAt hResult
    exact ⟨w, run_rtg hr, hw⟩
  have hRetry (v : TState) (hv : At v (waitSite i).pc F) :
      ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume v false) w ∧
        At w (waitSite i).pc F := hAfter v hv false
  obtain ⟨n,v,hv,he,hPast,hRest,hPolls⟩ :=
    Step.retrying_poll_at_count_of_maximal hMax Assumptions.wfStep
    hg hOut hRetry mark hFail ordinal hReady hCount hPositive hBound hReleased
      hAt hPrefix hTail hLocal
  obtain ⟨w,hNext,hAt⟩ := hAfter v hv true
  exact ⟨n,resume v true,w,he,hPast,hRest,hNext,hAt,hPolls⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (stage : Fin 2)
    (i : Fin 10) {phase : Nat} (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result)
    (hBase : ((waitSite i).base,b32 (waitLoc l g stage i).addr) ∈ F)
    (hPar : ((waitSite i).phase,b32 phase) ∈ F)
    (hReady : ∀ {t u}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → At u (waitSite i).pc F →
      let log := X.objects (waitLoc l g stage i)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) {pos : Nat}
    {t u : TState} {ending : Option TState} (hPositive : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Step.Released l X g) (hAt : At u (waitSite i).pc F)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
include hp hMax hg stage i hPhase hFresh hBase hPar hReady hPositive hBound hReleased hAt hPrefix
    hTail hLocal

/-- A maximal softmax cursor completes its decoded acquire if a stopped poll has opposite parity. -/
theorem waitOfMaximalWithTrace :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait (waitLoc l g stage i) phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F ∧
      (X.tr g).drop pos = List.replicate n
        ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase false true .cta⟩ ++
        ⟨(waitSite i).pc,.wait (waitLoc l g stage i) phase true true .cta⟩ ::
          (X.tr g).drop (pos+n+1) :=
  waitAtCountOfMaximalWithTrace hp hMax hg stage i hPhase hFresh hBase hPar
    (Flow.okPoll (waitLoc l g stage i)) rfl _
    (fun _ => hReady) rfl hPositive hBound hReleased hAt hPrefix hTail hLocal

theorem waitOfMaximalWithTcCount :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait (waitLoc l g stage i) phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F ∧
      ((X.tr g).take (pos+n+1)).countP isTcColl = ((X.tr g).take pos).countP isTcColl := by
  obtain ⟨n,after,v,he,hPast,hRest,hNext,hAt,hPolls⟩ :=
    waitOfMaximalWithTrace hp hMax hg stage i hPhase hFresh hBase hPar hReady
      hPositive hBound hReleased hAt hPrefix hTail hLocal
  refine ⟨n,after,v,he,hPast,hRest,hNext,hAt,?_⟩
  let failed := Event.mk (waitSite i).pc (.wait (waitLoc l g stage i) phase false true .cta)
  let success := Event.mk (waitSite i).pc (.wait (waitLoc l g stage i) phase true true .cta)
  have hLength : (List.replicate n failed ++ [success]).length = n+1 := by simp
  have hSplit : (X.tr g).drop pos = (List.replicate n failed ++ [success]) ++
      (X.tr g).drop (pos+n+1) := by
    simpa [List.append_assoc,failed,success] using hPolls
  rw [Nat.add_assoc,List.take_add,hSplit,← hLength,List.take_append_length,List.countP_append]
  suffices (List.replicate n failed ++ [success]).countP isTcColl = 0 by omega
  apply List.countP_eq_zero.mpr
  intro e he
  rcases List.mem_append.mp he with hf | hs
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp hf
    simp [failed,isTcColl]
  · obtain rfl := List.mem_singleton.mp hs
    simp [success,isTcColl]

/-- The checked poll loop returns after its first success. -/
theorem waitOfMaximal :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait (waitLoc l g stage i) phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F := by
  obtain ⟨n,v,w,he,hPast,hTail,hLocal,hAt,_⟩ := waitOfMaximalWithTcCount hp hMax hg stage i
    hPhase hFresh hBase hPar hReady hPositive hBound hReleased hAt hPrefix hTail hLocal
  exact ⟨n,v,w,he,hPast,hTail,hLocal,hAt⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
