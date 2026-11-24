-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Flow.Code.Part033
public import Kernels.TmlFa4Fwd.Flow.Code.Part034
public import Kernels.TmlFa4Fwd.Flow.Code.Part035
public import Kernels.TmlFa4Fwd.Flow.Code.Part036
public import Kernels.TmlFa4Fwd.Flow.Code.Part037
public import Kernels.TmlFa4Fwd.Flow.Code.Part038
public import Kernels.TmlFa4Fwd.Flow.Code.Part039
public import Kernels.TmlFa4Fwd.Flow.Code.Part040
public import Kernels.TmlFa4Fwd.Flow.Code.Part041
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Step.Released
import Lemmas.Step.PollProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Lemmas.Flow.LoadShared

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

structure WaitSite where
  pc : Nat
  result : Nat
  base : Nat
  phase : Nat
  uniform : Bool

/-- The Q, KV, P-ready and P-tail poll instructions in their code order. -/
def waitSite : Fin 14 → WaitSite
  | 0 => ⟨2141, 9634, 2535, 2536, true⟩
  | 1 => ⟨2145, 9635, 2537, 2536, true⟩
  | 2 => ⟨2210, 9652, 2562, 2563, true⟩
  | 3 => ⟨2294, 9669, 2568, 7208, true⟩
  | 4 => ⟨2297, 9670, 2610, 7205, true⟩
  | 5 => ⟨2335, 9680, 2614, 7205, false⟩
  | 6 => ⟨2352, 9681, 2571, 2572, true⟩
  | 7 => ⟨2419, 9698, 2615, 7205, true⟩
  | 8 => ⟨2450, 9708, 2618, 7205, false⟩
  | 9 => ⟨2545, 9725, 2609, 7208, true⟩
  | 10 => ⟨2548, 9726, 2610, 7205, true⟩
  | 11 => ⟨2586, 9736, 2614, 7205, false⟩
  | 12 => ⟨2595, 9737, 2615, 7205, true⟩
  | 13 => ⟨2626, 9747, 2618, 7205, false⟩

private def waitCodeMatches (i : Fin 14) : Bool :=
  let s := waitSite i
  match kernel.code[s.pc]?, kernel.code[s.pc + 1]?, kernel.code[s.pc + 2]? with
  | some ⟨none, .mbarWait rd base off phase acq scope⟩,
      some ⟨some (guard, false), .bra done doneUniform⟩, some ⟨none, .bra retry retryUniform⟩ =>
    decide (rd = s.result ∧ base = s.base ∧ off = 0 ∧ phase = .reg s.phase ∧ acq = true ∧
      scope = .cta ∧ guard = s.result ∧ done = s.pc + 3 ∧ doneUniform = s.uniform ∧
      retry = s.pc ∧ retryUniform = s.uniform)
  | _, _, _ => false

private theorem waitCode (i : Fin 14) :
    let s := waitSite i
    kernel.code[s.pc]? = some ⟨none, .mbarWait s.result s.base 0 (.reg s.phase) true .cta⟩ ∧
      kernel.code[s.pc + 1]? = some ⟨some (s.result, false), .bra (s.pc + 3) s.uniform⟩ ∧
      kernel.code[s.pc + 2]? = some ⟨none, .bra s.pc s.uniform⟩ := by
  have hAll : (List.finRange 14).all waitCodeMatches = true := by decide +kernel
  have h := List.all_eq_true.mp hAll i (List.mem_finRange i)
  unfold waitCodeMatches at h
  dsimp only at h ⊢
  split at h <;> simp_all

private theorem waitRange (i : Fin 14) : 1904 ≤ (waitSite i).pc ∧ (waitSite i).pc + 3 < 2768 := by
  have h : (List.finRange 14).all (fun j =>
      decide (1904 ≤ (waitSite j).pc ∧ (waitSite j).pc + 3 < 2768)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

/-- An MMA poll is a CTA acquire on the decoded address and parity. -/
theorem waitTemplate {l : Launch} {g : Nat} {t : TState} (i : Fin 14)
    {addr phase : Nat} (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) (hPhase : phase < 2)
    (hpc : t.pc = (waitSite i).pc) (hf : t.fault = none)
    (hBase : t.regs (waitSite i).base = some (b32 addr))
    (hPar : t.regs (waitSite i).phase = some (b32 phase)) :
    out kernel Assumptions.all l g t = .ev
      (.wait ⟨.shared, g / l.block, addr⟩ phase
        (fun ok => next (setReg t (waitSite i).result (.pred ok))) true .cta) := by
  let site := waitSite i
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  have hBounds := waitRange i
  have hCode := (waitCode i).1
  rw [← hpc] at hCode
  rw [out_eq_core (by omega) (by omega), out_event hf hCode rfl rfl]
  have hEff : effAddr l g t .shared site.base 0 = .ok loc := by
    simpa only [Nat.cast_zero, Nat.add_zero, loc] using
      (effAddr_b32_off (g := g) (L := l) (off := 0) hBase (by omega))
  have hLoc : mbarLoc l g t site.base 0 = .ok loc := by
    simp [mbarLoc, hEff, loc, hAlign, bind, Except.bind, pure, Except.pure]
  have hPhase32 : phase < 2 ^ 32 := by omega
  have hPhase64 : phase < 2 ^ 64 := by omega
  change t.regs site.phase = some (b32 phase) at hPar
  have hBits : readBits l g t 32 (.reg site.phase) = .ok (BitVec.ofNat 64 phase) := by
    simp only [readBits, readReg, hPar, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat hPhase32 (by decide)]
  change Out.ev (eventTmpl [] l g t (.mbarWait site.result site.base 0 (.reg site.phase)
    true .cta)) = _
  simp [eventTmpl, widenMbarScope, tmaTmpl, hLoc, hBits, toNat_ofNat_lt hPhase64, hPhase,
    bind, Except.bind, pure, Except.pure, ofExec, site, loc]

private theorem afterWait {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (i : Fin 14) (ok : Bool)
    (ht : At t ((waitSite i).pc + 1) (((waitSite i).result, .pred ok) :: F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if ok then (waitSite i).pc + 3 else (waitSite i).pc) F := by
  let site := waitSite i
  have hRange := waitRange i
  change 1904 ≤ site.pc ∧ site.pc + 3 < 2768 at hRange
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (waitCode i).2.1 ok ht ht.2.2.2.2.1 (by simp)
  have htPc : t.pc = site.pc + 1 := ht.1
  have huAll := localRun (n := 1) (by omega) (by omega) htPc rfl hu
  cases ok
  · have hPc : u.pc = site.pc + 2 := hU.1
    let v := { u with pc := site.pc }
    have hBack : run kernel [] l g 1 u = some v := by
      apply run_local (waitCode i).2.2 rfl hU
      rw [execLocalA_nil]
      rfl
    have hLocal := localRun (n := 1) (by omega) (by omega) hPc rfl hBack
    exact ⟨v, run_rtg (run_comp huAll hLocal), rfl, hU.2.1, hU.2.2.1, hU.2.2.2.1,
      hU.2.2.2.2.2⟩
  · exact ⟨u, run_rtg huAll, hU.mono hU.2.2.2.2.2⟩

private theorem walkAfterLocal {l : Launch} {g : Nat} {s t : TState}
    {es : List Event} {vs : List Visit}
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es = [] ∨ ∃ rest, rest.length ≤ vs.length ∧ Walk kernel Assumptions.all l g t es rest := by
  induction hLocal using Relation.ReflTransGen.head_induction_on generalizing vs with
  | refl => exact .inr ⟨vs, Nat.le_refl _, hw⟩
  | head ht _ ih =>
    cases hw with
    | stop => exact .inl rfl
    | tau ht' hw =>
      obtain rfl := Out.tau.inj (ht.symm.trans ht')
      exact (ih hw).imp_right (fun ⟨rest, hLen, hWalk⟩ =>
        ⟨rest, hLen.trans (by simp), hWalk⟩)
    | ev he _ => exact (not_tau_of_stops (stops_of_estep he) ht).elim
    | last he => exact (not_tau_of_stops (stops_of_estep he) ht).elim

section
variable {l : Launch} {g addr phase : Nat} {t : TState} {F : List (Nat × Value)} (i : Fin 14)
    (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) (hPhase : phase < 2)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result) (hBase : ((waitSite i).base, b32 addr) ∈ F)
    (hPar : ((waitSite i).phase, b32 phase) ∈ F) (ht : At t (waitSite i).pc F) {events : List Event}
include i hAddr hAlign hPhase hFresh hBase hPar ht

/-- A possibly truncated walk at a canonical MMA poll has only failed attempts unless it
reaches the successful event. In the latter case we retain its exact instruction frame. -/
theorem waitWalk {visits : List Visit} (hw : Walk kernel Assumptions.all l g t events visits) :
    let ev : Bool → Event := fun ok =>
      ⟨(waitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    (∃ n, events = List.replicate n (ev false)) ∨
      ∃ n rest, events = List.replicate n (ev false) ++ ev true :: rest ∧
        (rest = [] ∨ ∃ u post, post.length < visits.length ∧ At u ((waitSite i).pc + 3) F ∧
          Walk kernel Assumptions.all l g u rest post) := by
  dsimp only
  let site := waitSite i
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  let ev : Bool → Event := fun ok => ⟨site.pc, .wait loc phase ok true .cta⟩
  change (∃ n, events = List.replicate n (ev false)) ∨
    ∃ n rest, events = List.replicate n (ev false) ++ ev true :: rest ∧
      (rest = [] ∨ ∃ u post, post.length < visits.length ∧ At u (site.pc + 3) F ∧
        Walk kernel Assumptions.all l g u rest post)
  generalize hN : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing t events visits with
  | h fuel ih =>
    have hOut := waitTemplate (l := l) (g := g) i hAddr hAlign hPhase ht.1 ht.2.2.2.1
      (holds_mem ht.2.2.2.2 hBase) (holds_mem ht.2.2.2.2 hPar)
    cases hw with
    | stop => exact .inl ⟨0, rfl⟩
    | tau hTau _ => rw [Tau, hOut] at hTau; cases hTau
    | last he =>
      obtain ⟨tm, hTm, hFire⟩ := he
      rw [hOut] at hTm
      obtain rfl := Out.ev.inj hTm.symm
      obtain ⟨_, _, hImpossible⟩ := hFire
      cases hImpossible
    | @ev s u e es vs he hWalk =>
      obtain ⟨tm, hTm, hFire⟩ := he
      rw [hOut] at hTm
      obtain rfl := Out.ev.inj hTm.symm
      obtain ⟨ok, rfl, hU⟩ := hFire
      obtain rfl := Option.some.inj hU
      rw [ht.1]
      have hu : At (next (setReg t site.result (.pred ok))) (site.pc + 1)
          ((site.result, .pred ok) :: F) := ht.set hFresh
      obtain ⟨v, hLocal, hv⟩ := afterWait i ok hu
      have hRest := walkAfterLocal hLocal hWalk
      have hLess : vs.length < fuel := by simp at hN; omega
      cases ok with
      | false =>
        rcases hRest with rfl | ⟨post, hLe, hPost⟩
        · exact .inl ⟨1, rfl⟩
        rcases ih post.length (hLe.trans_lt hLess) hv hPost rfl with ⟨n, hEq⟩ |
          ⟨n, rest, hEq, hTail⟩
        · exact .inl ⟨n + 1, by rw [hEq, List.replicate_succ]⟩
        · refine .inr ⟨n + 1, rest, by rw [hEq, List.replicate_succ]; rfl, ?_⟩
          exact hTail.imp_right (fun ⟨v, suffix, hLen, hAt, hw⟩ =>
            ⟨v, suffix, by omega, hAt, hw⟩)
      | true =>
        refine .inr ⟨0, es, rfl, ?_⟩
        exact hRest.imp_right (fun ⟨post, hLen, hW⟩ =>
          ⟨v, post, hLen.trans_lt hLess, hv, hW⟩)

/-- Every terminated suffix at an MMA poll has a finite sequence of failures followed by the
first successful observation. Both paths retain the operand facts of the polling state. -/
theorem waitTraceInPrefix {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t events ending)
    (hLater : ending = none ∨ ∃ later ∈ events, (waitSite i).pc < later.pc) :
    let ev : Bool → Event := fun ok =>
      ⟨(waitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u ((waitSite i).pc + 3) F ∧ Run kernel Assumptions.all l g u rest ending := by
  dsimp only
  let site := waitSite i
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  induction events generalizing t with
  | nil =>
    rcases hLater with hDone | ⟨_,hNo,_⟩
    · subst ending
      cases hr
    · cases hNo
  | cons e tail ih =>
    have hOut := waitTemplate (l := l) (g := g) i hAddr hAlign hPhase ht.1 ht.2.2.2.1
      (holds_mem ht.2.2.2.2 hBase) (holds_mem ht.2.2.2.2 hPar)
    let cont := fun ok => next (setReg t site.result (.pred ok))
    let tmpl := Tmpl.wait loc phase cont true .cta
    have hn : Next kernel Assumptions.all l g t t tmpl := ⟨.refl, hOut⟩
    obtain ⟨v, hf, hNext⟩ := hn.continuing_event (by
      rintro ⟨ok, _, hEq⟩
      cases hEq) hr
    obtain ⟨ok, rfl, hEq⟩ := hf
    obtain rfl := Option.some.inj hEq
    have hAt : At (cont ok) (site.pc + 1) ((site.result, .pred ok) :: F) := ht.set hFresh
    obtain ⟨u, hu, hU⟩ := afterWait i ok hAt
    have hNotHead : ∀ later : Event, site.pc < later.pc →
        later ≠ ⟨t.pc, .wait loc phase ok true .cta⟩ := by
      intro later hPc hEq
      rw [hEq] at hPc
      exact (Nat.lt_irrefl _) (ht.1 ▸ hPc)
    have hTail : ending = none ∨ ∃ later ∈ tail, site.pc < later.pc := by
      refine hLater.imp_right ?_
      rintro ⟨later,hMem,hPc⟩
      rcases List.mem_cons.mp hMem with hEq | hMem
      · exact (hNotHead later hPc hEq).elim
      · exact ⟨later,hMem,hPc⟩
    have hMore : tail ≠ [] := by
      intro hNil
      rcases hTail with hDone | ⟨_,hMem,_⟩
      · rw [hNil,hDone] at hNext
        cases hNext
      · rw [hNil] at hMem
        cases hMem
    have hSuffix := hNext.after_local_nonempty hu hMore
    cases ok
    · obtain ⟨n, v, rest, he, hv, hRest⟩ := ih hU hSuffix hTail
      refine ⟨n + 1, v, rest, ?_, hv, hRest⟩
      simp only [ht.1, he, List.replicate_succ, List.cons_append, loc]
    · exact ⟨0, u, tail, by simp [ht.1, loc], hU, hSuffix⟩

/-- A terminated trace at an audited polling loop includes its success event. -/
theorem waitTrace (hr : Run kernel Assumptions.all l g t events none) :
    let ev : Bool → Event := fun ok =>
      ⟨(waitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u ((waitSite i).pc + 3) F ∧ Run kernel Assumptions.all l g u rest none :=
  waitTraceInPrefix i hAddr hAlign hPhase hFresh hBase hPar ht hr (.inl rfl)
end

variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (i : Fin 14) {addr phase : Nat} (hAddr : addr < 2^32)
    (hAlign : addr % 8 = 0) (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result) (hBase : ((waitSite i).base,b32 addr) ∈ F)
    (hPar : ((waitSite i).phase,b32 phase) ∈ F)
    (hReady : ∀ {t u}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → At u (waitSite i).pc F →
      let log := X.objects ⟨.shared,g/l.block,addr⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) {pos : Nat}
    {t u : TState} {ending : Option TState} (hPositive : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hReleased : pos = (X.tr g).length → Step.Released l X g) (hAt : At u (waitSite i).pc F)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
include hMax hg i hAddr hAlign hPhase hFresh hBase hPar hReady hPositive hBound hReleased hAt
    hPrefix

/-- A maximal MMA cursor completes its decoded acquire if a stopped poll has opposite parity. -/
theorem waitOfMaximalWithTrace (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F ∧
      (X.tr g).drop pos =
        List.replicate n ⟨(waitSite i).pc,.wait ⟨.shared,g/l.block,addr⟩ phase false true .cta⟩ ++
        (⟨(waitSite i).pc,.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ::
          (X.tr g).drop (pos+n+1)) := by
  let resume := fun t ok => next (setReg t (waitSite i).result (.pred ok))
  have hOut (v : TState) (hv : At v (waitSite i).pc F) :
      v.pc = (waitSite i).pc ∧ out kernel Assumptions.all l g v = .ev
        (.wait ⟨.shared,g/l.block,addr⟩ phase (resume v) true .cta) :=
    ⟨hv.1, waitTemplate i hAddr hAlign hPhase hv.1 hv.2.2.2.1
      (holds_mem hv.2.2.2.2 hBase) (holds_mem hv.2.2.2.2 hPar)⟩
  have hRetry (v : TState) (hv : At v (waitSite i).pc F) :
      ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume v false) w ∧
        At w (waitSite i).pc F := afterWait i false (hv.set hFresh)
  obtain ⟨n,v,hv,he,hPast,hRest,hTrace⟩ := Step.retrying_poll_of_maximal hMax Assumptions.wfStep
    hg hOut hRetry hReady hPositive hBound hReleased hAt hPrefix hTail hLocal
  obtain ⟨w,hNext,hAt⟩ := afterWait i true (hv.set hFresh)
  exact ⟨n,resume v true,w,he,hPast,hRest,hNext,hAt,hTrace⟩

/-- A maximal MMA cursor completes its decoded acquire if a stopped poll has opposite parity. -/
theorem waitOfMaximal (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    ∃ n after v,
      X.get (g,pos+n) = some ⟨(waitSite i).pc,
        .wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+n+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos+n+1)) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after v ∧
      At v ((waitSite i).pc+3) F := by
  obtain ⟨n,after,v,he,hPast,hRest,hNext,hFrame,_⟩ :=
    waitOfMaximalWithTrace hMax hg i hAddr hAlign hPhase hFresh hBase hPar hReady
      hPositive hBound hReleased hAt hPrefix hTail hLocal
  exact ⟨n,after,v,he,hPast,hRest,hNext,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
