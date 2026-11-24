-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Lemmas.Flow.Retry

@[expose] public section

/-! # A waiting loader can poll again

A loader whose trace ends with a failed poll of a slot's empty barrier is still at that wait:
after its run, local steps reach the poll, which can succeed (`loader_retry`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A loader at a slot's empty wait after its whole trace, whose last event is a failed poll, can
next perform a successful poll of the slot's empty barrier with its parity. -/
theorem loader_retry {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {l : Loader.D} {b : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .wait b) {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩) :
    ∃ t t1 u sc', Run kernel Prod L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.wait b).pc,
        .wait (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (InputRing.producerParity b)
          true true sc'⟩ (some u) := by
  obtain ⟨o, hr⟩ := hX.thr g hg
  cases o with
  | none => exact absurd hlast (run_last_not_wait hr pc m p false acq sc)
  | some t =>
    obtain ⟨t1, hl, hgood⟩ := Code.end_site (sound hpre hg) hr hσ
    have hat := hgood.1
    have hinv := hgood.2
    have hpc : (code L g).pc (.inr (.loader l)) = (Loader.Site.wait b).pc := by
      show l.site.pc = _
      rw [hs]
    have hout := Code.site_out (sound hpre hg) hgood
    have hc : kernel.code[l.site.pc]? = some ⟨none, .mbarWait (Loader.waitPred b)
        (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta⟩ := by
      rw [hs]; exact Loader.code_wait_ops b
    rw [Code.tmpl, hpc, Loader.code_wait_ops b] at hout
    dsimp only at hout
    have htpc : t1.pc = l.site.pc := hat.1
    rcases mbarWait_tmpl (A := Prod) (L := L) (g := g) (t := t1) (p' := Loader.waitPred b)
        (b := Loader.waitBase b) (off := 0) (par := .reg (Loader.waitPar b)) (acq := true)
        (sc := .cta) with ⟨f, hw⟩ | ⟨m0, q, k, acq', sc', hw⟩
    · exfalso
      have hf : Fires l.site.pc (eventTmpl Prod L g t1 (.mbarWait (Loader.waitPred b)
          (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta)) ⟨l.site.pc, .ub f⟩ none := by
        rw [hw]; exact ⟨rfl, rfl⟩
      obtain ⟨ok, acq0, sc0, he⟩ := Loader.wait_event hpre b hs hat hc hf
      cases he
    · have hf : Fires l.site.pc (eventTmpl Prod L g t1 (.mbarWait (Loader.waitPred b)
          (Loader.waitBase b) 0 (.reg (Loader.waitPar b)) true .cta))
          ⟨l.site.pc, .wait m0 q true acq' sc'⟩ (some (k true)) := by
        rw [hw]; exact ⟨true, rfl, rfl⟩
      obtain ⟨ok, acq0, sc0, he⟩ := Loader.wait_event hpre b hs hat hc hf
      simp only [Event.mk.injEq, Kind.wait.injEq] at he
      obtain ⟨-, rfl, rfl, -, -, -⟩ := he
      obtain ⟨p1, b1, o1, q1, s1, hop, -⟩ := fires_wait_flags hf rfl
      simp only [Op.mbarWait.injEq] at hop
      obtain ⟨-, -, -, -, rfl, -⟩ := hop
      refine ⟨t, t1, k true, sc', hr, hl, ⟨_, hout.trans (by rw [hw]), ?_⟩⟩
      rw [htpc, hs]
      exact ⟨true, rfl, rfl⟩

/-- A loader at a slot's empty wait after its whole trace polls with the parity after its own
successful polls on that barrier. -/
theorem loader_wait_parity {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {l : Loader.D} {b : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .wait b) :
    InputRing.producerParity b % 2 =
      (okPolls (InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b)) (X.tr g) + 1) % 2 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hc : LoaderTasks.Counts L g l (X.tr g) := by
    have h := LoaderTasks.run hpre hg htr (X.tr g).length _ (by rw [List.take_length]; exact hσ)
    rw [List.take_length] at h
    exact h
  obtain ⟨site, m, n, q, cp, r, x⟩ := l
  simp only at hs
  subst hs
  have h1 := hc.parity (by simp [Loader.Site.done]) (InputRing.slotOf b)
  have h2 : InputRing.producerParity b % 2 =
      (Loader.polled ⟨.wait b, m, n, q, cp, r, x⟩ (InputRing.slotOf b) + 1) % 2 := by
    fin_cases b <;> simp [Loader.polled, InputRing.producerParity, InputRing.slotOf]
  simp only [Loader.emptyOf] at h1
  omega

set_option maxHeartbeats 4000000 in
/-- A loader at a slot's empty wait after its whole trace, whose last event is a failed poll,
polled that slot's empty barrier: a failed poll keeps a thread at its wait. -/
theorem loader_last_wait {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {l : Loader.D} {b : Fin 8}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .wait b) {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩) :
    m = InputRing.emptyLoc L (g / L.block) (InputRing.slotOf b) := by
  obtain ⟨pre, hpe⟩ := List.getLast?_eq_some_iff.mp hlast
  set e : Event := ⟨pc, .wait m p false acq sc⟩ with he_def
  rw [hpe] at hσ
  have hsn := Machine.after_snoc (code L g).toMachine (some (code L g).init) pre e
  rw [hsn] at hσ
  cases ha : (code L g).toMachine.after (some (code L g).init) pre with
  | none => rw [ha] at hσ; cases hσ
  | some σ' =>
    rw [ha] at hσ
    change (code L g).toMachine.next σ' e = _ at hσ
    have hj : (X.tr g)[pre.length]? = some e := by rw [hpe]; simp
    have hta : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take pre.length) =
        some σ' := by rw [hpe, List.take_left' rfl]; exact ha
    rcases σ' with _ | d'
    · cases hσ
    obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX hj hta
    rcases d' with p' | (l' | m' | sd | cs)
    · exfalso
      change Prologue.next L g p' e = _ at hσ
      clear hat hc hfire hta hj hsn ha
      unfold Prologue.next at hσ
      repeat' split at hσ
      all_goals first | (cases hσ; done) | simp_all
    · obtain ⟨l'', hn, hl⟩ := next_of_loader hσ
      cases hl
      change kernel.code[l'.site.pc]? = some ins at hc
      change Fires l'.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
      obtain ⟨site, mm, n, q, cp, r, x⟩ := l'
      cases site
      case wait b' =>
        obtain ⟨ok', acq', sc', he'⟩ := Loader.wait_event hpre b' rfl hat hc hfire
        simp only [he_def, Event.mk.injEq, Kind.wait.injEq] at he'
        obtain ⟨-, rfl, -, rfl, -⟩ := he'
        simp only [Loader.next, he_def, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp only [Loader.Site.wait.injEq] at hs
        rw [hs]
      case clcWait =>
        exfalso
        simp only [Loader.next, he_def, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp at hs
      case drain i =>
        exfalso
        simp only [Loader.next, he_def, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp at hs
      all_goals exfalso
      all_goals exact fires_notWait (eventTmpl_notWait (Loader.code_notPoll _ rfl hc)) hfire _ _ _ _
                  _ rfl
    · obtain ⟨_, -, h⟩ := next_of_mma hσ; cases h
    · obtain ⟨_, -, h⟩ := next_of_sched hσ; cases h
    · obtain ⟨_, -, h⟩ := next_of_cons hσ; cases h

end
end PTX.Kernels.Fp16Gemm8192.Proof
