-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputStore
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX
noncomputable section

def readyReg : Fin 2 → Nat
  | 0 => 9748
  | 1 => 9749

private theorem moveWord {l : Launch} {g : Nat} {t : TState} {r n : Nat}
    (hf : t.fault = none)
    (hc : kernel.code[t.pc]? = some
      ⟨none, .move ⟨.scalar, .int .b 32, [some r], [.imm n]⟩⟩)
    (hn : n < 2 ^ 32) :
    tauStep kernel [] l g t = some (next (setReg t r (.bits 32 (BitVec.ofNat 64 n)))) := by
  apply tauLocalShared hf hc rfl
  rw [execLocal_move rfl]
  simp [execMove, readValue, readBits, DType.width, Value.bytes,
    bind, Except.bind, pure, Except.pure, PTX.Proof.truncBits_ofNat hn (by decide)]

private theorem addWord {l : Launch} {g : Nat} {t : TState} {r dst a n : Nat}
    (hf : t.fault = none)
    (hc : kernel.code[t.pc]? = some
      ⟨none, .int ⟨.add, .int .s 32, false, [some dst], [.reg r, .imm n]⟩⟩)
    (hr : t.regs r = some (.bits 32 (BitVec.ofNat 64 a))) (ha : a + n < 2 ^ 32) :
    tauStep kernel [] l g t = some (next (setReg t dst (.bits 32 (BitVec.ofNat 64 (a + n))))) := by
  apply tauLocalShared hf hc rfl
  rw [execLocal_int rfl]
  have hn : n < 2 ^ 32 := by omega
  have ha' : a < 2 ^ 32 := by omega
  simp only [execInt, DType.width, readBits, readValue, readReg, hr, bind, Except.bind,
    pure, Except.pure, BitVec.ofInt_natCast, PTX.Proof.truncBits_ofNat ha' (by decide),
    PTX.Proof.truncBits_ofNat hn (by decide), ← BitVec.ofNat_add,
    PTX.Proof.truncBits_ofNat ha (by decide)]

/-- The warp-13 dispatch target lowers its register allocation before entering the scheduler. -/
theorem entryTemplate (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = Flow.setMaxReg_2) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.setMaxReg false 80 (next t)) := by
  exact outEventShared hf (by rw [hpc]; exact Flow.code_2769) rfl

theorem finishSchedulerWith {A : List Assumption} (l : Launch) (g : Nat) (t : TState)
    (hModel : ∀ {s : TState}, s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205] →
      out kernel A l g s = out kernel [] l g s)
    (hpc : t.pc = 3099) (hf : t.fault = none)
    (hw : t.regs 1062 = some (.bits 32 13)) :
    ∃ u, run kernel A l g 5 t = some u ∧ u.pc = Flow.exit_0 ∧
      out kernel A l g u = .ev .exit :=
  finishSchedulerOfWarpWith l g t hModel hpc hf (.inr rfl) hw

theorem finishScheduler (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = 3099) (hf : t.fault = none)
    (hw : t.regs 1062 = some (.bits 32 13)) :
    ∃ u, run kernel [] l g 5 t = some u ∧ u.pc = Flow.exit_0 ∧
      out kernel [] l g u = .ev .exit :=
  finishSchedulerWith l g t (fun _ => rfl) hpc hf hw

def readyBase : Fin 2 → Nat
  | 0 => 2390
  | 1 => 2391

theorem pollInstr (stage : Fin 2) :
    kernel.code[pollPc stage]? =
      some ⟨none, .mbarWait (readyReg stage) (readyBase stage) 0 (.reg 7229) true .cta⟩ := by
  fin_cases stage
  · exact Flow.code_2958
  · exact Flow.code_2972

/-- Both stages poll their own ready barrier and record the returned predicate. -/
theorem pollTemplate (stage : Fin 2) (l : Launch) (g : Nat) (t : TState) (sl : Loc)
    (hpc : t.pc = pollPc stage) (hf : t.fault = none)
    (hshared : mbarLoc l g t (readyBase stage) 0 = .ok sl)
    (hpar : readBits l g t 32 (.reg 7229) = .ok 0) :
    out kernel [] l g t = .ev (.wait sl 0 (fun ok => next (setReg t (readyReg stage) (.pred ok)))
      true .cta) := by
  have hc := pollInstr stage
  rw [← hpc] at hc
  rw [outEventShared hf hc rfl]
  simp [eventTmpl, widenMbarScope, tmaTmpl, hshared, hpar, bind, Except.bind, pure, Except.pure,
    ofExec]

/-- The warp-13 epilogue polls again on a failed wait and leaves the spin on a successful wait. -/
theorem pollBranches (stage : Fin 2) (ok : Bool) (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = pollPc stage + 1) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hr : t.regs (readyReg stage) = some (.pred ok)) :
    run kernel [] l g (if ok then 1 else 2) t =
      some { t with pc := if ok then pollPc stage + 3 else pollPc stage } := by
  fin_cases stage <;> cases ok <;> simp [pollPc, readyReg] at hpc hr ⊢ <;>
    simp_all only [run, tauStep, out, Flow.code_2959, Flow.code_2960, Flow.code_2973,
      Flow.code_2974, guardHolds, readReg, bind, Except.bind, pure, Except.pure, skip,
      execLocalA, execLocalRule, List.findSome?_nil, execLocal, Op.rule, Op.isLocal, execBranch,
      Bool.bne_false, ↓reduceIte, Option.bind_some, Nat.reduceAdd]

/-- The first ready wait's success target prepares the map operand and the cache hint. -/
theorem prepareStore (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = 2961) (hf : t.fault = none)
    (ho : t.regs 7290 = some (.ptr 64 false (.param (param 10)) 0)) :
    run kernel [] l g 2 t =
      some (next (setReg (next (setReg t 7868 (.ptr 64 true (.param (param 10)) 0)))
        7869 (.bits 64 0))) := by
  let u := next (setReg t 7868 (.ptr 64 true (.param (param 10)) 0))
  have h1 : tauStep kernel [] l g t = some u := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2961) rfl
    rw [execLocal_cvta rfl, execCvta_param]
    simp [u, readValue, readReg, ho, bind, Except.bind, pure, Except.pure]
  have h2 : tauStep kernel [] l g u = some (next (setReg u 7869 (.bits 64 0))) := by
    have hu : u.pc = 2962 := by change t.pc + 1 = 2962; rw [hpc]
    apply tauLocalShared (t := u) hf (by rw [hu]; exact Flow.code_2962) rfl
    rw [execLocal_move rfl]
    rfl
  simp only [run, h1, h2, Option.bind_some, u]

section
variable {p : Params} {l : Launch} {m : Mem0}

/-- With the first group's commit issued, prepare the second ready-barrier operand. -/
theorem prepareSecondPoll (hp : Pre p l m) (g : Nat) (t : TState) (hpc : t.pc = 2971)
    (hf : t.fault = none) (hbase : t.regs 2535 = some (.bits 32 (BitVec.ofNat 64 l.sharedBase))) :
    tauStep kernel [] l g t =
      some (next (setReg t 2391 (.bits 32 (BitVec.ofNat 64 (l.sharedBase + 216))))) := by
  have hm := hp.shared.2.1
  exact addWord (r := 2535) (n := 216) hf (by rw [hpc]; exact Flow.code_2971) hbase (by omega)

/-- Origin obtained by the PTX's sign interpretation of the low 32 bits of four registers. -/
private theorem barrierAddress {l : Launch} {g : Nat} {t : TState} {r a off : Nat}
    (hr : t.regs r = some (.bits 32 (BitVec.ofNat 64 a))) (ha : a + off < 2 ^ 32)
    (hal : (a + off) % 8 = 0) :
    mbarLoc l g t r off = .ok ⟨.shared, g / l.block, a + off⟩ := by
  have hadd := sharedAddress (l := l) (g := g) hr ha
  simp [mbarLoc, effAddr, hadd, hal, bind, Except.bind, pure, Except.pure]

theorem readyPoll (hp : Pre p l m) (g : Nat) (t : TState) (stage : Fin 2)
    (hpc : t.pc = pollPc stage) (hf : t.fault = none)
    (hbar : t.regs (readyBase stage) = some (.bits 32 (BitVec.ofNat 64 (readyLoc l g stage).addr)))
    (hpar : t.regs 7229 = some (.bits 32 0)) :
    out kernel [] l g t = .ev (.wait (readyLoc l g stage) 0
      (fun ok => next (setReg t (readyReg stage) (.pred ok))) true .cta) := by
  have hLimit := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  apply pollTemplate stage l g t _ hpc hf
  · exact barrierAddress (off := 0) hbar (by change l.sharedBase + (208 + 8 * stage.val) < _; omega)
      (by change (l.sharedBase + (208 + 8 * stage.val)) % 8 = 0; omega)
  · simp [readBits, readReg, hpar, bind, Except.bind, pure, Except.pure, truncBits]

/-- The wait event writes only the branch predicate. Its retry is ready to execute the same
wait again, preserving the operand registers and substep state. -/
theorem retryPoll (l : Launch) (g : Nat) (t : TState) (stage : Fin 2)
    (hpc : t.pc = pollPc stage) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = []) :
    run kernel [] l g 2 (next (setReg t (readyReg stage) (.pred false))) =
      some (setReg t (readyReg stage) (.pred false)) := by
  have h := pollBranches stage false l g (next (setReg t (readyReg stage) (.pred false)))
    (by change t.pc + 1 = _; rw [hpc]) hf hs ha (by simp [next, setReg])
  simpa [next, setReg, hpc] using h

/-- The allocator's exit branch bypasses both output groups when it found no assigned tile. -/
theorem selectedBranch (l : Launch) (g : Nat) (t : TState) (found : Bool)
    (hpc : t.pc = 2947) (hf : t.fault = none)
    (hfound : t.regs 782 = some (.pred found)) :
    run kernel [] l g 2 t =
      some (if found then skip (next (setReg t 306 (.pred false)))
        else { next (setReg t 306 (.pred true)) with pc := 3099 }) := by
  let u := next (setReg t 306 (.pred (!found)))
  have h1 : tauStep kernel [] l g t = some u := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2947) rfl
    rw [execLocal_int rfl]
    simp [execInt, DType.width, readPred, readReg, hfound, bind, Except.bind, pure, Except.pure, u]
  have hp : u.pc = 2948 := by change t.pc + 1 = 2948; rw [hpc]
  have hPu : u.regs 306 = some (.pred (!found)) := by simp [u, next, setReg]
  have h2 : tauStep kernel [] l g u =
      some (if found then skip u else { u with pc := 3099 }) := by
    cases found
    · exact branchTrueShared (t := u) hf (by rw [hp]; exact Flow.code_2948) hPu
    · simp [tauStep, out, show u.fault = none from hf, hp, Flow.code_2948, guardHolds,
        readReg, hPu, bind, Except.bind, pure, Except.pure]
  simp only [run, h1, h2, Option.bind_some]
  cases found <;> rfl

private theorem signedReg {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, PTX.Proof.toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The first scheduler segment prepares one cuQ lookup per participating lane. Lanes beyond
the sentinel bypass their load, with a defined zero value for the shuffle. -/
theorem enterSchedulerWith {A : List Assumption} [Prologue.StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hpc : t.pc = 2770) (hf : t.fault = none)
    (hBatchReg : t.regs 7228 = some (.bits 32 (BitVec.ofNat 64 p.batch))) :
    ∃ u, run kernel A l g 4 t = some u ∧ u.fault = none ∧
      u.pc = (if p.batch < laneOf l g then 2777 else 2774) ∧
      u.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))) ∧
      u.regs 7217 = some (.bits 32 0) ∧
      (laneOf l g ≤ p.batch → u.sub = 0 ∧ u.acc = []) ∧
      (t.sub = 0 ∧ t.acc = [] → u.sub = 0 ∧ u.acc = []) ∧
      ∀ r ∉ [1201, 265, 7217], u.regs r = t.regs r := by
  let lane := laneOf l g
  let t1 := next (setReg t 1201 (.bits 32 (BitVec.ofNat 64 lane)))
  let t2 := next (setReg t1 265 (.pred (p.batch < lane)))
  let t3 := next (setReg t2 7217 (.bits 32 0))
  let u := if p.batch < lane then { t3 with pc := 2777 } else skip t3
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hb := hp.shape.2.1
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2770) rfl
    rw [execLocal_move rfl]
    simp [execMove, readValue, readBits, SReg.width, sregValue, DType.width, Value.bytes,
      bind, Except.bind, pure, Except.pure, t1, lane,
      PTX.Proof.truncBits_ofNat (show lane < 2 ^ 32 by omega) (by decide)]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp1 : t1.pc = 2771 := by change t.pc + 1 = 2771; rw [hpc]
    have hl1 : t1.regs 1201 = some (.bits 32 (BitVec.ofNat 64 lane)) := by
      simp [t1, next, setReg]
    have hb1 : t1.regs 7228 = some (.bits 32 (BitVec.ofNat 64 p.batch)) := by
      simpa [t1, next, setReg] using hBatchReg
    apply tauLocalShared (t := t1) hf (by rw [hp1]; exact Flow.code_2771) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hl1, hb1, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat (show lane < 2 ^ 32 by omega) (by decide),
      PTX.Proof.truncBits_ofNat (show p.batch < 2 ^ 32 by omega) (by decide)]
    change Except.ok (next (setReg t1 265 (.pred (decide
      (toSigned 32 (BitVec.ofNat 64 p.batch) < toSigned 32 (BitVec.ofNat 64 lane)))))) = .ok t2
    simp only [signedReg hb, signedReg (show lane < 2 ^ 31 by omega), Int.ofNat_lt, t2]
  have h3 : tauStep kernel [] l g t2 = some t3 := by
    have hp2 : t2.pc = 2772 := by change t.pc + 1 + 1 = 2772; rw [hpc]
    exact moveWord (n := 0) (t := t2) hf (by rw [hp2]; exact Flow.code_2772) (by decide)
  have h4 : tauStep kernel [] l g t3 = some u := by
    have hp3 : t3.pc = 2773 := by change t.pc + 1 + 1 + 1 = 2773; rw [hpc]
    have hp265 : t3.regs 265 = some (.pred (p.batch < lane)) := by
      simp [t3, t2, next, setReg]
    by_cases h : p.batch < lane
    · have hr : t3.regs 265 = some (.pred true) := by simpa [h] using hp265
      simpa [u, h] using branchTrueShared (t := t3) hf (by rw [hp3]; exact Flow.code_2773) hr
    · simp [tauStep, out, show t3.fault = none from hf, hp3, Flow.code_2773, guardHolds,
        readReg, hp265, h, bind, Except.bind, pure, Except.pure, u]
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have lift {s v : TState} {j : Nat} (hj : j < 4) (hs : s.pc = t.pc + j)
        (hr : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      Prologue.startupTau (.inr (.inr (by omega))) hr
    have s1 := lift (j := 0) (by decide) rfl h1
    have s2 := lift (j := 1) (by decide) rfl h2
    have s3 := lift (j := 2) (by decide) rfl h3
    have s4 := lift (j := 3) (by decide) rfl h4
    simp only [run, s1, s2, s3, s4, Option.bind_some]
  · by_cases h : p.batch < lane <;> simp [u, h, skip, t3, t2, t1, next, setReg, hf]
  · by_cases h : p.batch < lane <;> simp [u, h, lane, skip, t3, t2, t1, next, setReg, hpc]
  · by_cases h : p.batch < lane <;> simp [u, h, skip, t3, t2, t1, next, setReg, lane]
  · by_cases h : p.batch < lane <;> simp [u, h, skip, t3, next, setReg]
  · intro h
    have hn : ¬ p.batch < lane := Nat.not_lt.mpr h
    simp [u, hn, skip]
  · intro hClean
    by_cases h : p.batch < lane <;> simp [u, h, t3, t2, t1, next, setReg, skip, hClean]
  · intro r hr
    have hne (n : Nat) (hn : n ∈ [1201, 265, 7217]) : r ≠ n := by
      rintro rfl
      exact hr hn
    by_cases h : p.batch < lane <;> simp [u, h, skip, t3, t2, t1, next, setReg,
      hne 1201 (by decide), hne 265 (by decide), hne 7217 (by decide)]

theorem enterScheduler (hp : Pre p l m) (g : Nat) (t : TState) (hpc : t.pc = 2770)
    (hf : t.fault = none) (hBatchReg : t.regs 7228 = some (.bits 32 (BitVec.ofNat 64 p.batch))) :
    ∃ u, run kernel [] l g 4 t = some u ∧ u.fault = none ∧
      u.pc = (if p.batch < laneOf l g then 2777 else 2774) ∧
      u.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))) ∧
      u.regs 7217 = some (.bits 32 0) ∧
      (laneOf l g ≤ p.batch → u.sub = 0 ∧ u.acc = []) ∧
      ∀ r ∉ [1201, 265, 7217], u.regs r = t.regs r := by
  obtain ⟨u, hr, hFault, hpcU, hLane, hZero, hPart, _, hFrame⟩ :=
    enterSchedulerWith (A := []) hp g t hpc hf hBatchReg
  exact ⟨u, hr, hFault, hpcU, hLane, hZero, hPart, hFrame⟩

/-- Prepare the lane’s first lookup while keeping all registers except the address words. -/
theorem schedulerLaneReadWithFrame {A : List Assumption} [Prologue.StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hLane : laneOf l g ≤ p.batch)
    (hpc : t.pc = 2774) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hIndex : t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))))
    (hBase : t.regs 7506 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase))) :
    ∃ u, run kernel A l g 2 t = some u ∧ u.pc = 2776 ∧ u.fault = none ∧
      u.sub = 0 ∧ u.acc = [] ∧
      out kernel A l g u = .ev (.read
        { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 } (afterLoad u [7217])) ∧
      ∀ r ∉ [7862,7863], u.regs r = t.regs r := by
  let lane := laneOf l g
  let t1 := next (setReg t 7862 (.bits 64 (BitVec.ofNat 64 (4 * lane))))
  let t2 := next (setReg t1 7863 (.bits 64 (BitVec.ofNat 64 (p.cuQBase + 4 * lane))))
  have hLaneLt : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane32 : lane < 2 ^ 32 := by omega
  have hLane64 : lane < 2 ^ 64 := by omega
  have hOff64 : 4 * lane < 2 ^ 64 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hBase64 : p.cuQBase < 2 ^ 64 := by omega
  have hSum : p.cuQBase + 4 * lane < 2 ^ 64 := by change lane ≤ p.batch at hLane; omega
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2774) rfl
    rw [execLocal_int rfl]
    change t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 lane)) at hIndex
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hIndex, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hLane32 (by decide)]
    change Except.ok (next (setReg t 7862 (.bits 64
      (BitVec.ofNat 64 ((BitVec.ofNat 64 lane).toNat * 4))))) = .ok t1
    rw [PTX.Proof.toNat_ofNat_lt hLane64, Nat.mul_comm lane 4]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp1 : t1.pc = 2775 := by change t.pc + 1 = 2775; rw [hpc]
    have hB : t1.regs 7506 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase)) := by
      simpa [t1, next, setReg] using hBase
    have hOff : t1.regs 7862 = some (.bits 64 (BitVec.ofNat 64 (4 * lane))) := by
      simp [t1, next, setReg]
    apply tauLocalShared (t := t1) hf (by rw [hp1]; exact Flow.code_2775) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readBits, readReg, hB, hOff, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hBase64 (by decide),
      PTX.Proof.truncBits_ofNat hOff64 (by decide), ← BitVec.ofNat_add,
      PTX.Proof.truncBits_ofNat hSum (by decide), t2]
  have hp2 : t2.pc = 2776 := by change t.pc + 1 + 1 = 2776; rw [hpc]
  refine ⟨t2, ?_, hp2, hf, hs, ha, ?_, ?_⟩
  · have lift {s v : TState} {j : Nat} (hj : j < 2) (hs : s.pc = t.pc + j)
        (hr : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      Prologue.startupTau (.inr (.inr (by omega))) hr
    have s1 := lift (j := 0) (by decide) rfl h1
    have s2 := lift (j := 1) (by decide) rfl h2
    simp only [run, s1, s2, Option.bind_some]
  · apply Prologue.startupOut (.inr (.inr (by rw [hp2]; decide)))
    have hR : t2.regs 7863 = some (PTX.Proof.b64 (p.cuQBase + 4 * lane)) := by
      simp [t2, next, setReg, PTX.Proof.b64]
    have hAl := hp.alignment.2.2.2.2.2.2.2.2.1
    rw [outEventShared (t := t2) hf (by rw [hp2]; exact Flow.code_2776) rfl]
    change Out.ev (loadTmpl [] l g t2 .global false 32 [7217] 7863 0) = _
    exact congrArg Out.ev (PTX.Proof.loadTmpl_global (t := t2) (w := 32)
      hs hR hSum (by decide) (by omega))

  · intro r hr
    have h0 : r ≠ 7862 := fun h => hr (by simp [h])
    have h1 : r ≠ 7863 := fun h => hr (by simp [h])
    simp [t2,t1,next,setReg,Function.update_of_ne,h0,h1]

theorem schedulerLaneReadWith {A : List Assumption} [Prologue.StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (t : TState) (hLane : laneOf l g ≤ p.batch)
    (hpc : t.pc = 2774) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hIndex : t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))))
    (hBase : t.regs 7506 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase))) :
    ∃ u, run kernel A l g 2 t = some u ∧ u.pc = 2776 ∧ u.fault = none ∧
      u.sub = 0 ∧ u.acc = [] ∧
      out kernel A l g u = .ev (.read
        { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 } (afterLoad u [7217])) := by
  obtain ⟨u, hr, hpc, hf, hs, ha, hout, _⟩ :=
    schedulerLaneReadWithFrame (A := A) hp g t hLane hpc hf hs ha hIndex hBase
  exact ⟨u,hr,hpc,hf,hs,ha,hout⟩

theorem schedulerLaneRead (hp : Pre p l m) (g : Nat) (t : TState) (hLane : laneOf l g ≤ p.batch)
    (hpc : t.pc = 2774) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hIndex : t.regs 1201 = some (.bits 32 (BitVec.ofNat 64 (laneOf l g))))
    (hBase : t.regs 7506 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase))) :
    ∃ u, run kernel [] l g 2 t = some u ∧ u.pc = 2776 ∧ u.fault = none ∧
      u.sub = 0 ∧ u.acc = [] ∧
      out kernel [] l g u = .ev (.read
        { loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4 } (afterLoad u [7217])) :=
  schedulerLaneReadWith hp g t hLane hpc hf hs ha hIndex hBase

theorem schedulerFirstShuffle (hp : Pre p l m) (g : Nat) (t : TState) (cuq : Nat)
    (hpc : t.pc = 2777) (hf : t.fault = none)
    (hv : t.regs 7217 = some (.bits 32 (BitVec.ofNat 64 cuq))) :
    out kernel [] l g t = .ev (.shfl .down (.bits 32 (BitVec.ofNat 64 cuq)) 1 31
      (fun value _ => next (setReg t 2308 value))) := by
  rw [outEventShared hf (by rw [hpc]; exact Flow.code_2777) rfl]
  change Out.ev (shflTmpl l g t .down 2308 none (.reg 7217) (.imm 1) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, hv, hBlock, Value.bytes, readBits, pure, Except.pure]
  rfl

/-- For the initialized cuQ bytes, the scalar read's continuation reaches the same shuffle
as the lanes outside the batch. -/
theorem schedulerAfterLaneRead (hp : Pre p l m) (g : Nat) (t : TState) (hpc : t.pc = 2776)
    (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = []) :
    let q := p.qOffset (laneOf l g)
    let v := Value.bits 32 (BitVec.ofNat 64 q)
    let u := afterLoad t [7217] (v.toBytes.map some)
    out kernel [] l g u = .ev
      (.shfl .down v 1 31 (fun value _ => next (setReg u 2308 value))) := by
  dsimp only
  have hRead := PTX.Proof.rebuild_scalar
    (v := .bits 32 (BitVec.ofNat 64 (p.qOffset (laneOf l g)))) (show 0 < 4 by decide) rfl
  rw [PTX.Proof.afterLoad_ok hs ha hRead]
  apply schedulerFirstShuffle hp
  · change t.pc + 1 = 2777
    rw [hpc]
  · exact hf
  · simp [setReg]

/-- The selected signed 32-bit batch index scales by four without wrapping and is added to
the loaded cuQ pointer. Both operations preserve the registers holding the selected tile. -/
theorem prepareCuQAddress (hp : Pre p l m) (g : Nat) (t : TState) {batch : Nat}
    (hb : batch < p.batch) (hpc : t.pc = 2951) (hf : t.fault = none)
    (hIndex : t.regs 7228 = some (.bits 32 (BitVec.ofNat 64 batch)))
    (hBase : t.regs 7502 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase))) :
    run kernel [] l g 2 t =
      some (next (setReg (next (setReg t 7866 (.bits 64 (BitVec.ofNat 64 (4 * batch)))))
        7867 (.bits 64 (BitVec.ofNat 64 (p.cuQBase + 4 * batch))))) := by
  let t1 := next (setReg t 7866 (.bits 64 (BitVec.ofNat 64 (4 * batch))))
  let t2 := next (setReg t1 7867 (.bits 64 (BitVec.ofNat 64 (p.cuQBase + 4 * batch))))
  have hBatch := hp.shape.2.1
  have hb31 : batch < 2 ^ 31 := lt_trans hb hBatch
  have hb32 : batch < 2 ^ 32 := by omega
  have hb64 : 4 * batch < 2 ^ 64 := by omega
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
  have hBase64 : p.cuQBase < 2 ^ 64 := by omega
  have hSum : p.cuQBase + 4 * batch < 2 ^ 64 := by omega
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2951) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, DType.kind?, readBits, readReg, hIndex, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hb32 (by decide)]
    change Except.ok (next (setReg t 7866
      (.bits 64 (truncBits 64 (BitVec.ofInt 64 (toSigned 32 (BitVec.ofNat 64 batch) * 4)))))) =
      .ok t1
    have hm : (batch : Int) * 4 = ((4 * batch : Nat) : Int) := by push_cast; omega
    rw [signedReg hb31, hm, BitVec.ofInt_natCast,
      PTX.Proof.truncBits_ofNat hb64 (by decide)]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp1 : t1.pc = 2952 := by change t.pc + 1 = 2952; rw [hpc]
    have hB : t1.regs 7502 = some (.bits 64 (BitVec.ofNat 64 p.cuQBase)) := by
      simpa [t1, next, setReg] using hBase
    have hOff : t1.regs 7866 = some (.bits 64 (BitVec.ofNat 64 (4 * batch))) := by
      simp [t1, next, setReg]
    apply tauLocalShared (t := t1) hf (by rw [hp1]; exact Flow.code_2952) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readBits, readReg, hB, hOff, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hBase64 (by decide),
      PTX.Proof.truncBits_ofNat hb64 (by decide), ← BitVec.ofNat_add,
      PTX.Proof.truncBits_ofNat hSum (by decide), t2]
  simp only [run, h1, h2, Option.bind_some, t2, t1]

private def cuQInstr (endpoint : Fin 2) : MemAccess := {
  kind := .load
  space := some .global
  sem := .weak
  elem := .int .b 32
  addr := ⟨.reg 7867 64, (4 * endpoint.val : Nat)⟩
  dsts := [some (2392 + endpoint.val)]
}

/-- The selected batch reads its two adjacent prefix offsets from the cuQ array. -/
theorem cuQTemplate (hp : Pre p l m) (g : Nat) (t : TState) {batch : Nat} (hb : batch < p.batch)
    (endpoint : Fin 2) (hpc : t.pc = 2953 + endpoint.val) (hf : t.fault = none) (hs : t.sub = 0)
    (hbase : t.regs 7867 = some (.bits 64 (BitVec.ofNat 64 (p.cuQBase + 4 * batch)))) :
    out kernel [] l g t = .ev (.read
      { loc := globalLoc (p.cuQBase + 4 * (batch + endpoint.val)), size := 4 }
      (afterLoad t [2392 + endpoint.val])) := by
  have hc : kernel.code[2953 + endpoint.val]? = some ⟨none, .mem (cuQInstr endpoint)⟩ := by
    fin_cases endpoint
    · exact Flow.code_2953
    · exact Flow.code_2954
  rw [← hpc] at hc
  rw [outEventShared hf hc rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [2392 + endpoint.val] 7867 _) = _
  have ha := hp.alignment.2.2.2.2.2.2.2.2.1
  have hRegion := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  have hBound : p.cuQBase + 4 * (batch + endpoint.val) < 2 ^ 64 := by
    have := endpoint.isLt
    change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRegion
    omega
  have hStart : p.cuQBase + 4 * batch < 2 ^ 64 := by omega
  have hEff : effAddr l g t .global 7867 (4 * endpoint.val : Nat) =
      .ok (globalLoc (p.cuQBase + 4 * (batch + endpoint.val))) := by
    simp only [effAddr, readBits, readReg, hbase, bind, Except.bind, pure, Except.pure,
      PTX.Proof.truncBits_ofNat hStart (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      PTX.Proof.toNat_ofNat_lt (show p.cuQBase + 4 * batch + 4 * endpoint.val < 2 ^ 64 by omega)]
    unfold globalLoc
    congr 2
    omega
  have hAl : (globalLoc (p.cuQBase + 4 * (batch + endpoint.val))).addr % (4 * 1) = 0 := by
    change (p.cuQBase + 4 * (batch + endpoint.val)) % 4 = 0
    omega
  simp only [cuQInstr, loadTmpl, hEff, bind, Except.bind, List.length_singleton, hs]
  rw [PTX.Proof.elemAcc_ok (by decide) hAl]
  rfl

/-- Use the selected batch's two offsets to encode the ragged row coordinate and poll parity. -/
theorem prepareFirstRow (hp : Pre p l m) (g : Nat) (t : TState) {batch tile : Nat}
    (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch) (hpc : t.pc = 2955)
    (hf : t.fault = none)
    (hx : t.regs 7226 = some (.bits 32 (BitVec.ofNat 64 (2 ^ 30 + 256 * tile))))
    (hbreg : t.regs 2392 = some (.bits 32 (BitVec.ofNat 64 (p.qOffset batch))))
    (hereg : t.regs 2393 = some (.bits 32 (BitVec.ofNat 64 (p.qOffset (batch + 1))))) :
    run kernel [] l g 3 t =
      some (next (setReg (next (setReg
        (next (setReg t 2394 (.bits 32 (BitVec.ofNat 64 (2 ^ 30 + 256 * tile + p.qOffset batch)))))
        2395 (.bits 32 (BitVec.ofNat 64 (2 ^ 30 - p.qLength batch + 256 * tile)))))
        7229 (.bits 32 0))) := by
  let a := 2 ^ 30 + 256 * tile
  let b := p.qOffset batch
  let e := p.qOffset (batch + 1)
  let r := 2 ^ 30 - p.qLength batch + 256 * tile
  let t1 := next (setReg t 2394 (.bits 32 (BitVec.ofNat 64 (a + b))))
  let t2 := next (setReg t1 2395 (.bits 32 (BitVec.ofNat 64 r)))
  let t3 := next (setReg t2 7229 (.bits 32 0))
  have hLength : p.qLength batch = e - b := rfl
  have hEnd : e ≤ p.totalQ := hp.qOffset_le_total (by omega)
  have hMono : b ≤ e := (hp.lengths batch hb).1
  have hTotal := hp.shape.2.2.2.2.2
  have hLimit : a + b < 2 ^ 32 := by dsimp only [a]; omega
  have hA : a < 2 ^ 32 := by omega
  have hB : b < 2 ^ 32 := by omega
  have hE : e < 2 ^ 32 := by omega
  have hSub : a + b - e = r := by dsimp only [a, r]; omega
  have hR : r < 2 ^ 32 := by omega
  have hUnder : e ≤ a + b := by dsimp only [a]; omega
  have h1 : tauStep kernel [] l g t = some t1 := by
    apply tauLocalShared hf (by rw [hpc]; exact Flow.code_2955) rfl
    rw [execLocal_int rfl]
    change t.regs 7226 = some (.bits 32 (BitVec.ofNat 64 a)) at hx
    change t.regs 2392 = some (.bits 32 (BitVec.ofNat 64 b)) at hbreg
    simp only [execInt, DType.width, readValue, readBits, readReg, hx, hbreg, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hA (by decide),
      PTX.Proof.truncBits_ofNat hB (by decide), ← BitVec.ofNat_add,
      PTX.Proof.truncBits_ofNat hLimit (by decide), t1]
  have h2 : tauStep kernel [] l g t1 = some t2 := by
    have hp1 : t1.pc = 2956 := by change t.pc + 1 = 2956; rw [hpc]
    have hm : t1.regs 2394 = some (.bits 32 (BitVec.ofNat 64 (a + b))) := by
      simp [t1, next, setReg]
    have he : t1.regs 2393 = some (.bits 32 (BitVec.ofNat 64 e)) := by
      simpa [t1, next, setReg] using hereg
    apply tauLocalShared (t := t1) hf (by rw [hp1]; exact Flow.code_2956) rfl
    rw [execLocal_int rfl]
    simp only [execInt, DType.width, readValue, readBits, readReg, hm, he, bind, Except.bind,
      pure, Except.pure, PTX.Proof.truncBits_ofNat hLimit (by decide),
      PTX.Proof.truncBits_ofNat hE (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show e < 2 ^ 64 by omega) hUnder, hSub,
      PTX.Proof.truncBits_ofNat hR (by decide), t2]
  have h3 : tauStep kernel [] l g t2 = some t3 := by
    have hp2 : t2.pc = 2957 := by change t.pc + 1 + 1 = 2957; rw [hpc]
    exact moveWord (n := 0) (t := t2) hf (by rw [hp2]; exact Flow.code_2957) (by decide)
  simp only [run, h1, h2, h3, Option.bind_some, t3, t2, t1, a, b, r]

theorem prepareSecondRow (hp : Pre p l m) (g : Nat) (t : TState) {batch tile : Nat}
    (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch) (hpc : t.pc = 2975)
    (hf : t.fault = none)
    (hrow : t.regs 2395 = some (.bits 32 (BitVec.ofNat 64 (2 ^ 30 - p.qLength batch + 256 * tile))))
    :
    tauStep kernel [] l g t = some (next (setReg t 2399
      (.bits 32 (BitVec.ofNat 64 (2 ^ 30 - p.qLength batch + stageRow tile 1))))) := by
  have hq := hp.qLength_fits hb
  have hs : 2 ^ 30 - p.qLength batch + 256 * tile + 128 < 2 ^ 32 := by omega
  exact addWord (r := 2395) (n := 128) hf (by rw [hpc]; exact Flow.code_2975) hrow hs

theorem prepareColumn (subbox : Fin 3) (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = 2964 + 2 * subbox.val) (hf : t.fault = none) :
    tauStep kernel [] l g t =
      some (next (setReg t (columnReg subbox.succ)
        (.bits 32 (BitVec.ofNat 64 (32 * subbox.succ.val))))) := by
  apply moveWord hf _ (by have := subbox.isLt; omega)
  rw [hpc]
  fin_cases subbox
  · exact Flow.code_2964
  · exact Flow.code_2966
  · exact Flow.code_2968

theorem prepareReleaseCount (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = 2982) (hf : t.fault = none) :
    tauStep kernel [] l g t = some (next (setReg t 2400 (.bits 32 1))) := by
  exact moveWord (n := 1) hf (by rw [hpc]; exact Flow.code_2982) (by decide)

end

def commitPc : Fin 2 → Nat
  | 0 => 2970
  | 1 => 2980

theorem commitTemplate (stage : Fin 2) (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = commitPc stage) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.bulkCommit (next t)) := by
  have hCode : kernel.code[commitPc stage]? = some ⟨none, .bulkCommit⟩ := by
    fin_cases stage
    · exact Flow.code_2970
    · exact Flow.code_2980
  rw [← hpc] at hCode
  exact outEventShared hf hCode rfl

def readWaitPc : Fin 2 → Nat
  | 0 => 2981
  | 1 => 2984

theorem readWaitTemplate (stage : Fin 2) (l : Launch) (g : Nat) (t : TState)
    (hpc : t.pc = readWaitPc stage) (hf : t.fault = none) :
    out kernel [] l g t = .ev (.bulkWait .read (1 - stage.val) (next t)) := by
  have hCode : kernel.code[readWaitPc stage]? = some ⟨none, .bulkWait .read (1 - stage.val)⟩ := by
    fin_cases stage
    · exact Flow.code_2981
    · exact Flow.code_2984
  rw [← hpc] at hCode
  exact outEventShared hf hCode rfl

def freeBase : Fin 2 → Nat
  | 0 => 6497
  | 1 => 2535

def freeOffset : Fin 2 → Int
  | 0 => 0
  | 1 => 232

/-- Each bulk read wait is followed by a release arrival that frees the corresponding stage. -/
theorem freeTemplate (stage : Fin 2) (l : Launch) (g : Nat) (t : TState) (sl : Loc)
    (hpc : t.pc = freePc stage) (hf : t.fault = none)
    (hshared : mbarLoc l g t (freeBase stage) (freeOffset stage) = .ok sl)
    (hcount : readBits l g t 32 (.reg 2400) = .ok 1) :
    out kernel [] l g t =
      .ev (.arrive sl 0 (next (mbarStateDest t (some (7870 + stage.val)))) 1 true .cta) := by
  have hCode : kernel.code[freePc stage]? = some
      ⟨none, .mbarArrive (freeBase stage) (freeOffset stage) (.imm 0) (.reg 2400) false true .cta
        (some (7870 + stage.val))⟩ := by
    fin_cases stage
    · exact Flow.code_2983
    · exact Flow.code_2985
  rw [← hpc] at hCode
  rw [outEventShared hf hCode rfl]
  have hz : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp [eventTmpl, widenMbarScope, tmaTmpl, hshared, hz, hcount, bind, Except.bind,
    pure, Except.pure, ofExec]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
