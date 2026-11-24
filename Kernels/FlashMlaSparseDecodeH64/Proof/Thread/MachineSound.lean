-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Dispatch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.LaunchTest
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Return

@[expose] public section

/-!
# Soundness of the composed FlashMLA thread machine

The prologue hands each thread to its warpgroup through `setmaxnreg`. The warpgroup-1 broadcast
dispatches by warp, and each role's final local segment reaches the shared return instruction.
The composition uses each role's entry proof and the per-site step proofs.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ## The facts the hand-offs ask for -/

/-- The `Wg1Index` entry run: the role's local prefix from its entry state reaches its first
site. `Wg1Index.lean` states it from `Wg1Index.Entry` and `Wg1Index.LaunchTest` and does not
prove it. -/
def Wg1IndexEntryRun (P : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ t : TState, Wg1Index.Entry P L g t → Wg1Index.LaunchTest P L g →
    ∃ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t' ∧
      (Wg1Index.code P L g).AtD (Wg1Index.init P L g) t'

/-- The index role's entry run follows from its own `start`. -/
theorem wg1IndexEntryRun_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} : Wg1IndexEntryRun P L g := by
  intro t he hlt
  exact Wg1Index.start P L g mem0 t hpre he hlt

/-- The index role's launch test follows from the preconditions. -/
theorem wg1IndexLaunchTest_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (hg : g < L.threads) : Wg1Index.LaunchTest P L g :=
  Interface.launchTest_of_pre hpre hg

/-! ## Reading the prologue's facts -/

/-- The prologue's table value of a live register is a fact at the program counter. -/
theorem pro_mem {L : Launch} {g pc r : Nat} (h : r ∈ liveAll pc) :
    (r, valueOf L g r) ∈ factsAt L g pc :=
  mem_factsFrom h

/-- The MMA role's table and the prologue's agree on the registers live at the head's broadcast
(pc 1843): both value the prologue's launch reads and the two parameter-space addresses. -/
theorem mma_valueOf_eq {L : Launch} {g : Nat} {r : Nat} (hr : r ∈ Flow.live 1843) :
    Wg1Mma.valueOf P L g Wg1Mma.init r = valueOf L g r := by
  rw [show Flow.live 1843 = [459, 460, 461, 464, 466, 2990, 2991] from by decide +kernel] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Wg1Mma.valueOf, Wg1Mma.values, Wg1Mma.init, valueOf, values, PTX.Flow.lookupLit,
      Option.getD_some, Wg1Mma.queryOf_eq_ctaidX, Wg1Mma.batchOf_eq_ctaidY]

/-! ## The events of the hand-offs and of the roles' ends -/

/-- A `setmaxnreg` event continues at the next instruction. -/
theorem fires_setMaxReg_next {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {pc : Nat} {e : Event} {inc : Bool} {n : Nat}
    (hf : Fires pc (eventTmpl A L g t (.setMaxReg inc n)) e (some u)) :
    u = PTX.next t := by
  simp only [eventTmpl, SetMaxNReg.tmpl] at hf
  split at hf
  · obtain ⟨-, -, hu⟩ := hf
    exact Option.some.inj hu
  · obtain ⟨-, hu⟩ := hf
    exact absurd hu (by simp)

/-- An unguarded uniform branch is one local step to its target. -/
theorem tau_bra {L : Launch} {g : Nat} {t : TState} {pc target : Nat}
    (hpc : t.pc = pc) (hflt : t.fault = none)
    (hc : kernel.code[pc]? = some ⟨none, .bra target true⟩)
    (hL : ∀ a ∈ Assumptions.all, a.localRule L g t (.bra target true) = none)
    (hA : Assumption.SegFreePc Assumptions.all pc) :
    Tau kernel Assumptions.all L g t { t with pc := target } := by
  have hseg : execLocalA Assumptions.all L g t (.bra target true) =
      execLocalRule Assumptions.all L g t (.bra target true) := hA.exec hpc
  simp only [Tau, out, hflt, hpc, hc, guardHolds, hseg, execLocalRule_of_none hL, execLocal,
    Op.rule, execBranch, Op.isLocal, pure, Except.pure, ↓reduceIte]

/-- The `ret` has no continuing event: its event never reaches a concrete state of `done`. -/
theorem good_done_of_ret {L : Launch} {g : Nat} {t u : TState} {e : Event} {ins : Instr}
    {pc : Nat} (hpc : pc = 3611) (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e (some u)) :
    (code P L g).Good (some .done) u := by
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  simp only [eventTmpl, Fires] at hf
  exact absurd hf.2 (by simp)

/-- A thread at an unguarded branch to the `ret` reaches `done`. -/
theorem good_done_of_bra {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    (hpc : t.pc = pc) (hflt : t.fault = none) (hsub : t.sub = 0) (hacc : t.acc = [])
    (hc : kernel.code[pc]? = some ⟨none, .bra 3611 true⟩)
    (hL : ∀ a ∈ Assumptions.all, a.localRule L g t (.bra 3611 true) = none)
    (hA : Assumption.SegFreePc Assumptions.all pc) :
    ∃ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t' ∧
      (code P L g).Good (some .done) t' :=
  ⟨{ t with pc := 3611 }, .single (tau_bra hpc hflt hc hL hA),
    ⟨⟨rfl, hsub, hacc, hflt, trivial⟩, trivial⟩⟩

/-- A thread at the `ret`'s program counter is `done`. -/
theorem good_done_here {L : Launch} {g : Nat} {t : TState}
    (hpc : t.pc = 3611) (hflt : t.fault = none) (hsub : t.sub = 0) (hacc : t.acc = []) :
    (code P L g).Good (some .done) t :=
  ⟨⟨hpc, hsub, hacc, hflt, trivial⟩, trivial⟩

/-! ## The role entries from the prologue's hand-offs -/

variable {P : Params} {L : Launch}

/-- Warpgroup 0's entry state is `Wg0.Entry`: the prologue's launch reads and
the CTA's place in the grid. Its state is at pc 104 with the prologue's hand-off facts at
pc 103 (the `setmaxnreg` event leaves the registers unchanged). -/
theorem wg0Entry_of_handoff {mem0 : Mem0} {g : Nat} {t : TState} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hat : At t 104 (factsAt L g 103)) (hwg : wgOf L g = 0) :
    Wg0.Entry P L g t := by
  refine ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, ?_, hwg, hg, ?_, ?_⟩
  · refine holds_of_pointwise fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
    · exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
  · rw [← Wg1Mma.batchOf_eq_ctaidY]
    exact Wg1Mma.batchOf_lt hpre hg
  · rw [← Wg1Mma.queryOf_eq_ctaidX]
    exact Wg1Mma.queryOf_lt hpre hg

/-- Warpgroup 2's entry state is `Wg2.Entry`: the prologue's launch reads and
the CTA's place in the grid. Its state is at pc 2607 with the prologue's hand-off facts at
pc 2606. -/
theorem wg2Entry_of_handoff {mem0 : Mem0} {g : Nat} {t : TState} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hat : At t 2607 (factsAt L g 2606)) :
    Wg2.Entry P L g t := by
  refine ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, ?_, ?_, ?_⟩
  · refine holds_of_pointwise fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact holds_mem hat.2.2.2.2 (pro_mem (by decide +kernel))
  · rw [← Wg1Mma.batchOf_eq_ctaidY]
    exact Wg1Mma.batchOf_lt hpre hg
  · rw [← Wg1Mma.queryOf_eq_ctaidX]
    exact Wg1Mma.queryOf_lt hpre hg

/-- Warpgroup 1's hand-off state is the head state at the broadcast (pc 1843): the prologue's
live registers at pc 1842, valued by the MMA role's table, which values them identically. -/
theorem at_head_of_handoff {g : Nat} {t : TState} (hat : At t 1843 (factsAt L g 1842)) :
    At t 1843 (Wg1Mma.facts P L g Wg1Mma.init) := by
  obtain ⟨hpc, hsub, hacc, hflt, hregs⟩ := hat
  refine ⟨hpc, hsub, hacc, hflt, ?_⟩
  show Holds t.regs (factsFrom (Flow.live 1843) (Wg1Mma.valueOf P L g Wg1Mma.init))
  refine holds_of_pointwise fun r hr => ?_
  rw [mma_valueOf_eq hr]
  have hlive : Flow.live 1843 = [459, 460, 461, 464, 466, 2990, 2991] := by decide +kernel
  have hmem : r ∈ liveAll 1842 := by
    rw [hlive] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [show liveAll 1842 = [459, 460, 461, 464, 466, 2990, 2991, 459, 460, 461, 462, 463,
        464, 465, 466] from by decide +kernel]; simp)
  exact holds_mem hregs (mem_factsFrom hmem)

/-- After the broadcast of the thread's own warp index with its validity bit, the thread is at
pc 1844 with the head's facts: the broadcast value and the validity bit, and the warp index. -/
theorem at_after_headFacts {g : Nat} {t : TState} {recv : Value} {ok : Bool}
    (hat : At t 1843 (Wg1Mma.facts P L g Wg1Mma.init)) (hrecv : recv = b32 (warpOf L g))
    (hok : ok = true) :
    At (PTX.next (setReg (setReg t 558 recv) 10 (.pred ok))) 1844
      (Wg1Mma.headFacts L g (warpOf L g)) := by
  obtain ⟨hpc, hsub, hacc, hflt, h7⟩ := Wg1Mma.at_after_head P L g hat hrecv
  obtain ⟨h459, h460, h461, h466, h558, h2990, h2991, -⟩ := h7
  have h464t : t.regs 464 = some (b32 (warpOf L g)) := by
    have hmem : (464 : Nat) ∈ Flow.live 1843 := by
      rw [show Flow.live 1843 = [459, 460, 461, 464, 466, 2990, 2991] from by decide +kernel]
      simp
    have := holds_mem hat.2.2.2.2 (mem_factsFrom hmem)
    simpa [Wg1Mma.valueOf, Wg1Mma.values, Wg1Mma.init, PTX.Flow.lookupLit, Option.getD_some]
      using this
  refine ⟨hpc, hsub, hacc, hflt, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simpa [PTX.next, setReg] using h459
  · simpa [PTX.next, setReg] using h460
  · simpa [PTX.next, setReg] using h461
  · simpa [PTX.next, setReg] using h464t
  · simpa [PTX.next, setReg] using h466
  · simpa [PTX.next, setReg] using h2990
  · simpa [PTX.next, setReg] using h2991
  · simpa [PTX.next, setReg] using h558
  · simp [PTX.next, setReg, hok]

/-! ## The composed successor equations

Each equation is the composed `next` at one state, from the successor its own machine names. A
role's `next` is reached through its code projection, so the equations restate the successor in
the function form the composed `next` matches. -/

theorem next_prologue_some {L : Launch} {g : Nat} {s s' : PSite} {e : Event}
    (hn : (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g).next s e =
      some (some s')) :
    (code P L g).next (.prologue s) e = some (some (.prologue s')) := by
  have h : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e = some (some s') := hn
  simp only [code, next, h]

theorem next_prologue_stop {L : Launch} {g : Nat} {s : PSite} {e : Event}
    (hn : (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g).next s e = some none)
    (h : ∀ wg : Fin 3, s ≠ .handoff wg) :
    (code P L g).next (.prologue s) e = some none := by
  have hn' : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e = some none := hn
  cases s with
  | handoff wg => exact absurd rfl (h wg)
  | _ => simp only [code, next, hn']

theorem next_prologue_dead {L : Launch} {g : Nat} {s : PSite} {e : Event}
    (hn : (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g).next s e = none) :
    (code P L g).next (.prologue s) e = none := by
  have h : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e = none := hn
  simp only [code, next, h]

theorem next_prologue_handoff_true {L : Launch} {g : Nat} {wg : Fin 3} {e : Event}
    (hn : (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g).next (.handoff wg) e =
      some none) (hwg : wgOf L g = wg.val) :
    (code P L g).next (.prologue (.handoff wg)) e = some (some (roleStart P L g wg)) := by
  have h : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g (.handoff wg) e = some none :=
    hn
  simp only [code, next, h, ite_eq_left hwg]

theorem next_prologue_handoff_false {L : Launch} {g : Nat} {wg : Fin 3} {e : Event}
    (hn : (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g).next (.handoff wg) e =
      some none) (hwg : ¬ wgOf L g = wg.val) :
    (code P L g).next (.prologue (.handoff wg)) e = some none := by
  have h : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g (.handoff wg) e = some none :=
    hn
  simp only [code, next, h, ite_eq_right hwg]

theorem next_head_shfl {L : Launch} {g : Nat} {pc : Nat} {m : ShflMode} {a : Value}
    {b c : Nat} {recv : Value} {ok : Bool} (hrecv : recv = b32 (warpOf L g)) (hok : ok = true) :
    (code P L g).next .head ⟨pc, .shfl m a b c recv ok⟩ =
      some (match headStart P L g with
        | some d => some d
        | none => none) := by
  simp only [code, next]
  rw [ite_eq_left ⟨hrecv, hok⟩]
  rfl

theorem next_head_other {L : Launch} {g : Nat} {pc : Nat} {m : ShflMode} {a : Value}
    {b c : Nat} {recv : Value} {ok : Bool} (h : ¬ (recv = b32 (warpOf L g) ∧ ok)) :
    (code P L g).next .head ⟨pc, .shfl m a b c recv ok⟩ = some none := by
  simp only [code, next]
  rw [ite_eq_right h]

theorem headStart_eq4 {L : Launch} {g : Nat} (hw : warpOf L g = 4) :
    headStart P L g = some (.mma ⟨.elect, 0⟩) := by
  simp only [headStart]
  rw [ite_eq_left hw]

theorem headStart_eq5 {L : Launch} {g : Nat} (hw4 : warpOf L g ≠ 4) (hw : warpOf L g = 5) :
    headStart P L g = some (.tma (Wg1Tma.init P L g)) := by
  simp only [headStart]
  rw [ite_eq_right hw4, ite_eq_left hw]

theorem headStart_eq7 {L : Launch} {g : Nat} (hw4 : warpOf L g ≠ 4) (hw5 : warpOf L g ≠ 5)
    (hw : warpOf L g = 7) :
    headStart P L g = some (.index (Wg1Index.init P L g)) := by
  simp only [headStart]
  rw [ite_eq_right hw4, ite_eq_right hw5, ite_eq_left hw]

theorem headStart_eq6 {L : Launch} {g : Nat} (hw4 : warpOf L g ≠ 4) (hw5 : warpOf L g ≠ 5)
    (hw7 : warpOf L g ≠ 7) (hw : warpOf L g = 6) :
    headStart P L g = some (.idle (Thread.startSite L g)) := by
  simp only [headStart]
  rw [ite_eq_right hw4, ite_eq_right hw5, ite_eq_right hw7, ite_eq_left hw]

theorem headStart_eqNone {L : Launch} {g : Nat} (hw4 : warpOf L g ≠ 4) (hw5 : warpOf L g ≠ 5)
    (hw7 : warpOf L g ≠ 7) (hw6 : warpOf L g ≠ 6) :
    headStart P L g = none := by
  simp only [headStart]
  rw [ite_eq_right hw4, ite_eq_right hw5, ite_eq_right hw7, ite_eq_right hw6]

theorem next_head_done {L : Launch} {g : Nat} {pc : Nat} {m : ShflMode} {a : Value}
    {b c : Nat} {recv : Value} {ok : Bool} {d : ThreadD}
    (hrecv : recv = b32 (warpOf L g)) (hok : ok = true) (h : headStart P L g = some d) :
    (code P L g).next .head ⟨pc, .shfl m a b c recv ok⟩ = some (some d) := by
  rw [next_head_shfl hrecv hok, h]
  rfl

theorem next_head_none {L : Launch} {g : Nat} {pc : Nat} {m : ShflMode} {a : Value}
    {b c : Nat} {recv : Value} {ok : Bool}
    (hrecv : recv = b32 (warpOf L g)) (hok : ok = true) (h : headStart P L g = none) :
    (code P L g).next .head ⟨pc, .shfl m a b c recv ok⟩ = some none := by
  rw [next_head_shfl hrecv hok, h]

theorem next_wg0_some {L : Launch} {g : Nat} {d d' : Wg0.D} {e : Event}
    (hn : (Wg0.code P L g).next d e = some (some d')) :
    (code P L g).next (.wg0 d) e = some (some (.wg0 d')) := by
  have h : Wg0.next P L g d e = some (some d') := hn
  simp only [code, next, h]

theorem next_wg0_end {L : Launch} {g : Nat} {d : Wg0.D} {e : Event}
    (hn : (Wg0.code P L g).next d e = some none)
    (hd : d.site = Wg0.Site.exit ∨ d.site = Wg0.Site.everyone) :
    (code P L g).next (.wg0 d) e = some (some .done) := by
  have h : Wg0.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_wg0_stop {L : Launch} {g : Nat} {d : Wg0.D} {e : Event}
    (hn : (Wg0.code P L g).next d e = some none)
    (hd : d.site ≠ Wg0.Site.exit) (he : d.site ≠ Wg0.Site.everyone) :
    (code P L g).next (.wg0 d) e = some none := by
  have h : Wg0.next P L g d e = some none := hn
  simp only [code, next, h, hd, he, false_or, ite_false]

theorem next_wg0_dead {L : Launch} {g : Nat} {d : Wg0.D} {e : Event}
    (hn : (Wg0.code P L g).next d e = none) :
    (code P L g).next (.wg0 d) e = none := by
  have h : Wg0.next P L g d e = none := hn
  simp only [code, next, h]

theorem next_mma_some {L : Launch} {g : Nat} {d d' : Wg1Mma.D} {e : Event}
    (hn : (Wg1Mma.code P L g).next d e = some (some d')) :
    (code P L g).next (.mma d) e = some (some (.mma d')) := by
  have h : Wg1Mma.next P L g d e = some (some d') := hn
  simp only [code, next, h]

theorem next_mma_stop {L : Launch} {g : Nat} {d : Wg1Mma.D} {e : Event}
    (hn : (Wg1Mma.code P L g).next d e = some none) (hd : d.site ≠ Wg1Mma.Site.elect) :
    (code P L g).next (.mma d) e = some none := by
  have h : Wg1Mma.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_right hd]

theorem next_mma_idle {L : Launch} {g : Nat} {d : Wg1Mma.D} {e : Event}
    (hn : (Wg1Mma.code P L g).next d e = some none) (hd : d.site = Wg1Mma.Site.elect) :
    (code P L g).next (.mma d) e = some (some (.idle (Thread.startSite L g))) := by
  have h : Wg1Mma.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_mma_end {L : Launch} {g : Nat} {d : Wg1Mma.D} {e : Event}
    (hn : (Wg1Mma.code P L g).next d e = none) (hd : d.site = Wg1Mma.Site.exit) :
    (code P L g).next (.mma d) e = some (some .done) := by
  have h : Wg1Mma.next P L g d e = none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_mma_dead {L : Launch} {g : Nat} {d : Wg1Mma.D} {e : Event}
    (hn : (Wg1Mma.code P L g).next d e = none) (hd : d.site ≠ Wg1Mma.Site.exit) :
    (code P L g).next (.mma d) e = none := by
  have h : Wg1Mma.next P L g d e = none := hn
  simp only [code, next, h, ite_eq_right hd]

theorem next_tma_some {L : Launch} {g : Nat} {d d' : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = some (some d')) :
    (code P L g).next (.tma d) e = some (some (.tma d')) := by
  have h : Wg1Tma.next P L g d e = some (some d') := hn
  simp only [code, next, h]

theorem next_tma_end {L : Launch} {g : Nat} {d : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = some none) (hd : d.site = Wg1Tma.Site.exit) :
    (code P L g).next (.tma d) e = some (some .done) := by
  have h : Wg1Tma.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_tma_stop {L : Launch} {g : Nat} {d : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = some none) (hd : d.site ≠ Wg1Tma.Site.exit)
    (hi : ¬ (d.site = Wg1Tma.Site.elect ∧ lostElection L g e = true)) :
    (code P L g).next (.tma d) e = some none := by
  have h : Wg1Tma.next P L g d e = some none := hn
  simp only [code, next, h, hd, hi, ↓reduceIte]

theorem next_tma_idle {L : Launch} {g : Nat} {d : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = some none) (hd : d.site = Wg1Tma.Site.elect)
    (hi : lostElection L g e = true) :
    (code P L g).next (.tma d) e = some (some (.idle (Thread.startSite L g))) := by
  have h : Wg1Tma.next P L g d e = some none := hn
  simp [code, next, h, hd, hi]

theorem lostElection_spec {L : Launch} {g : Nat} {e : Event} (h : lostElection L g e = true) :
    ∃ mask inst leader, e.kind = .elect mask inst leader ∧ leader ≠ PTX.laneOf L g := by
  cases hk : e.kind <;> simp [lostElection, hk] at h
  rename_i mask inst leader
  exact ⟨mask, inst, leader, rfl, h⟩

theorem next_tma_end_dead {L : Launch} {g : Nat} {d : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = none) (hd : d.site = Wg1Tma.Site.exit) :
    (code P L g).next (.tma d) e = some (some .done) := by
  have h : Wg1Tma.next P L g d e = none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_tma_dead {L : Launch} {g : Nat} {d : Wg1Tma.D} {e : Event}
    (hn : (Wg1Tma.code P L g).next d e = none) (hd : d.site ≠ Wg1Tma.Site.exit) :
    (code P L g).next (.tma d) e = none := by
  have h : Wg1Tma.next P L g d e = none := hn
  simp only [code, next, h, ite_eq_right hd]

theorem next_index_some {L : Launch} {g : Nat} {d d' : Wg1Index.D} {e : Event}
    (hn : (Wg1Index.code P L g).next d e = some (some d')) :
    (code P L g).next (.index d) e = some (some (.index d')) := by
  have h : Wg1Index.next P L g d e = some (some d') := hn
  simp only [code, next, h]

theorem next_index_end {L : Launch} {g : Nat} {d : Wg1Index.D} {e : Event}
    (hn : (Wg1Index.code P L g).next d e = some none) (hd : d.site = Wg1Index.Site.barrier) :
    (code P L g).next (.index d) e = some (some .done) := by
  have h : Wg1Index.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_index_stop {L : Launch} {g : Nat} {d : Wg1Index.D} {e : Event}
    (hn : (Wg1Index.code P L g).next d e = some none) (hd : d.site ≠ Wg1Index.Site.barrier) :
    (code P L g).next (.index d) e = some none := by
  have h : Wg1Index.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_right hd]

theorem next_index_dead {L : Launch} {g : Nat} {d : Wg1Index.D} {e : Event}
    (hn : (Wg1Index.code P L g).next d e = none) :
    (code P L g).next (.index d) e = none := by
  have h : Wg1Index.next P L g d e = none := hn
  simp only [code, next, h]

theorem next_wg2_some {L : Launch} {g : Nat} {d d' : Wg2.D} {e : Event}
    (hn : (Wg2.code P L g).next d e = some (some d')) :
    (code P L g).next (.wg2 d) e = some (some (.wg2 d')) := by
  have h : Wg2.next P L g d e = some (some d') := hn
  simp only [code, next, h]

theorem next_wg2_end {L : Launch} {g : Nat} {d : Wg2.D} {e : Event}
    (hn : (Wg2.code P L g).next d e = some none) (hd : d.site = Wg2.Site.barrier) :
    (code P L g).next (.wg2 d) e = some (some .done) := by
  have h : Wg2.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_left hd]

theorem next_wg2_stop {L : Launch} {g : Nat} {d : Wg2.D} {e : Event}
    (hn : (Wg2.code P L g).next d e = some none) (hd : d.site ≠ Wg2.Site.barrier) :
    (code P L g).next (.wg2 d) e = some none := by
  have h : Wg2.next P L g d e = some none := hn
  simp only [code, next, h, ite_eq_right hd]

theorem next_wg2_dead {L : Launch} {g : Nat} {d : Wg2.D} {e : Event}
    (hn : (Wg2.code P L g).next d e = none) :
    (code P L g).next (.wg2 d) e = none := by
  have h : Wg2.next P L g d e = none := hn
  simp only [code, next, h]

theorem next_idle_some {L : Launch} {g : Nat} {s s' : Thread.Site} {e : Event}
    (hn : (Thread.code L g).next s e = some (some s')) :
    (code P L g).next (.idle s) e = some (some (.idle s')) := by
  have h : Thread.next L s e = some (some s') := hn
  simp only [code, next, h]

theorem next_idle_stop {L : Launch} {g : Nat} {s : Thread.Site} {e : Event}
    (hn : (Thread.code L g).next s e = some none) :
    (code P L g).next (.idle s) e = some none := by
  have h : Thread.next L s e = some none := hn
  simp only [code, next, h]

theorem next_idle_end {L : Launch} {g : Nat} {s : Thread.Site} {e : Event}
    (hn : (Thread.code L g).next s e = none) (hs : s = Thread.Site.exit) :
    (code P L g).next (.idle s) e = some (some .done) := by
  have h : Thread.next L s e = none := hn
  simp only [code, next, h, ite_eq_left hs]

theorem next_idle_dead {L : Launch} {g : Nat} {s : Thread.Site} {e : Event}
    (hn : (Thread.code L g).next s e = none) (hs : s ≠ Thread.Site.exit) :
    (code P L g).next (.idle s) e = none := by
  have h : Thread.next L s e = none := hn
  simp only [code, next, h, ite_eq_right hs]

/-! ## The prologue's states -/

/-- **A prologue state is a thread state.** Every site is the prologue's; a hand-off runs the
`setmaxnreg` event and reaches the role of the thread's warpgroup; the other sites keep the
prologue's successor. -/
theorem stepAt_prologue {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (s : PSite) :
    (code P L g).StepAt (.prologue s) := by
  refine ⟨fun _ => (steps_pre hpre s).site trivial, ?_⟩
  intro t e u ins hat _ hc hf
  rcases (steps_pre hpre s).step ins hat trivial hc hf with
    (hn | ⟨s', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · cases s with
    | handoff wg =>
      by_cases hwg : wgOf L g = wg.val
      · -- the setmaxnreg event hands the thread to its warpgroup's role
        fin_cases wg
        · -- warpgroup 0
          have hpc : t.pc = 103 := hat.1
          have hc0 : kernel.code[103]? = some ins := hc
          obtain rfl := Option.some.inj (hc0.symm.trans Flow.code_setMaxReg_0)
          have hu : u = PTX.next t := fires_setMaxReg_next hf
          have hsub : u.sub = 0 := by rw [hu]; exact hat.2.1
          have hacc : u.acc = [] := by rw [hu]; exact hat.2.2.1
          have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
          have hupc : u.pc = 104 := by rw [hu]; simp [PTX.next, hpc]
          have hat104 : At u 104 (factsAt L g 103) :=
            ⟨hupc, hsub, hacc, hflt, by rw [hu]; exact hat.2.2.2.2⟩
          have hentry : Wg0.Entry P L g u :=
            wg0Entry_of_handoff hpre hg hat104 hwg
          obtain ⟨t', hr', hatd, hinv⟩ := Wg0.start_of_entry hpre hentry
          exact Or.inl (Or.inr ⟨.wg0 (Wg0.init P L g), t',
            next_prologue_handoff_true hn hwg, hr', ⟨hatd, hinv⟩⟩)
        · -- warpgroup 1: the head state at the broadcast
          have hpc : t.pc = 1842 := hat.1
          have hc1 : kernel.code[1842]? = some ins := hc
          obtain rfl := Option.some.inj (hc1.symm.trans Flow.code_setMaxReg_1)
          have hu : u = PTX.next t := fires_setMaxReg_next hf
          have hsub : u.sub = 0 := by rw [hu]; exact hat.2.1
          have hacc : u.acc = [] := by rw [hu]; exact hat.2.2.1
          have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
          have hupc : u.pc = 1843 := by rw [hu]; simp [PTX.next, hpc]
          have hat43 : At u 1843 (factsAt L g 1842) :=
            ⟨hupc, hsub, hacc, hflt, by rw [hu]; exact hat.2.2.2.2⟩
          exact Or.inl (Or.inr ⟨.head, u, next_prologue_handoff_true hn hwg, .refl,
            ⟨at_head_of_handoff hat43, trivial⟩⟩)
        · -- warpgroup 2
          have hpc : t.pc = 2606 := hat.1
          have hc2 : kernel.code[2606]? = some ins := hc
          obtain rfl := Option.some.inj (hc2.symm.trans Flow.code_setMaxReg_2)
          have hu : u = PTX.next t := fires_setMaxReg_next hf
          have hsub : u.sub = 0 := by rw [hu]; exact hat.2.1
          have hacc : u.acc = [] := by rw [hu]; exact hat.2.2.1
          have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
          have hupc : u.pc = 2607 := by rw [hu]; simp [PTX.next, hpc]
          have hat27 : At u 2607 (factsAt L g 2606) :=
            ⟨hupc, hsub, hacc, hflt, by rw [hu]; exact hat.2.2.2.2⟩
          have hentry : Wg2.Entry P L g u :=
            wg2Entry_of_handoff hpre hg hat27
          obtain ⟨t', hr', hatd, hinv⟩ := Wg2.start_all hpre hentry
          exact Or.inl (Or.inr ⟨.wg2 (Wg2.init P L g), t',
            next_prologue_handoff_true hn hwg, hr',
            ⟨hatd, hinv⟩⟩)
      · -- a warpgroup the thread is not in: not followed
        exact Or.inl (Or.inl (next_prologue_handoff_false hn hwg))
    | _ => exact Or.inl (Or.inl (next_prologue_stop hn (by intro wg hh; cases hh)))
  · exact Or.inl (Or.inr ⟨.prologue s', t', next_prologue_some hn, hr, hg'⟩)
  · exact Or.inr ⟨next_prologue_dead hn, hd⟩

/-! ## The warpgroup-1 head -/

/-- The instruction at the head's program counter: the warp-index broadcast, from lane 0 with the
full member mask, into `%r558` and the validity predicate `%p10`. -/
def headInstr : Instr :=
  ⟨none, .warp ⟨.shfl .idx, some (.int .b 32), [some 558, some 10],
    [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩⟩

/-- **The head's state**: the broadcast continues on the thread's own warp index with its
validity bit, to the warp's role; the warp's dispatch state is the role's entry. -/
theorem stepAt_head {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads) :
    (code P L g).StepAt .head := by
  refine ⟨fun _ => Wg1Mma.site_event P L g Wg1Mma.init, ?_⟩
  intro t e u ins hat _ hc hf
  have hc' : kernel.code[1843]? = some ins := hc
  obtain rfl : ins = headInstr := Option.some.inj (hc'.symm.trans Flow.code_shfl_2)
  have hpc' : (code P L g).pc ThreadD.head = 1843 := rfl
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have htr : eventTmpl Assumptions.all L g t headInstr.op =
      .shfl .idx (b32 (warpOf L g)) 0 31
        (fun recv ok => PTX.next (setReg (setReg t 558 recv) 10 (.pred ok))) := by
    simpa [headInstr] using Wg1Mma.event_head P L g hat hb
  rw [hpc'] at hf
  rw [htr] at hf
  obtain ⟨recv, ok, he, hu⟩ := hf
  have hu' : u = PTX.next (setReg (setReg t 558 recv) 10 (.pred ok)) := Option.some.inj hu
  by_cases hrecv : recv = b32 (warpOf L g)
  · by_cases hok : ok = true
    · have hat44 : At u 1844 (Wg1Mma.headFacts L g (warpOf L g)) := by
        rw [hu']
        exact at_after_headFacts hat hrecv hok
      by_cases hw4 : warpOf L g = 4
      · -- warp 4: the MMA role's election
        have hrecv4 : recv = b32 4 := by rw [hrecv, hw4]
        have h7 : At u 1844
            [(459, b32 (Wg1Mma.queryOf L g)), (460, b32 (Wg1Mma.batchOf L g)),
             (461, b32 (tidOf L g)), (466, b32 (laneOf L g)), (558, b32 4),
             (2990, .ptr 64 false (.param (param "1")) 0),
             (2991, .ptr 64 false (.param (param "0")) 0)] := by
          rw [hu', hrecv4]
          exact Wg1Mma.at_after_head4 P L g hat hw4
        have hnext : (code P L g).next .head e = some (some (.mma ⟨.elect, 0⟩)) := by
          rw [he]
          exact next_head_done hrecv hok (headStart_eq4 hw4)
        obtain ⟨t', hr', hat'⟩ : ∃ t', run kernel Assumptions.all L g 9 u = some t' ∧
            At t' 1853 (Wg1Mma.facts P L g ⟨.elect, 0⟩) := by
          seg_fp h7 using
            (simp only [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some];
             decide)
        have hinv' : Wg1Mma.Inv P L g ⟨.elect, 0⟩ := by
          refine ⟨hw4, Nat.mod_lt _ (by decide), Wg1Mma.blocks_pos P L g, Nat.zero_le _, ?_, ?_,
            ?_, hpre.mapQBind, qkIdesc_decode, pvIdesc_decode, rfl, by decide⟩
          · intro h
            exact absurd h (by simp [Wg1Mma.LoopSite])
          · intro _
            rfl
          · intro h
            exact absurd h (by simp)
        exact Or.inl (Or.inr ⟨.mma ⟨.elect, 0⟩, t', hnext, run_rtg hr', hat', hinv'⟩)
      · by_cases hw5 : warpOf L g = 5
        · -- warp 5: the raw-KV producer
          obtain ⟨t1, hr1, hentry⟩ := Wg1Mma.handoff_tma hpre hg (by rw [← hw5]; exact hat44)
          obtain ⟨t2, hr2, hatd⟩ := Wg1Tma.start_of_entry P L g hentry
          refine Or.inl (Or.inr ⟨.tma (Wg1Tma.init P L g), t2, ?_,
            Relation.ReflTransGen.trans (run_rtg hr1) hr2,
            ⟨hatd, Wg1Tma.init_inv P L g (Wg1Mma.batchOf_lt hpre hg)⟩⟩)
          rw [he]
          exact next_head_done hrecv hok (headStart_eq5 hw4 hw5)
        · by_cases hw7 : warpOf L g = 7
          · -- warp 7: the index role
            obtain ⟨t1, hr1, hentry⟩ := Wg1Mma.handoff_index hpre hg (by rw [← hw7]; exact hat44)
            obtain ⟨t2, hr2, hatd⟩ := wg1IndexEntryRun_of_pre hpre t1 hentry
              (Interface.launchTest_of_pre hpre hg)
            refine Or.inl (Or.inr ⟨.index (Wg1Index.init P L g), t2, ?_,
              Relation.ReflTransGen.trans (run_rtg hr1) hr2,
              ⟨hatd, Wg1Index.init_inv P L g⟩⟩)
            rw [he]
            exact next_head_done hrecv hok (headStart_eq7 hw4 hw5 hw7)
          · by_cases hw6 : warpOf L g = 6
            · -- warp 6: the idle loop
              obtain ⟨t1, hr1, hentry⟩ := Wg1Mma.handoff_idle (by rw [← hw6]; exact hat44)
              obtain ⟨t2, hr2, hatd, hinv'⟩ := Thread.start_of_entry hpre hentry
              refine Or.inl (Or.inr ⟨.idle (Thread.startSite L g), t2, ?_,
                Relation.ReflTransGen.trans (run_rtg hr1) hr2, ⟨hatd, hinv'⟩⟩)
              rw [he]
              exact next_head_done hrecv hok (headStart_eq6 hw4 hw5 hw7 hw6)
            · -- a warp the dispatch does not name: not followed
              exact Or.inl (Or.inl (by
                rw [he]
                exact next_head_none hrecv hok (headStart_eqNone hw4 hw5 hw7 hw6)))
    · -- the validity bit is false: not followed
      exact Or.inl (Or.inl (by
        rw [he]
        exact next_head_other (by simp [hrecv, hok])))
  · -- another warp's index: not followed
    exact Or.inl (Or.inl (by
      rw [he]
      exact next_head_other (by simp [hrecv])))

/-! ## The roles' states -/

/-- **A `Wg0` state**: the role's own step, or its `tcgen05.dealloc` end, which reaches the
`ret` across the unguarded branch at pc 1841. -/
theorem stepAt_wg0 {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (h0 : ∀ d, (Wg0.code P L g).StepAt d) (d : Wg0.D) :
    (code P L g).StepAt (.wg0 d) := by
  refine ⟨fun hinv => (h0 d).site hinv, ?_⟩
  intro t e u ins hat hinv hc hf
  rcases (h0 d).step ins hat hinv hc hf with (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · by_cases hend : d.site = Wg0.Site.exit
    · -- the deallocation ends the role; the branch at 1841 reaches the `ret`
      have htpc : t.pc = 1840 := by
        rw [hat.1]
        show d.site.pc = 1840
        rw [hend]
        rfl
      have hc' : kernel.code[1840]? = some ins := by
        have h := hc
        change kernel.code[ThreadD.pc P L g (.wg0 d)]? = some ins at h
        rw [show ThreadD.pc P L g (.wg0 d) = 1840 from by
          show d.site.pc = 1840
          rw [hend]
          rfl] at h
        exact h
      obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemDealloc_0)
      have hu : u = PTX.next t :=
        fires_async_next (A := Assumptions.all)
          (op := .tcDealloc .one (.reg 2427) (.reg 2428)) trivial hf
      have hdsub : d.sub = 0 := by
        have h := hinv.subLt
        rw [hend] at h
        have h1 : Wg0.Site.elems Wg0.Site.exit = 1 := rfl
        rw [h1] at h
        omega
      have hupc : u.pc = 1841 := by rw [hu]; simp [PTX.next, htpc]
      have hsub : u.sub = 0 := by rw [hu]; show t.sub = 0; rw [hat.2.1]; exact hdsub
      have hacc : u.acc = [] := by
        rw [hu]
        exact hat.2.2.1.trans (Wg0.siteAcc_nil d hdsub)
      have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
      obtain ⟨t', hrt, hgood⟩ := good_done_of_bra (pc := 1841) hupc hflt hsub hacc
        Flow.code_1841
        (Thread.asms_localRule_bra (t := u) (by rw [hupc]; decide) (by rw [hupc]; decide))
        (by seg_free_pc)
      exact Or.inl (Or.inr ⟨.done, t', next_wg0_end hn (.inl hend), hrt, hgood⟩)
    · by_cases hlast : d.site = .everyone
      · have hc' : kernel.code[1835]? = some ins := by
          change kernel.code[d.site.pc]? = some ins at hc
          rw [hlast] at hc
          exact hc
        obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_1835)
        have hw : warpOf L g ≠ 0 := by
          intro hw
          change Wg0.next P L g d e = some none at hn
          have he : e.kind = .bar 12 none .sync := by
            change Fires d.site.pc
              (eventTmpl Wg0.asms L g t (.barSyncN (.reg 2425) (.reg 2426) false)) e (some u) at hf
            rw [Wg0.event_everyone hpre hat hlast] at hf
            exact congrArg Event.kind hf.1
          simp [Wg0.next, Wg0.nextSite, hlast, he, hw] at hn
        obtain ⟨v, hr, hv⟩ := Wg0.everyone_return_tail hpre hlast hw hat hinv hf
        have hgood := good_done_here (P := P) (L := L) (g := g)
          hv.1 hv.2.2.2.1 hv.2.1 hv.2.2.1
        exact Or.inl (Or.inr ⟨.done, v, next_wg0_end hn (.inr hlast), run_rtg hr, hgood⟩)
      · exact Or.inl (Or.inl (next_wg0_stop hn hend hlast))
  · exact Or.inl (Or.inr ⟨.wg0 d', t', next_wg0_some hn, hr, hg'⟩)
  · exact Or.inr ⟨next_wg0_dead hn, hd⟩

/-- **An MMA state**: the role's own step. The role's last state is the `ret` itself. -/
theorem stepAt_mma {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hm : ∀ d, (Wg1Mma.code P L g).StepAt d) (d : Wg1Mma.D) :
    (code P L g).StepAt (.mma d) := by
  refine ⟨fun hinv => (hm d).site hinv, ?_⟩
  intro t e u ins hat hinv hc hf
  rcases (hm d).step ins hat hinv hc hf with (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · by_cases hd : d.site = Wg1Mma.Site.elect
    · have hnext := next_mma_idle hn hd
      obtain ⟨site, i⟩ := d
      change site = Wg1Mma.Site.elect at hd
      subst site
      obtain ⟨t', hr, hentry⟩ := Wg1Mma.handoff_elect_idle hpre hat hinv hc hf hn
      obtain ⟨t'', hr', hat', hi⟩ := Thread.start_of_entry hpre hentry
      exact Or.inl (Or.inr ⟨.idle (Thread.startSite L g), t'', hnext,
        (run_rtg hr).trans hr', ⟨hat', hi⟩⟩)
    · exact Or.inl (Or.inl (next_mma_stop hn hd))
  · exact Or.inl (Or.inr ⟨.mma d', t', next_mma_some hn, hr, hg'⟩)
  · by_cases hend : d.site = Wg1Mma.Site.exit
    · -- the `ret`: it has no continuing event, and the thread is done
      have hpc : ThreadD.pc P L g (.mma d) = 3611 := by
        show d.site.pc = 3611
        rw [hend]
        rfl
      exact Or.inl (Or.inr ⟨.done, u, next_mma_end hn hend, .refl,
        good_done_of_ret (pc := ThreadD.pc P L g (.mma d)) hpc hc hf⟩)
    · exact Or.inr ⟨next_mma_dead hn hend, hd⟩

/-- **A TMA state**: the role's own step. The role's last state is the `ret` itself. -/
theorem stepAt_tma {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (ht : ∀ d, (Wg1Tma.code P L g).StepAt d) (d : Wg1Tma.D) :
    (code P L g).StepAt (.tma d) := by
  refine ⟨fun hinv => (ht d).site hinv, ?_⟩
  intro t e u ins hat hinv hc hf
  have hdone : d.site = Wg1Tma.Site.exit → (code P L g).Good (some .done) u := by
    intro hend
    have hpc : ThreadD.pc P L g (.tma d) = 3611 := by
      show d.site.pc = 3611
      rw [hend]
      rfl
    exact good_done_of_ret hpc hc hf
  have hatD : (Wg1Tma.code P L g).AtD d t := hat
  rcases (ht d).step ins hatD hinv hc hf with (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · by_cases hend : d.site = Wg1Tma.Site.exit
    · exact Or.inl (Or.inr ⟨.done, u, next_tma_end hn hend, .refl, hdone hend⟩)
    · by_cases hi : d.site = Wg1Tma.Site.elect ∧ lostElection L g e = true
      · obtain ⟨mask, inst, leader, hkind, hne⟩ := lostElection_spec hi.2
        obtain ⟨t', hr, hentry⟩ := Wg1Tma.handoff_unelected d hi.1 hatD hc hf hkind hne
        obtain ⟨t'', hr', hat', hinv'⟩ := Thread.start_of_entry hpre hentry
        exact Or.inl (Or.inr ⟨.idle (Thread.startSite L g), t'', next_tma_idle hn hi.1 hi.2,
          hr.trans hr', ⟨hat', hinv'⟩⟩)
      · exact Or.inl (Or.inl (next_tma_stop hn hend hi))
  · have hgc : (code P L g).Good (some (.tma d')) t' := hg'
    exact Or.inl (Or.inr ⟨.tma d', t', next_tma_some hn, hr, hgc⟩)
  · by_cases hend : d.site = Wg1Tma.Site.exit
    · exact Or.inl (Or.inr ⟨.done, u, next_tma_end_dead hn hend, .refl, hdone hend⟩)
    · exact Or.inr ⟨next_tma_dead hn hend, hd⟩

/-- **An index state**: the role's own step, or its final `barrier.sync`, which reaches the
`ret` across the unguarded branch at pc 2586. -/
theorem stepAt_index {g : Nat} (hi : ∀ d, (Wg1Index.code P L g).StepAt d) (d : Wg1Index.D) :
    (code P L g).StepAt (.index d) := by
  refine ⟨fun hinv => (hi d).site hinv, ?_⟩
  intro t e u ins hat hinv hc hf
  rcases (hi d).step ins hat hinv hc hf with (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · by_cases hend : d.site = Wg1Index.Site.barrier
    · have htpc : t.pc = 2585 := by
        rw [hat.1]
        show d.site.pc = 2585
        rw [hend]
        rfl
      have hc' : kernel.code[2585]? = some ins := by
        have h := hc
        change kernel.code[ThreadD.pc P L g (.index d)]? = some ins at h
        rw [show ThreadD.pc P L g (.index d) = 2585 from by
          show d.site.pc = 2585
          rw [hend]
          rfl] at h
        exact h
      obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_13)
      have hu : u = PTX.next t :=
        fires_async_next (A := Assumptions.all)
          (op := .barSyncN (.reg 659) (.reg 660) false) trivial hf
      have hupc : u.pc = 2586 := by rw [hu]; simp [PTX.next, htpc]
      have hsub : u.sub = 0 := by
        rw [hu]
        show t.sub = 0
        rw [hat.2.1]
        show d.site.sub = 0
        rw [hend]
        rfl
      have hacc : u.acc = [] := by
        rw [hu]
        show t.acc = []
        rw [hat.2.2.1]
        change Wg1Index.accOf d = []
        simp [Wg1Index.accOf, hend]
      have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
      obtain ⟨t', hrt, hgood⟩ := good_done_of_bra (pc := 2586) hupc hflt hsub hacc
        Flow.code_2586
        (Thread.asms_localRule_bra (t := u) (by rw [hupc]; decide) (by rw [hupc]; decide))
        (by seg_free_pc)
      exact Or.inl (Or.inr ⟨.done, t', next_index_end hn hend, hrt, hgood⟩)
    · exact Or.inl (Or.inl (next_index_stop hn hend))
  · exact Or.inl (Or.inr ⟨.index d', t', next_index_some hn, hr, hg'⟩)
  · exact Or.inr ⟨next_index_dead hn, hd⟩

/-- **A `Wg2` state**: the role's own step, or its final `barrier.sync` at pc 3610, after which
the thread is at the `ret`. -/
theorem stepAt_wg2 {g : Nat} (hw2 : ∀ d, (Wg2.code P L g).StepAt d) (d : Wg2.D) :
    (code P L g).StepAt (.wg2 d) := by
  refine ⟨fun hinv => (hw2 d).site hinv, ?_⟩
  intro t e u ins hat hinv hc hf
  rcases (hw2 d).step ins hat hinv hc hf with (hn | ⟨d', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · by_cases hend : d.site = Wg2.Site.barrier
    · have htpc : t.pc = 3610 := by
        rw [hat.1]
        show d.site.pc = 3610
        rw [hend]
        rfl
      have hc' : kernel.code[3610]? = some ins := by
        have h := hc
        change kernel.code[ThreadD.pc P L g (.wg2 d)]? = some ins at h
        rw [show ThreadD.pc P L g (.wg2 d) = 3610 from by
          show d.site.pc = 3610
          rw [hend]
          rfl] at h
        exact h
      obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_15)
      have hu : u = PTX.next t :=
        fires_async_next (A := Assumptions.all)
          (op := .barSyncN (.reg 2878) (.reg 2879) false) trivial hf
      have hupc : u.pc = 3611 := by rw [hu]; simp [PTX.next, htpc]
      have hsub : u.sub = 0 := by
        rw [hu]
        show t.sub = 0
        rw [hat.2.1]
        change d.site.sub = 0
        rw [hend]; rfl
      have hacc : u.acc = [] := by
        rw [hu]
        show t.acc = []
        rw [hat.2.2.1]
        change Wg2.accAt d = []
        simp [Wg2.accAt, hend]
      have hflt : u.fault = none := by rw [hu]; exact hat.2.2.2.1
      exact Or.inl (Or.inr ⟨.done, u, next_wg2_end hn hend, .refl,
        good_done_here hupc hflt hsub hacc⟩)
    · exact Or.inl (Or.inl (next_wg2_stop hn hend))
  · exact Or.inl (Or.inr ⟨.wg2 d', t', next_wg2_some hn, hr, hg'⟩)
  · exact Or.inr ⟨next_wg2_dead hn, hd⟩

/-- **An idle state**: the role's own step; its final `ret` is `done`. -/
theorem stepAt_idle {L : Launch} {g : Nat}
    (hidle : ∀ s, (Thread.code L g).StepAt s) (s : Thread.Site) :
    (code P L g).StepAt (.idle s) := by
  refine ⟨fun _ => (hidle s).site trivial, ?_⟩
  intro t e u ins hat hinv hc hf
  have hdone : s = Thread.Site.exit → (code P L g).Good (some .done) u := by
    intro hend
    have hpc : ThreadD.pc P L g (.idle s) = 3611 := by
      show s.pc = 3611
      rw [hend]
      rfl
    exact good_done_of_ret hpc hc hf
  rcases (hidle s).step ins hat hinv hc hf with (hn | ⟨s', t', hn, hr, hg'⟩) | ⟨hn, hd⟩
  · exact Or.inl (Or.inl (next_idle_stop hn))
  · exact Or.inl (Or.inr ⟨.idle s', t', next_idle_some hn, hr, hg'⟩)
  · by_cases hend : s = Thread.Site.exit
    · exact Or.inl (Or.inr ⟨.done, u, next_idle_end hn hend, .refl, hdone hend⟩)
    · exact Or.inr ⟨next_idle_dead hn hend, hd⟩

/-- **The final state**: the `ret` performs no continuing event. -/
theorem stepAt_done {g : Nat} : (code P L g).StepAt .done := by
  refine ⟨fun _ => ⟨_, Flow.code_exit_0, rfl, trivial⟩, ?_⟩
  intro t e u ins _hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  simp only [eventTmpl, Fires] at hf
  exact absurd hf.2 (by simp)

/-! ## The composition -/

/-- The concrete index steps need only the launch's bounds and parameter bindings. -/
theorem indexSteps_of_pre {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (d : Wg1Index.D) :
    (Wg1Index.code P L g).StepAt d :=
  Wg1Index.steps hpre (wg1IndexLaunchTest_of_pre hpre hg)
    (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg) d

/-- **Every thread state is a step of the composed machine**, given the role states' steps, the
prologue's steps and the entry facts. -/
theorem steps_of_role_steps {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (h0 : ∀ d, (Wg0.code P L g).StepAt d) :
    ∀ d : ThreadD, (code P L g).StepAt d := by
  intro d
  cases d with
  | prologue s => exact stepAt_prologue hpre hg s
  | head => exact stepAt_head hpre hg
  | wg0 d => exact stepAt_wg0 hpre h0 d
  | mma d => exact stepAt_mma hpre (Wg1Mma.steps hpre) d
  | tma d => exact stepAt_tma hpre (Wg1Tma.steps hpre) d
  | index d => exact stepAt_index (indexSteps_of_pre hpre hg) d
  | idle s => exact stepAt_idle (Thread.steps hpre) s
  | wg2 d => exact stepAt_wg2 (Wg2.steps_all hpre) d
  | done => exact stepAt_done

/-- **The composed thread machine is sound**: it starts at the prologue's first shuffle and every
state is a step. -/
theorem sound_of_role_steps {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (h0 : ∀ d, (Wg0.code P L g).StepAt d) :
    (code P L g).Sound where
  start := by
    obtain ⟨t, hr, hat, -⟩ := (sound_pre hpre hg).start
    exact ⟨t, hr, hat, trivial⟩
  steps := steps_of_role_steps hpre hg h0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
