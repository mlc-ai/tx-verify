-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr
public import Core.Sync.ClusterBarrierExecution
public import Core.Sync.MatrixExec
public import Core.Thread.SetMaxNReg

@[expose] public section

/-!
# The `.aligned` qualifier

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

variable (L : Launch)

/-! ## ERR-ALIGNED-MISMATCH — aligned participants execute the same instruction
Statement: The lanes of one warp execute their k-th aligned instruction of one class at one source
  position and with the same operands. The classes are the warp-collective `tcgen05`
  instructions, `barrier{.cta}`, `barrier.cluster`, `setmaxnreg` and the warp-level matrix
  instructions. A participant of an aligned instruction does not exit before it executes the
  instruction. The participants are the warp, the warpgroup for `setmaxnreg`, and every thread of
  the CTA for an aligned `barrier{.cta}` without a thread count. An execution that breaks either
  condition is unsafe.

Defs: Execution.ExitedShort, Kernel.alignedAt, Kernel.isAlignedCtaBar, tcStatic, AlignedClass,
  AlignedClass.member, AlignedClass.exitMember, AlignedClass.aligned, AlignedClass.operands,
  AlignedClass.Participants, AlignedClass.Divergent, AlignedClass.Exited, AlignedMismatch,
  alignedMismatch_iff, isTcColl_kind, isCluster_kind, isMatrix_kind, isRequest_kind,
  isAlignedCtaBar_kind, sameWarp_lane, AlignedClass.divergent_tc_iff,
  AlignedClass.exited_tc_iff, AlignedClass.divergent_bar_iff, AlignedClass.exited_bar_iff,
  AlignedClass.divergent_cluster_iff, AlignedClass.exited_cluster_iff,
  AlignedClass.divergent_setMaxReg_iff, AlignedClass.exited_setMaxReg_old,
  AlignedClass.divergent_matrix_old, AlignedClass.exited_matrix_old

Source:
- §9.7.15.1: "Instruction barrier{.cta} has optional .aligned modifier. When specified, it indicates
    that all threads in CTA will execute the same barrier{.cta} instruction."
- §9.7.15.1 (bar.sync is barrier.sync.aligned)
- §9.7.15.1: "bar{.cta}.arrive is equivalent to barrier{.cta}.arrive.aligned ."
- §9.7.15.3: "The optional .aligned qualifier indicates that all threads in the warp must execute
    the same barrier.cluster instruction."
- §9.7.16.5.14: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same mma instruction."
- §9.7.16.5.14: "The behavior of mma instruction is undefined if all threads in the same warp do not
    use the same qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.15: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same ldmatrix instruction."
- §9.7.16.5.15: "The behavior of ldmatrix is undefined if all threads do not use the same
    qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.16: "The behavior of stmatrix is undefined if all threads do not use the same
    qualifiers, or if any thread in the warp has exited."
- §9.7.16.5.17: "The mandatory .aligned qualifier indicates that all threads in the warp must
    execute the same movmatrix instruction."
- §9.7.16.6.3: "The behavior of mma.sp/mma.sp::ordered_metadata instruction is undefined if all
    threads in the same warp do not use the same qualifiers, or if any thread in the warp has
    exited."
- §9.7.18.7.1: "The mandatory .aligned qualifier indicates that all threads in the warp must execute
    the same instruction."
- §9.7.18.7.1: "The behavior of the instruction is undefined if all the threads in the warp do not
    use the same values of nCols , or if any thread in the warp has exited."
- §9.7.18.8.3: "The behavior of tcgen05.ld is undefined if all threads do not use the same values of
    taddr , or if any thread in the warp has exited."
- §9.7.18.8.4: "The behavior of tcgen05.st is undefined if all threads do not use the same values of
    taddr , or if any thread in the warp has exited."
- §9.7.18.8.5: "The mandatory .aligned qualifier indicates that all threads in the warp must execute
    the same tcgen05.wait_operation instruction."
- §9.7.21.5: "The mandatory .aligned qualifier indicates that all threads in the warpgroup must
    execute the same setmaxnreg instruction."
- §9.7.21.5: "If a setmaxnreg instruction is not executed by all warps in the warpgroup , then the
    behavior is undefined."
- EXT-BAR-PARTICIPANTS

Direction: reading

Applies: Warp-collective `tcgen05` events (allocation management, `ld`, `st`, the waits),
  `barrier{.cta}` events of either form, `barrier.cluster` events, `setmaxnreg` requests and
  warp-level matrix events

Premises: Each class numbers its events within a thread (`AlignedClass.member`); the exit clause of
  `barrier{.cta}` numbers the aligned barriers without a thread count (`AlignedClass.exitMember`).
  The exit clause counts the events of the class in the whole trace of the exiting thread
  (`Execution.ExitedShort`). A trace that the thread rules produce ends at its exit (THREAD-RUN),
  so there this count equals the count of the events before the exit. On a trace built by hand
  with events after the exit, the count can be larger and the clause can miss the exit.

Effect: Safety rejection (`AlignedMismatch`). Two lanes of a warp at their `k`-th event of a class,
  one of them aligned, at different source positions or with different operands
  (`AlignedClass.Divergent`), are undefined. So is a participant that exits with at most `k` events
  of the class while another participant executes its `k`-th aligned one (`AlignedClass.Exited`).
  The guard of an aligned instruction is ERR-NONUNIFORM-GUARD. Between different warps, the barrier
  name and thread count of `barrier{.cta}` and the direction and count of `setmaxnreg` are compared
  by ERR-BARRIER-MISMATCH and ERR-SETMAXNREG (EXT-BAR-PARTICIPANTS).

Review: The operands compared (`AlignedClass.operands`) are the static operands of the event. A
  `tcgen05.ld` or `tcgen05.st` lane's loaded or stored values are its own, so `tcStatic` drops them,
  and the address and the access shape, with the `.16x32bx2` half-split offset, are compared. A
  matrix lane's contributed and received bytes are dropped, and its operation is compared. A
  `barrier.cluster` event is compared whole. The operands of `barrier{.cta}` and `setmaxnreg` are
  not compared here, because the instruction's own rule compares them for every form. The
  warp-collective `tcgen05` forms, `setmaxnreg` and the matrix instructions carry `.sync.aligned` in
  their syntax (`Op.aligned`), so all their events are aligned. A `barrier.cluster` event carries
  its qualifier. A `barrier{.cta}` event takes it from the instruction at its position
  (`Kernel.alignedAt`). An exited thread does not execute the instruction, so the `.aligned`
  sentence makes the exit of a participant undefined. The text says so for the allocation
  instructions, `tcgen05.ld`, `tcgen05.st`, `ldmatrix`, `stmatrix`, `mma`, `mma.sp` and
  `setmaxnreg`. For `tcgen05.wait`, `barrier.cluster` and `movmatrix` the model reads the `.aligned`
  sentence the same way. For `barrier{.cta}`, "all threads in CTA" means the participants of the
  barrier (EXT-BAR-PARTICIPANTS). For a barrier without a thread count these are all threads of the
  CTA. A barrier with a thread count is not in the exit clause. The sentence "All threads in warp
  (except for those have exited) must execute barrier{.cta} instruction in convergence" governs the
  lanes of one warp and is ERR-BARRIER-MISMATCH. Accesses outside a Tensor Memory allocation are
  ERR-TMEM-ACCESS-LIFETIME.
  This rule replaced the alignment clauses of the former per-instruction checks. For the
  warp-collective `tcgen05` instructions, `barrier{.cta}`, `barrier.cluster` and the divergence
  clause of `setmaxnreg`, lemmas state that the two checks are equivalent (`divergent_tc_iff`,
  `exited_tc_iff`, `divergent_bar_iff`, `exited_bar_iff`, `divergent_cluster_iff`,
  `exited_cluster_iff`, `divergent_setMaxReg_iff`). For the matrix instructions and the exit
  clause of `setmaxnreg`, the lemmas state one direction only: this rule implies the former clause
  (`divergent_matrix_old`, `exited_matrix_old`, `exited_setMaxReg_old`). The former matrix
  clauses named the lanes `g - laneOf g + lane` for every `lane < 32`, which can leave the CTA
  when the CTA size is not a multiple of 32, and the former `setmaxnreg` exit clause counted the
  requests before the exit. On the traces that the thread rules produce, a thread outside the
  launch has no events and a trace ends at its exit, so the former clauses also imply this rule
  there. No lemma states this converse.
-/

/-- Thread `f.1` has exited (`f` is its exit event) having executed at most `k` events of
class `c` in its whole trace (an execution that the thread rules produce ends at the exit,
THREAD-RUN): it skips the aligned collective that other participants execute as their `k`-th. -/
def Execution.ExitedShort (X : Execution) (c : Event → Bool) (f : EvId) (k : Nat) : Prop :=
  (∃ pc, X.get f = some ⟨pc, .exit⟩) ∧ (X.tr f.1).countP c ≤ k

/-- The instruction at `pc` is aligned; positions outside the code count as aligned. -/
def Kernel.alignedAt (K : Kernel) (pc : Nat) : Bool :=
  match K.code[pc]? with
  | some ins => ins.op.aligned
  | none => true

/-- An aligned barrier (either form) without a thread count: its participants are the whole
CTA. -/
def Kernel.isAlignedCtaBar (K : Kernel) : Event → Bool
  | ⟨pc, .bar _ none _⟩ => K.alignedAt pc
  | _ => false

/-- What every lane of a warp must agree on for a `tcgen05` collective: the event without what it
returned. -/
def tcStatic : TcKind → TcKind
  | .ld a _ shape => .ld a [] shape
  | .st a _ shape => .st a [] shape
  | k => k

/-- The classes of aligned instructions. Each class numbers its events within a thread. -/
inductive AlignedClass where
  /-- The warp-collective `tcgen05` instructions (`isTcColl`). -/
  | tc
  /-- `barrier{.cta}`, either form. -/
  | bar
  /-- `barrier.cluster`, either operation. -/
  | cluster
  /-- `setmaxnreg`. -/
  | setMaxReg
  /-- The warp-level matrix instructions. -/
  | matrix
  deriving DecidableEq, Repr

namespace AlignedClass

/-- The events of the class, numbered within each thread for the comparison of the lanes of a
warp. -/
def member : AlignedClass → Event → Bool
  | .tc => isTcColl
  | .bar => Execution.isBar
  | .cluster => isCluster
  | .setMaxReg => SetMaxNReg.isRequest
  | .matrix => isMatrix

/-- The events of the class numbered for the exit clause: the aligned barriers without a thread
count for `barrier{.cta}`, the class itself otherwise. -/
def exitMember (K : Kernel) : AlignedClass → Event → Bool
  | .bar => K.isAlignedCtaBar
  | c => c.member

/-- The event carries `.aligned`: a `barrier{.cta}` takes it from its instruction, a
`barrier.cluster` from its operation, and the other classes are always aligned. -/
def aligned (K : Kernel) : AlignedClass → Event → Bool
  | .bar, ev => K.alignedAt ev.pc
  | .cluster, ev => match ev.kind with
    | .cluster op => op.aligned
    | _ => false
  | _, _ => true

/-- The operands the lanes of a warp must agree on. They are `none` for `barrier{.cta}` and
`setmaxnreg`, whose own rules compare their operands. -/
def operands : AlignedClass → Kind → Option Kind
  | .tc, .tc k => some (.tc (tcStatic k))
  | .matrix, .matrix op _ _ => some (.matrix op [] [])
  | .bar, _ | .setMaxReg, _ => none
  | _, k => some k

/-- The participants of an aligned instruction of the class whose exit is undefined: the CTA for
a barrier without a thread count, the warpgroup for `setmaxnreg`, the warp otherwise. -/
def Participants : AlignedClass → Nat → Nat → Prop
  | .bar, g, h => SameCta L g h
  | .setMaxReg, g, h => SameWarpgroup L g h
  | _, g, h => SameWarp L g h

/-- Two lanes of a warp at their `k`-th event of class `c`, one of them aligned, execute
different source instructions or use different operands. -/
def Divergent (K : Kernel) (c : AlignedClass) (X : Execution) : Prop :=
  ∃ e f pe pf ke kf, SameWarp L e.1 f.1 ∧ X.get e = some ⟨pe, ke⟩ ∧ X.get f = some ⟨pf, kf⟩ ∧
    c.member ⟨pe, ke⟩ = true ∧ c.member ⟨pf, kf⟩ = true ∧
    ((X.tr e.1).take e.2).countP c.member = ((X.tr f.1).take f.2).countP c.member ∧
    (c.aligned K ⟨pe, ke⟩ || c.aligned K ⟨pf, kf⟩) = true ∧
    (pe ≠ pf ∨ c.operands ke ≠ c.operands kf)

/-- A participant exits having executed at most `k` events of the exit class of `c` while another
participant executes its `k`-th, which is aligned. -/
def Exited (K : Kernel) (c : AlignedClass) (X : Execution) : Prop :=
  ∃ e f ev, c.Participants L e.1 f.1 ∧ X.get e = some ev ∧ c.exitMember K ev = true ∧
    c.aligned K ev = true ∧
    X.ExitedShort (c.exitMember K) f (((X.tr e.1).take e.2).countP (c.exitMember K))

end AlignedClass

/-- The `.aligned` check fails for some class: two lanes of a warp diverge at an aligned
instruction, or a participant exits before one. -/
def AlignedMismatch (K : Kernel) (X : Execution) : Prop :=
  ∃ c : AlignedClass, c.Divergent L K X ∨ c.Exited L K X

/-- `AlignedMismatch` class by class. -/
theorem alignedMismatch_iff {K : Kernel} {X : Execution} :
    AlignedMismatch L K X ↔
      (AlignedClass.tc.Divergent L K X ∨ AlignedClass.tc.Exited L K X) ∨
      (AlignedClass.bar.Divergent L K X ∨ AlignedClass.bar.Exited L K X) ∨
      (AlignedClass.cluster.Divergent L K X ∨ AlignedClass.cluster.Exited L K X) ∨
      (AlignedClass.setMaxReg.Divergent L K X ∨ AlignedClass.setMaxReg.Exited L K X) ∨
      (AlignedClass.matrix.Divergent L K X ∨ AlignedClass.matrix.Exited L K X) := by
  constructor
  · rintro ⟨c, h⟩
    cases c
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · rintro (h | h | h | h | h)
    exacts [⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩, ⟨_, h⟩]

theorem isTcColl_kind {pc : Nat} {k : Kind} (h : isTcColl ⟨pc, k⟩ = true) : ∃ a, k = .tc a := by
  cases k <;> simp_all [isTcColl]

theorem isCluster_kind {pc : Nat} {k : Kind} (h : isCluster ⟨pc, k⟩ = true) :
    ∃ op, k = .cluster op := by
  cases k <;> simp_all [isCluster]

theorem isMatrix_kind {pc : Nat} {k : Kind} (h : isMatrix ⟨pc, k⟩ = true) :
    ∃ op own recv, k = .matrix op own recv := by
  cases k <;> simp_all [isMatrix]

theorem isRequest_kind {pc : Nat} {k : Kind} (h : SetMaxNReg.isRequest ⟨pc, k⟩ = true) :
    ∃ inc n inst, k = .setMaxReg inc n inst := by
  cases k <;> simp_all [SetMaxNReg.isRequest]

theorem isAlignedCtaBar_kind {K : Kernel} {ev : Event} (h : K.isAlignedCtaBar ev = true) :
    K.alignedAt ev.pc = true := by
  obtain ⟨pc, k⟩ := ev
  cases k <;> simp_all [Kernel.isAlignedCtaBar]
  rename_i id count mode
  cases count <;> simp_all

/-- A thread of the warp of `g` is the lane of its own lane index in that warp. -/
theorem sameWarp_lane {g h : Nat} (hw : SameWarp L g h) : h = g - laneOf L g + laneOf L h := by
  obtain ⟨⟨-, -, hc⟩, hw⟩ := hw
  have hg := Nat.div_add_mod g L.block
  have hh := Nat.div_add_mod h L.block
  simp only [laneOf]
  generalize g % L.block = r at *
  generalize h % L.block = r' at *
  generalize g / L.block = q at *
  subst hc
  omega

namespace AlignedClass

/-- The `tcgen05` divergence clause is the first clause of the former `TcUnsafe`. -/
theorem divergent_tc_iff {K : Kernel} {X : Execution} :
    AlignedClass.tc.Divergent L K X ↔
      ∃ e f k pc pc' ke kf, SameWarp L e.1 f.1 ∧ X.TcK e k ∧ X.TcK f k ∧
        X.get e = some ⟨pc, .tc ke⟩ ∧ X.get f = some ⟨pc', .tc kf⟩ ∧
        (pc ≠ pc' ∨ tcStatic ke ≠ tcStatic kf) := by
  constructor
  · rintro ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, -, hd⟩
    obtain ⟨a, rfl⟩ := isTcColl_kind hme
    obtain ⟨b, rfl⟩ := isTcColl_kind hmf
    refine ⟨e, f, _, pe, pf, a, b, hw, ⟨⟨_, he, hme⟩, rfl⟩, ⟨⟨_, hf, hmf⟩, hk.symm⟩, he, hf, ?_⟩
    simpa [operands] using hd
  · rintro ⟨e, f, k, pc, pc', ke, kf, hw, ⟨⟨ev, he', hme⟩, hke⟩, ⟨⟨fv, hf', hmf⟩, hkf⟩, he, hf,
      hd⟩
    rw [he] at he'
    rw [hf] at hf'
    cases he'
    cases hf'
    exact ⟨e, f, pc, pc', .tc ke, .tc kf, hw, he, hf, hme, hmf, hke.trans hkf.symm, rfl,
      by simpa [operands] using hd⟩

/-- The `tcgen05` exit clause is the second clause of the former `TcUnsafe`. -/
theorem exited_tc_iff {K : Kernel} {X : Execution} :
    AlignedClass.tc.Exited L K X ↔
      ∃ e f k, SameWarp L e.1 f.1 ∧ X.TcK e k ∧ X.ExitedShort isTcColl f k := by
  constructor
  · rintro ⟨e, f, ev, hw, he, hm, -, hx⟩
    exact ⟨e, f, _, hw, ⟨⟨ev, he, hm⟩, rfl⟩, hx⟩
  · rintro ⟨e, f, k, hw, ⟨⟨ev, he, hm⟩, rfl⟩, hx⟩
    exact ⟨e, f, ev, hw, he, hm, rfl, hx⟩

/-- The `barrier{.cta}` divergence clause is the source-position part of the former
`BarMismatch` and `BarArriveMismatch`, for both forms. -/
theorem divergent_bar_iff {K : Kernel} {X : Execution} :
    AlignedClass.bar.Divergent L K X ↔
      ∃ g h i j id id' count count' mode mode' pc pc', SameWarp L g h ∧
        X.get (g, i) = some ⟨pc, .bar id count mode⟩ ∧
        X.get (h, j) = some ⟨pc', .bar id' count' mode'⟩ ∧
        ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar ∧
        (K.alignedAt pc || K.alignedAt pc') = true ∧ pc ≠ pc' := by
  constructor
  · rintro ⟨⟨g, i⟩, ⟨h, j⟩, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, ha, hd⟩
    cases ke <;> simp [member, Execution.isBar] at hme
    cases kf <;> simp [member, Execution.isBar] at hmf
    exact ⟨g, h, i, j, _, _, _, _, _, _, pe, pf, hw, he, hf, hk, ha, by simpa [operands] using hd⟩
  · rintro ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', hw, he, hf, hk, ha, hd⟩
    exact ⟨(g, i), (h, j), pc, pc', _, _, hw, he, hf, rfl, rfl, hk, ha, .inl hd⟩

/-- The `barrier{.cta}` exit clause is the second clause of the former `BarMismatch`. -/
theorem exited_bar_iff {K : Kernel} {X : Execution} :
    AlignedClass.bar.Exited L K X ↔
      ∃ e f k, SameCta L e.1 f.1 ∧ (∃ ev, X.get e = some ev ∧ K.isAlignedCtaBar ev = true) ∧
        ((X.tr e.1).take e.2).countP K.isAlignedCtaBar = k ∧
        X.ExitedShort K.isAlignedCtaBar f k := by
  constructor
  · rintro ⟨e, f, ev, hc, he, hm, -, hx⟩
    exact ⟨e, f, _, hc, ⟨ev, he, hm⟩, rfl, hx⟩
  · rintro ⟨e, f, k, hc, ⟨ev, he, hm⟩, rfl, hx⟩
    exact ⟨e, f, ev, hc, he, hm, isAlignedCtaBar_kind hm, hx⟩

/-- The `barrier.cluster` divergence clause is the first clause of the former
`ClusterMismatch`. -/
theorem divergent_cluster_iff {K : Kernel} {X : Execution} :
    AlignedClass.cluster.Divergent L K X ↔
      ∃ g h i j pc pc' op op', SameWarp L g h ∧
        X.get (g, i) = some ⟨pc, .cluster op⟩ ∧ X.get (h, j) = some ⟨pc', .cluster op'⟩ ∧
        ((X.tr g).take i).countP isCluster = ((X.tr h).take j).countP isCluster ∧
        (op.aligned = true ∨ op'.aligned = true) ∧ (pc ≠ pc' ∨ op ≠ op') := by
  constructor
  · rintro ⟨⟨g, i⟩, ⟨h, j⟩, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, ha, hd⟩
    obtain ⟨op, rfl⟩ := isCluster_kind hme
    obtain ⟨op', rfl⟩ := isCluster_kind hmf
    refine ⟨g, h, i, j, pe, pf, op, op', hw, he, hf, hk, by simpa [aligned] using ha, ?_⟩
    simpa [operands] using hd
  · rintro ⟨g, h, i, j, pc, pc', op, op', hw, he, hf, hk, ha, hd⟩
    exact ⟨(g, i), (h, j), pc, pc', _, _, hw, he, hf, rfl, rfl, hk,
      by simpa [aligned] using ha, by simpa [operands] using hd⟩

/-- The `barrier.cluster` exit clause is the second clause of the former `ClusterMismatch`. -/
theorem exited_cluster_iff {K : Kernel} {X : Execution} :
    AlignedClass.cluster.Exited L K X ↔
      ∃ e f k pc op, SameWarp L e.1 f.1 ∧ X.get e = some ⟨pc, .cluster op⟩ ∧ op.aligned = true ∧
        ((X.tr e.1).take e.2).countP isCluster = k ∧ X.ExitedShort isCluster f k := by
  constructor
  · rintro ⟨e, f, ⟨pc, k⟩, hw, he, hm, ha, hx⟩
    obtain ⟨op, rfl⟩ := isCluster_kind hm
    exact ⟨e, f, _, pc, op, hw, he, by simpa [aligned] using ha, rfl, hx⟩
  · rintro ⟨e, f, k, pc, op, hw, he, ha, rfl, hx⟩
    exact ⟨e, f, _, hw, he, rfl, by simpa [aligned] using ha, hx⟩

/-- The `setmaxnreg` divergence clause is the source-position part of the former
`SetMaxNReg.Unsafe`. -/
theorem divergent_setMaxReg_iff {K : Kernel} {X : Execution} :
    AlignedClass.setMaxReg.Divergent L K X ↔
      ∃ e f pc pc' inc inc' n n' inst inst', SameWarp L e.1 f.1 ∧
        SetMaxNReg.Request X e pc inc n inst ∧ SetMaxNReg.Request X f pc' inc' n' inst' ∧
        SetMaxNReg.ordinal X e = SetMaxNReg.ordinal X f ∧ pc ≠ pc' := by
  constructor
  · rintro ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, -, hd⟩
    obtain ⟨inc, n, inst, rfl⟩ := isRequest_kind hme
    obtain ⟨inc', n', inst', rfl⟩ := isRequest_kind hmf
    exact ⟨e, f, pe, pf, inc, inc', n, n', inst, inst', hw, he, hf, hk,
      by simpa [operands] using hd⟩
  · rintro ⟨e, f, pc, pc', inc, inc', n, n', inst, inst', hw, he, hf, hk, hd⟩
    exact ⟨e, f, pc, pc', _, _, hw, he, hf, rfl, rfl, hk, rfl, .inl hd⟩

/-- The `setmaxnreg` exit clause implies the exit clause of the former `SetMaxNReg.Unsafe`. The
converse holds when the exit is the last event of its thread. -/
theorem exited_setMaxReg_old {K : Kernel} {X : Execution}
    (h : AlignedClass.setMaxReg.Exited L K X) :
    ∃ e pc inc n inst, SetMaxNReg.Request X e pc inc n inst ∧
      ∃ h j pc', h < L.threads ∧ SetMaxNReg.SameGroup L e.1 h ∧
        X.get (h, j) = some ⟨pc', .exit⟩ ∧
        SetMaxNReg.ordinal X (h, j) ≤ SetMaxNReg.ordinal X e := by
  obtain ⟨e, ⟨h, j⟩, ⟨pc, k⟩, ⟨hc, hg⟩, he, hm, -, ⟨pcx, hx⟩, hle⟩ := h
  obtain ⟨inc, n, inst, rfl⟩ := isRequest_kind hm
  refine ⟨e, pc, inc, n, inst, he, h, j, pcx, hc.2.1, ⟨hc, ?_⟩, hx, ?_⟩
  · dsimp only at hg
    omega
  · exact (List.take_sublist j (X.tr h)).countP_le.trans hle

/-- The matrix divergence clause implies the source-position clause of the former
`MatrixUnsafe`. The converse holds when the CTA size is a multiple of 32. -/
theorem divergent_matrix_old {K : Kernel} {X : Execution}
    (h : AlignedClass.matrix.Divergent L K X) :
    ∃ g i pc op own recv n, X.get (g, i) = some ⟨pc, .matrix op own recv⟩ ∧ X.MatrixK (g, i) n ∧
      ∃ lane < 32, ∃ j pc' op' own' recv',
        X.get (g - laneOf L g + lane, j) = some ⟨pc', .matrix op' own' recv'⟩ ∧
        X.MatrixK (g - laneOf L g + lane, j) n ∧ (pc' ≠ pc ∨ op' ≠ op) := by
  obtain ⟨⟨g, i⟩, ⟨h, j⟩, pe, pf, ke, kf, hw, he, hf, hme, hmf, hk, -, hd⟩ := h
  obtain ⟨op, own, recv, rfl⟩ := isMatrix_kind hme
  obtain ⟨op', own', recv', rfl⟩ := isMatrix_kind hmf
  have hl := sameWarp_lane L hw
  refine ⟨g, i, pe, op, own, recv, _, he, ⟨⟨_, he, hme⟩, rfl⟩, laneOf L h, Nat.mod_lt _ (by omega),
    j, pf, op', own', recv', ?_, ?_, ?_⟩
  · rw [← hl]
    exact hf
  · rw [← hl]
    exact ⟨⟨_, hf, hmf⟩, hk.symm⟩
  · rcases hd with hd | hd
    · exact .inl (Ne.symm hd)
    · refine .inr fun ho => hd ?_
      rw [ho]
      rfl

/-- The matrix exit clause implies the exit clause of the former `MatrixUnsafe`. -/
theorem exited_matrix_old {K : Kernel} {X : Execution} (h : AlignedClass.matrix.Exited L K X) :
    ∃ g i pc op own recv n, X.get (g, i) = some ⟨pc, .matrix op own recv⟩ ∧ X.MatrixK (g, i) n ∧
      ∃ lane < 32, ∃ k, X.ExitedShort isMatrix (g - laneOf L g + lane, k) n := by
  obtain ⟨⟨g, i⟩, ⟨h, j⟩, ⟨pc, k⟩, hw, he, hm, -, hx⟩ := h
  obtain ⟨op, own, recv, rfl⟩ := isMatrix_kind hm
  have hl := sameWarp_lane L hw
  refine ⟨g, i, pc, op, own, recv, _, he, ⟨⟨_, he, hm⟩, rfl⟩, laneOf L h,
    Nat.mod_lt _ (by omega), j, ?_⟩
  rw [← hl]
  exact hx

end AlignedClass

end PTX
