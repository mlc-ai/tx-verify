-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order

@[expose] public section

namespace PTX.SetMaxNReg
noncomputable section

/-! ## THREAD-SETMAXNREG — register adjustment requests
Statement: A `setmaxnreg` instruction is one event that carries its direction and its count, and it
  changes no register of the thread. The count must be between 24 and 256 and a multiple of 8,
  otherwise the instruction faults. The lanes of one warp are matched by the ordinal of the request,
  its source instruction and its payload.

Defs: SetMaxNReg.validCount, SetMaxNReg.tmpl, SetMaxNReg.Request, SetMaxNReg.isRequest,
  SetMaxNReg.ordinal, SetMaxNReg.SameGroup

Source:
- §9.7.21.5: "The value of imm-reg-count must be in the range 24 to 256 (both inclusive) and must be
    a multiple of 8."
- EXT-SETMAXNREG-VIRTUAL
- EXT-SETMAXNREG-EFFECTIVE

Direction: reading

Applies: setmaxnreg.inc/dec.sync.aligned.u32

Premises: Immediate count is between 24 and 256, inclusive, and a multiple of eight.

Effect: Event production. Its return is constrained by DEP-SETMAXNREG-RENDEZVOUS and its legality by
  ERR-SETMAXNREG. The local instance labels of the lanes may differ or repeat and impose no
  legality constraint.

### EXT-SETMAXNREG-VIRTUAL — PTX registers keep their values across setmaxnreg

Statement: The model takes every PTX register to keep the value last written to it across
  `setmaxnreg.inc` and `setmaxnreg.dec`, and the request changes no register of the thread
  (`SetMaxNReg.tmpl` is `next t`). The PTX ISA says that the new physical registers after `.inc`
  have undefined contents and does not say how PTX registers map onto physical ones.

Source:
- §9.7.21.5: "setmaxnreg provides a hint to the system to update the maximum number of per-thread
    registers owned by the executing warp"
- §9.7.21.5: "After the instruction setmaxnreg.inc obtains new registers from the CTA pool, the
    initial contents of the new registers are undefined. The new registers must be initialized
    before they are used."

Why it is not spec text: §9.7.21.5 speaks of the physical registers a warp owns and leaves the
  new ones' contents undefined; it does not say how the program's PTX registers map onto them.
  That `ptxas` keeps every PTX register's value across the adjustment (reading the undefined new
  registers never stands for reading a PTX register the program wrote) is the toolchain's
  allocation, not stated.

Direction: reading

Effect: If it does not hold, a PTX register read after `setmaxnreg.inc` may return the undefined
  contents of a newly obtained physical register. The values the model gives the thread after the
  request, with every result that depends on them, are then not those of the hardware. Disclosed by
  every kernel whose statement names `Op.setMaxReg`: FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192, InklingRelDecode.

### EXT-SETMAXNREG-EFFECTIVE — every setmaxnreg request takes effect and returns

Statement: The model assumes that the kernel was launched with a valid per-thread register
  configuration. Then every `setmaxnreg` request takes effect: the count the warp owns after it is
  the requested count, which is the count later requests of the warp are compared with
  (`SetMaxNReg.prior` is the previous request, ERR-SETMAXNREG). Every `setmaxnreg.inc`
  returns as soon as every lane of its warp has executed it (DEP-SETMAXNREG-RENDEZVOUS), whatever
  registers the CTA's pool holds. Register counts and the register pool are not represented, and the
  direction requirement of a warp's first request is not compared with the per-thread register
  count the kernel was launched with.

Source:
- §9.7.21.5: "The setmaxnreg.inc instruction blocks the execution until enough registers are
    available in the CTA’s register pool."
- §9.7.21.5: "The setmaxnreg instruction requires that the kernel has been launched with a valid
    value of maximum number of per-thread registers specified via the appropriate compilation via
    the appropriate compile-time option or the appropriate performance tuning directive. Otherwise,
    the setmaxnreg instruction may have no effect."
- §9.7.21.5: "When qualifier .inc is specified, the maximum number of per-thread registers owned by
    the warp prior to the execution of setmaxnreg instruction should be less than or equal to the
    imm-reg-count . Otherwise, the behavior is undefined."

Why it is not spec text: the text lets `setmaxnreg.inc` block until the pool can supply the
  registers, lets a request have no effect when the launch configuration is not valid, and states
  its direction requirements on the count the warp owns, which for a warp's first request is the
  count of the launch; the model represents none of these.

Direction: reading

Effect: The reading is not stricter than the text. It depends on the launch configuration, which
  the model does not check. If it does not hold, an `inc` that the registers of the launch cannot
  satisfy blocks the warp forever on hardware, and the model's `progress` and `terminates`
  conclusions do not reflect that. A request may have no effect, so the count the model uses as
  the base of the next direction comparison (the previous request) differs from the count the
  hardware holds, and a later request in the wrong direction, which is undefined, may not be
  reported. A warp's first request in the wrong direction from the launch's per-thread count is
  undefined, and the model does not report it. Disclosed by every kernel whose statement names
  `Op.setMaxReg`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.
-/
/-- A legal register count: between 24 and 256 and a multiple of 8. -/
def validCount (n : Nat) : Bool := 24 ≤ n && n ≤ 256 && n % 8 == 0

/-- The event of a `setmaxnreg` of count `n`: a request event that leaves the registers
unchanged, or `badValue` for an illegal count. -/
def tmpl (t : TState) (inc : Bool) (n : Nat) : Tmpl :=
  if validCount n then .setMaxReg inc n (next t) else .ub .badValue

/-- Event `e` is a `setmaxnreg` request with direction `inc`, count `n` and instance label
`inst`, at source position `pc`. -/
def Request (X : Execution) (e : EvId) (pc : Nat) (inc : Bool) (n inst : Nat) : Prop :=
  X.get e = some ⟨pc, .setMaxReg inc n inst⟩

/-- The event is a `setmaxnreg` request. -/
def isRequest (ev : Event) : Bool :=
  match ev.kind with
  | .setMaxReg .. => true
  | _ => false

/-- The number of `setmaxnreg` requests that the thread of `e` made before `e`. -/
def ordinal (X : Execution) (e : EvId) : Nat := ((X.tr e.1).take e.2).countP isRequest

/-- Threads `g` and `h` are in the same warpgroup of one CTA. -/
def SameGroup (L : Launch) (g h : Nat) : Prop :=
  SameCta L g h ∧ (g % L.block) / 128 = (h % L.block) / 128

/-! ## DEP-SETMAXNREG-RENDEZVOUS — warp rendezvous of a register adjustment
Statement: A `setmaxnreg` request returns only after every one of the 32 lanes of its warp has made
  the same request, with the same ordinal, source instruction and payload.

Defs: SetMaxNReg.SameRequest

Source:
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- EXT-SETMAXNREG-EFFECTIVE

Direction: reading

Applies: setmaxnreg events

Premises: The request is followed by another event of its thread: it returned.

Effect: `SameRequest` gives the needs of a request in `KindNeeds` (DEP-ORDER): the matching
  request of every lane of the warp is a witness of its return. No other condition delays the
  return (EXT-SETMAXNREG-EFFECTIVE): the wait for the CTA's register pool is not a need.
-/
/-- `e` and `f` are the same request of one warp: same warp, same ordinal, same source
position, direction and count. -/
def SameRequest (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  SameWarp L e.1 f.1 ∧ ordinal X e = ordinal X f ∧
    ∃ pc inc n einst finst, Request X e pc inc n einst ∧ Request X f pc inc n finst

/-! ## ERR-SETMAXNREG — register adjustment legality
Statement: A `setmaxnreg` request is unsafe when its direction disagrees with the count of the
  thread's previous request, when its warpgroup is not entirely inside the CTA, or when requests of
  one warpgroup with the same ordinal differ in direction or count. It is also unsafe when a thread
  of the previous request of the warpgroup is not ordered before it.

Defs: SetMaxNReg.prior, SetMaxNReg.Unsafe, SetMaxNReg.UnsafeAt, SetMaxNReg.UnsafeAt.unsafe,
  SetMaxNReg.unsafeAt_noExempt

Source:
- §9.7.21.5: "When qualifier .dec is specified, the maximum number of per-thread registers owned by
    the warp prior to the execution of setmaxnreg instruction should be greater than or equal to the
    imm-reg-count . Otherwise, the behavior is undefined."
- §9.7.21.5: "When qualifier .inc is specified, the maximum number of per-thread registers owned by
    the warp prior to the execution of setmaxnreg instruction should be less than or equal to the
    imm-reg-count . Otherwise, the behavior is undefined."
- §9.7.21.5: "The same setmaxnreg instruction must be executed by all warps in a warpgroup ."
- §9.7.21.5: "After executing a setmaxnreg instruction, all warps in the warpgroup must synchronize
    explicitly before executing subsequent setmaxnreg instructions."
- §9.7.21.5: "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
    executing thread to wait until all threads in the warp execute the same setmaxnreg instruction
    before resuming execution."
- EXT-SETMAXNREG-EFFECTIVE
- EXT-BAR-PARTICIPANTS

Direction: stricter

Applies: setmaxnreg events

Premises: A thread's request has an ordinal (DEP-SETMAXNREG-RENDEZVOUS); its previous request, if
  any, gives the count the warp owns, as if it took effect (EXT-SETMAXNREG-EFFECTIVE).

Effect: Contributes to Unsafe. A warpgroup thread that has not exited and not yet reached the
  request remains a progress obligation, not an assumed arrival. The first request of a thread is
  not compared with the launch's register count (EXT-SETMAXNREG-EFFECTIVE). Between warps only the
  direction and count are compared, which is the reading EXT-BAR-PARTICIPANTS. The source
  instructions of the lanes of one warp and a thread of the warpgroup that exits before the request
  are ERR-ALIGNED-MISMATCH. The order between the previous request of the warpgroup and a later
  request is base causality order (`baseCausality`, MEM-BASE-CAUSALITY). A request at a site that
  an assumption selects with `regSyncExempt` (ASM-SETMAXNREG-SYNC) is not subject to the last
  clause (`UnsafeAt`).
-/
/-- The count of the thread's previous request before `e`, if any. -/
def prior (X : Execution) (e : EvId) : Option Nat :=
  ((X.tr e.1).take e.2).foldl (fun old ev => match ev.kind with
    | .setMaxReg _ n _ => some n | _ => old) none

/-- The execution contains a `setmaxnreg` request that is unsafe (ERR-SETMAXNREG). -/
def Unsafe (L : Launch) (X : Execution) : Prop :=
  ∃ e pc inc n inst, Request X e pc inc n inst ∧
    ( (∃ m, prior X e = some m ∧ (if inc then n < m else m < n)) ∨
      (e.1 % L.block / 128 * 128 + 128 > L.block) ∨
      (∃ f pc' inc' n' inst', SameGroup L e.1 f.1 ∧
        Request X f pc' inc' n' inst' ∧ ordinal X e = ordinal X f ∧
        (inc ≠ inc' ∨ n ≠ n')) ∨
      (0 < ordinal X e ∧ ¬ ∀ h, h < L.threads → SameGroup L e.1 h →
        ∃ j pc' inc' n' inst', Request X (h, j) pc' inc' n' inst' ∧
          ordinal X (h, j) + 1 = ordinal X e ∧ baseCausality L X (h, j) e) )

/-- `Unsafe` with the exemption of ASM-SETMAXNREG-SYNC: the fourth clause (the previous request of
the warpgroup is not ordered before the request) does not apply to a request at a site that an
assumption of `A` selects with `regSyncExempt`. The other three clauses are those of `Unsafe`.
With no site selected it is `Unsafe` (`unsafeAt_noExempt`). -/
def UnsafeAt (A : List Assumption) (L : Launch) (X : Execution) : Prop :=
  ∃ e pc inc n inst, Request X e pc inc n inst ∧
    ( (∃ m, prior X e = some m ∧ (if inc then n < m else m < n)) ∨
      (e.1 % L.block / 128 * 128 + 128 > L.block) ∨
      (∃ f pc' inc' n' inst', SameGroup L e.1 f.1 ∧
        Request X f pc' inc' n' inst' ∧ ordinal X e = ordinal X f ∧
        (inc ≠ inc' ∨ n ≠ n')) ∨
      (A.all (fun a => !a.regSyncExempt pc) = true ∧ 0 < ordinal X e ∧
        ¬ ∀ h, h < L.threads → SameGroup L e.1 h →
        ∃ j pc' inc' n' inst', Request X (h, j) pc' inc' n' inst' ∧
          ordinal X (h, j) + 1 = ordinal X e ∧ baseCausality L X (h, j) e) )

/-- The exemption only removes unsafety: `UnsafeAt` implies `Unsafe`. -/
theorem UnsafeAt.unsafe {A : List Assumption} {L : Launch} {X : Execution}
    (h : UnsafeAt A L X) : Unsafe L X := by
  obtain ⟨e, pc, inc, n, inst, hr, h1 | h2 | h3 | ⟨-, h4, h5⟩⟩ := h
  · exact ⟨e, pc, inc, n, inst, hr, Or.inl h1⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inl h2)⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inr (Or.inl h3))⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inr (Or.inr ⟨h4, h5⟩))⟩

/-- With no site selected by `regSyncExempt`, `UnsafeAt` is `Unsafe`. -/
theorem unsafeAt_noExempt {A : List Assumption} {L : Launch} {X : Execution}
    (h : ∀ a ∈ A, ∀ pc, a.regSyncExempt pc = false) : UnsafeAt A L X ↔ Unsafe L X := by
  refine ⟨UnsafeAt.unsafe, ?_⟩
  rintro ⟨e, pc, inc, n, inst, hr, h1 | h2 | h3 | ⟨h4, h5⟩⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inl h1⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inl h2)⟩
  · exact ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inr (Or.inl h3))⟩
  · refine ⟨e, pc, inc, n, inst, hr, Or.inr (Or.inr (Or.inr ⟨?_, h4, h5⟩))⟩
    simp only [List.all_eq_true]
    intro a ha
    simp [h a ha pc]

end
end PTX.SetMaxNReg
