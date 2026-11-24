-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.Flow.Run
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Order.OrderNotAccess
public import Lemmas.Tcgen05.TcFence
public import Assumption.TcLdDataflow

/-!
# What a `tcgen05.ld` orders without `tcgen05.wait::ld` (THREAD-TC, DEP-TC-LOAD-VALUE)

PTX ISA 9.5 §9.7.18.6.4.5: "For tcgen05.ld , an intra-thread ordering through true register
dependency will be respected regardless of the presence or absence of other forms of
synchronization." and "This form of register dependency does not imply any other form of
ordering."

* `RegisterUse` (i): a kernel that uses the destination register of a `tcgen05.ld` in the next
  instruction, with no `tcgen05.wait::ld`, decodes; its thread performs the load and then exits,
  the next instruction is a local step that reads the loaded value, and no `ub` event occurs.
* `NoWait` (ii): thread 0 stores a Tensor Memory cell, waits for the store, loads the cell and,
  without `tcgen05.wait::ld`, fences and arrives on an mbarrier (relaxed); thread 1 of the same
  warp waits for the phase, fences and issues an MMA that writes the cell (the non-pipelined
  pattern of §9.7.18.6.4.4). The store is ordered before the MMA, the load is not: no write
  ordered before the load is stable against the MMA (DEP-TC-LOAD-VALUE `LoadStable`), so the
  loaded register has no source, the load leaves the supported fragment and the execution is
  unsafe (ERR-TMEM-READ-SOURCE).
* `Fenced` and `Acquire` (iii): the same with `tcgen05.wait::ld` before the synchronization,
  through the fences of §9.7.18.6.4.4 (DEP-TC-FENCE) or through a release arrive and an acquire
  wait without fences (EXT-TCACQUIRE): the load is ordered before the MMA, and the store is a
  stable source of the loaded cell.

* `Assumed` (iv): with the kernel assumption `tcLdDataflowAt` (ASM-TCLD-DATAFLOW) listing the
  load's site, a load whose register is read by a computing instruction before the thread's next
  event passes the static check, and the thread performs the load and then, at the same `pc`, an
  implicit `tcgen05.wait::ld` (THREAD-RUN `tcLdTmpl`). The `NoWait` execution with that wait
  event is ordered as `Fenced` is. A load whose next event (a fence) comes before the use fails
  the check, so the listed site keeps the load without a wait, and the `NoWait` execution stays
  unsafe.

The executions check the ordering rules, not whole launches: they allocate no Tensor Memory,
and the statements about stability do not depend on allocation.
-/

namespace PTX.Tests.TcLdOrder
open PTX PTX.AsyncCopy

noncomputable section

/-! ## (i) A register dependency needs no wait -/

namespace RegisterUse

private def source : Syntax.Function := {
  name := "ld_use"
  header := [".visible", ".entry", "ld_use", "(", ")"]
  body := [.declaration [".reg", ".b32", "%r", "<", "3", ">"],
    .instruction none "mov.b32" [.register "%r0", .literal "0"],
    .instruction none "tcgen05.ld.sync.aligned.32x32b.x1.b32"
      [.vector [.register "%r1"], .address [.register "%r0"]],
    .instruction none "mov.b32" [.register "%r2", .register "%r1"],
    .instruction none "ret" []] }

private def code : List Instr :=
  [⟨none, .move ⟨.scalar, .int .b 32, [some 0], [.imm 0]⟩⟩, ⟨none, .tcLd [1] 0⟩,
    ⟨none, .move ⟨.scalar, .int .b 32, [some 2], [.reg 1]⟩⟩, ⟨none, .ret⟩]

/-- The load and the use of its register, with no wait between them, decode. -/
example : (Decode.kernel source).map (·.code) = .ok code := rfl

private def K : Kernel := { name := "ld_use", params := [], code }
private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
/-- The value the load returns. -/
private def v : Value := .bits 32 7
/-- The state after `mov.b32 %r0, 0`. -/
private def t1 : TState := next (setReg {} 0 (.bits 32 0))
/-- The state after the load returns `v`. -/
private def t2 : TState := setRegs (next t1) [1] [v]
/-- The state after `mov.b32 %r2, %r1`. -/
private def t3 : TState := next (setReg t2 2 v)

example : run K [] L 0 1 {} = some t1 := rfl
/-- The load is an event that sets `%r1` to the value it returns. -/
theorem load : EStep K [] L 0 t1 ⟨1, .tc (.ld 0 [v] .s32x32b)⟩ (some t2) :=
  ⟨_, rfl, [v], rfl, rfl, rfl⟩
/-- The next instruction is a local step that reads the loaded value. -/
example : run K [] L 0 1 t2 = some t3 := rfl
example : t3.regs 2 = some v := rfl
/-- The thread then exits; its trace is the load and the exit, with no `ub` event. -/
theorem trace : Run K [] L 0 {} [⟨1, .tc (.ld 0 [v] .s32x32b)⟩, ⟨3, .exit⟩] none :=
  .step (run_rtg (K := K) (A := []) (L := L) (g := 0) (n := 1) (t' := t1) rfl) load
    (.last (run_rtg (K := K) (A := []) (L := L) (g := 0) (n := 1) (t' := t3) rfl)
      ⟨.exit, rfl, rfl, rfl⟩)

end RegisterUse

/-! ## Executions: a load, synchronization, and an MMA writing the loaded cell -/

private def replayLog (ops : List (Ref × MBarrier.Action)) : List (MBarrier.Record Ref) :=
  match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

def L : Launch := { grid := 1, block := 32, params := fun _ => none, sharedBase := 0,
                    clusterSize := 1 }
def bar : Loc := ⟨.shared, 0, 0⟩
def smem : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
/-- A cta_group::1 kind::i8 128x8 MMA with D at Tensor Memory address 0. -/
def spec : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, smem, smem, 0, 0, none,
    {}⟩
def v : Value := .bits 32 7
/-- Lane 0, column 0 of CTA 0: written by the store and the MMA, read by the load. -/
def cell0 : TcMma.Cell := ⟨0, 0, 0⟩

@[simp] def init : Event := ⟨0, .mbInit bar 1⟩
@[simp] def tst : Event := ⟨1, .tc (.st 0 [v] .s32x32b)⟩
@[simp] def waitSt : Event := ⟨2, .tc .waitSt⟩
@[simp] def tld : Event := ⟨3, .tc (.ld 0 [v] .s32x32b)⟩
@[simp] def waitLd : Event := ⟨4, .tc .waitLd⟩
@[simp] def fBefore : Event := ⟨5, .tc .fenceBefore⟩
/-- `mbarrier.arrive.relaxed.cluster` (`rel = false`) or `mbarrier.arrive.release.cluster`. -/
@[simp] def arrive (rel : Bool) : Event := ⟨6, .arrive bar 0 1 rel .cluster⟩
/-- A successful `mbarrier.try_wait.parity.{relaxed,acquire}.cluster`. -/
@[simp] def poll (acq : Bool) : Event := ⟨7, .wait bar 0 true acq .cluster⟩
@[simp] def fAfter : Event := ⟨8, .tc .fenceAfter⟩
@[simp] def mma : Event := ⟨9, .tc (.mma 0 spec false [0, 0, 0, 0])⟩
@[simp] def exit : Event := ⟨10, .exit⟩

/-- Thread 0 runs `a`, thread 1 runs `b`; thread 0's arrival at `i` completes the phase that
thread 1's first event observes. -/
def exec (a b : List Event) (i : Nat) : Execution where
  tr g := if g = 0 then a else if g = 1 then b else []
  rf _ _ := none
  objects m := if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.thread (0, i), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else []

theorem warp01 : SameWarp L 0 1 :=
  ⟨⟨by simp [L, Launch.threads], by simp [L, Launch.threads], rfl⟩, rfl⟩

theorem cluster {g h : Nat} (hg : g < 32) (hh : h < 32) : SameCluster L g h := by
  refine ⟨by simp [L, Launch.threads]; omega, by simp [L, Launch.threads]; omega, ?_⟩
  simp [L, Launch.clusterOfCta, Nat.div_eq_of_lt hg, Nat.div_eq_of_lt hh]

theorem po' {X : Execution} {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length)
    (hna : (X.get (g, i)).bind Event.acc = none := by decide) : po X (g, i) (g, j) :=
  po_of_source_not_access rfl hij hj hna

theorem baseCausalityPo {X : Execution} {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length)
    (hna : (X.get (g, i)).bind Event.acc = none := by decide) :
    baseCausality L X (g, i) (g, j) := .single (.inl (po' hij hj hna))

theorem cell0_eq : tcDataCell L 0 .s32x32b 0 0 = cell0 := by
  rfl

/-- A load of thread 0 reads `cell0` into its register 0. -/
theorem loadCell {X : Execution} {i : Nat} (h : X.get (0, i) = some tld) :
    TcMma.LoadCell L X (0, i) 0 cell0 :=
  ⟨0, [v], _, ⟨3, h⟩, by decide, cell0_eq.symm⟩

/-- A load's register 0 maps to one cell. -/
theorem loadCell_eq {X : Execution} {i : Nat} {cell : TcMma.Cell}
    (h : X.get (0, i) = some tld) (hc : TcMma.LoadCell L X (0, i) 0 cell) : cell = cell0 := by
  obtain ⟨a, vals, sh, ⟨pc, ha⟩, -, rfl⟩ := hc
  rw [h] at ha
  cases ha
  exact cell0_eq

/-- The MMA writes `cell0`. -/
theorem mmaCell {X : Execution} {e : EvId} (h : X.get e = some mma) :
    TcMma.TmemWrite L X e cell0 :=
  .inl ⟨0, spec, false, [0, 0, 0, 0], 0, 0, ⟨9, h⟩, rfl⟩

/-! ## (ii) No `wait::ld` before the synchronization: unsafe -/

namespace NoWait

def X : Execution :=
  exec [init, tst, waitSt, tld, fBefore, arrive false, exit] [poll false, fAfter, mma, exit] 5

theorem obs : MbarExec L X (0, 5) (1, 0) :=
  ⟨bar, 0, 1, false, .cluster, false, .cluster, ⟨6, rfl⟩, ⟨⟨7, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- The same synchronization orders the store, completed by its `wait::st`, before the MMA. -/
theorem store_done : TcMma.WaitBefore L X .waitSt (0, 1) (1, 2) :=
  ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide, .inr ⟨(0, 4), po' (by decide) (by decide), ⟨5, rfl⟩,
    ExecOrder.of_obs (f := (1, 1)) (po' (by decide) (by decide)) obs
      (baseCausalityPo (by decide) (by decide)) ⟨8, rfl⟩ (po' (by decide) (by decide))⟩⟩

/-- The MMA is the only one. -/
theorem mma_only {e : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (h : X.MmaIssue e d s acc mask) : e = (1, 2) := by
  obtain ⟨pc, h⟩ := h
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, exec] at h
  · by_cases h1 : g = 1
    · subst g
      match i with
      | 2 => rfl
      | 0 | 1 | 3 | _ + 4 => simp [Execution.get, X, exec] at h
    · simp [Execution.get, X, exec, hg, h1] at h

/-- The uncommitted MMA's write is ordered before no other event. -/
theorem mma_not_before {e : EvId} (he : e ≠ (1, 2)) : ¬ TcMma.WriteBefore L X (1, 2) e := by
  rintro ((hd | hp) | ⟨⟨a, vals, sh, pc, hs⟩, -⟩ | hp)
  · obtain ⟨c, rank, -, hr⟩ := hd.tracked
    simp [X, exec] at hr
  · simp only [TcMma.Pipelined] at hp
    obtain ⟨-, -, d, s, a, m, d', s', a', m', -, hm, -⟩ := hp
    exact he (mma_only hm)
  · simp [Execution.get, X, exec] at hs
  · simp only [TcMma.Pipelined] at hp
    obtain ⟨-, -, c, d, s, accum, mask, ⟨pc, hc⟩, -, -, -⟩ := hp
    simp [Execution.get, X, exec] at hc

/-- Thread 0 has no `wait::ld`, and the MMA is not a store: the load is not ordered before
the MMA. -/
theorem load_not_before : ¬ TcMma.ReadBefore L X .ld (0, 3) (1, 2) := by
  rintro (h | h)
  · obtain ⟨w, ⟨pc, hw⟩, hw1, -, -⟩ := h
    obtain ⟨g, i⟩ := w
    simp only at hw1
    subst hw1
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [Execution.get, X, exec] at hw
  · obtain ⟨-, -, -, hst⟩ := h
    obtain ⟨_, _, _, pc, hw⟩ := hst
    simp [Execution.get, X, exec] at hw

/-- No write ordered before the load is stable against the MMA (DEP-TC-LOAD-VALUE): the store
is not, since the load is not ordered before the MMA, and the MMA, which follows the load, is not
ordered before it. Allocation plays no part. -/
theorem no_stable_source (source : EvId) (hb : TcMma.WriteBefore L X source (0, 3)) :
    ¬ TcMma.ReadSource L X .ld source (0, 3) cell0 := by
  rw [TcMma.readSource_ld]
  rintro ⟨-, -, -, hs, -⟩
  rcases hs (1, 2) (mmaCell rfl) with rfl | h | h
  · exact mma_not_before (by decide) hb
  · by_cases he : source = (1, 2)
    · subst he
      exact mma_not_before (by decide) hb
    · exact mma_not_before he h
  · exact load_not_before h

/-- The store is ordered before the load, as in `Fenced.store_before`. -/
theorem store_before : TcMma.WriteBefore L X (0, 1) (0, 3) :=
  .inr (.inl ⟨⟨0, [v], _, 1, rfl⟩,
    .inl ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide, .inl (baseCausalityPo (by decide) (by decide))⟩⟩)

/-- The execution is unsafe: the loaded register has no stable source, so the load leaves the
supported fragment (ERR-TMEM-READ-SOURCE). -/
theorem rejected (K : Kernel) (A : List Assumption) (mem0 : Mem0) : Unsafe L K A mem0 X := by
  refine .inr (.inr (.inr (.inr (.inr (.inr (.inl fun h => ?_))))))
  obtain ⟨source, value, hs, -⟩ :=
    (TcMma.sourceSafe_iff.1 h).1 (0, 3) 0 cell0 (loadCell (X := X) rfl)
  exact no_stable_source source hs.2.2.1 hs

end NoWait

/-! ## (iii) `wait::ld` before the synchronization: ordered -/

/-! Through `wait::ld`, `fence::before_thread_sync`, a relaxed arrive, a relaxed wait and
`fence::after_thread_sync` (§9.7.18.6.4.4, DEP-TC-FENCE). -/
namespace Fenced

def X : Execution :=
  exec [init, tst, waitSt, tld, waitLd, fBefore, arrive false, exit]
    [poll false, fAfter, mma, exit] 6

theorem obs : MbarExec L X (0, 6) (1, 0) :=
  ⟨bar, 0, 1, false, .cluster, false, .cluster, ⟨6, rfl⟩, ⟨⟨7, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

theorem load_before : TcMma.ReadBefore L X .ld (0, 3) (1, 2) :=
  .inl ⟨(0, 4), ⟨4, rfl⟩, rfl, by decide, .inr ⟨(0, 5), po' (by decide) (by decide), ⟨5, rfl⟩,
    ExecOrder.of_obs (f := (1, 1)) (po' (by decide) (by decide)) obs
      (baseCausalityPo (by decide) (by decide)) ⟨8, rfl⟩ (po' (by decide) (by decide))⟩⟩

/-- The Tensor Memory writes are the store and the MMA. -/
theorem writers {e : EvId} {cell : TcMma.Cell} (h : TcMma.TmemWrite L X e cell) :
    e = (0, 1) ∨ e = (1, 2) := by
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, _, _, _, ⟨pc, h⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, ⟨pc, h⟩, -⟩
  all_goals
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
    · by_cases h1 : g = 1
      · subst g
        rcases i with _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
      · simp [Execution.get, X, exec, hg, h1] at h

/-- The store, completed by `wait::st`, is ordered before the load. -/
theorem store_before : TcMma.WriteBefore L X (0, 1) (0, 3) :=
  .inr (.inl ⟨⟨0, [v], _, 1, rfl⟩,
    .inl ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide, .inl (baseCausalityPo (by decide) (by decide))⟩⟩)

/-- The MMA is ordered after the load, so the store is a stable source of the loaded cell. -/
theorem stable : TcMma.ReadSource L X .ld (0, 1) (0, 3) cell0 := by
  rw [TcMma.readSource_ld]
  refine ⟨by decide, .inr (.inl ⟨0, [v], .s32x32b, 0, ⟨1, rfl⟩, by decide, cell0_eq.symm⟩),
    store_before, ?_, ?_⟩
  · intro w hw
    rcases writers hw with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr load_before)
  · rintro cta r hr
    simp [X, exec] at hr

end Fenced

/-! Through `wait::ld`, a release arrive and an acquire wait, with no tcgen05 fence
(EXT-TCACQUIRE). -/
namespace Acquire

def X : Execution :=
  exec [init, tst, waitSt, tld, waitLd, arrive true, exit] [poll true, mma, exit] 5

theorem sync : MSync L X (0, 4) (1, 1) :=
  ⟨(0, 5), (1, 0), bar, .cluster, .cluster, ⟨0, 1, 6, rfl⟩, ⟨⟨7, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    ⟨cluster (by decide) (by decide), cluster (by decide) (by decide)⟩, rfl, by decide, by decide,
    rfl, by decide⟩

theorem load_before : TcMma.ReadBefore L X .ld (0, 3) (1, 1) :=
  .inl ⟨(0, 4), ⟨4, rfl⟩, rfl, by decide, .inl (.single (.inr (.inr (.inl sync))))⟩

/-- The Tensor Memory writes are the store and the MMA. -/
theorem writers {e : EvId} {cell : TcMma.Cell} (h : TcMma.TmemWrite L X e cell) :
    e = (0, 1) ∨ e = (1, 1) := by
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, _, _, _, ⟨pc, h⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, ⟨pc, h⟩, -⟩
  all_goals
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
    · by_cases h1 : g = 1
      · subst g
        rcases i with _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
      · simp [Execution.get, X, exec, hg, h1] at h

/-- The store, completed by `wait::st`, is ordered before the load. -/
theorem store_before : TcMma.WriteBefore L X (0, 1) (0, 3) :=
  .inr (.inl ⟨⟨0, [v], _, 1, rfl⟩,
    .inl ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide, .inl (baseCausalityPo (by decide) (by decide))⟩⟩)

/-- The MMA is ordered after the load, so the store is a stable source of the loaded cell. -/
theorem stable : TcMma.ReadSource L X .ld (0, 1) (0, 3) cell0 := by
  rw [TcMma.readSource_ld]
  refine ⟨by decide, .inr (.inl ⟨0, [v], .s32x32b, 0, ⟨1, rfl⟩, by decide, cell0_eq.symm⟩),
    store_before, ?_, ?_⟩
  · intro w hw
    rcases writers hw with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr load_before)
  · rintro cta r hr
    simp [X, exec] at hr

end Acquire

/-! ## (iv) An assumed wait after a consumed load -/

namespace Assumed

/-- The load's register is read by `add` before the next event, a fence. -/
private def consumed : List Instr :=
  [⟨none, .move ⟨.scalar, .int .b 32, [some 0], [.imm 0]⟩⟩, ⟨none, .tcLd [1] 0⟩,
    ⟨none, .int ⟨.add, .int .u 32, false, [some 2], [.reg 1, .imm 1]⟩⟩,
    ⟨none, .tcFenceBefore⟩, ⟨none, .ret⟩]

/-- The fence comes before the read of the load's register. -/
private def unconsumed : List Instr :=
  [⟨none, .move ⟨.scalar, .int .b 32, [some 0], [.imm 0]⟩⟩, ⟨none, .tcLd [1] 0⟩,
    ⟨none, .tcFenceBefore⟩,
    ⟨none, .int ⟨.add, .int .u 32, false, [some 2], [.reg 1, .imm 1]⟩⟩, ⟨none, .ret⟩]

private def Kc : Kernel := { name := "ld_consumed", params := [], code := consumed }
private def Kn : Kernel := { name := "ld_unconsumed", params := [], code := unconsumed }
private def Ac : List Assumption := [Assumption.tcLdDataflowAt Kc "ld" [1] ""]
private def An : List Assumption := [Assumption.tcLdDataflowAt Kn "ld" [1] ""]
private def L1 : Launch := { grid := 1, block := 32, params := fun _ => none }
private def v : Value := .bits 32 7
private def t1 : TState := next (setReg {} 0 (.bits 32 0))
/-- After the load at sub-step 0: the register holds the value, the thread stays at the load. -/
private def t2 : TState := { setRegs (next t1) [1] [v] with pc := 1, sub := 1 }
/-- After the implicit wait: the next instruction, sub-step 0. -/
private def t3 : TState := { next t2 with sub := 0 }

/-- The static check passes for the consumed load and fails for the other. -/
example : Assumption.ldConsumedAt Kc 1 = true := by decide
example : Assumption.ldConsumedAt Kn 1 = false := by decide

/-- With the site listed and the check passing, the load continues at the same `pc`... -/
theorem load : EStep Kc Ac L1 0 t1 ⟨1, .tc (.ld 0 [v] .s32x32b)⟩ (some t2) :=
  ⟨_, rfl, [v], rfl, rfl, rfl⟩
/-- ...where the implicit `tcgen05.wait::ld` follows it. -/
theorem wait : EStep Kc Ac L1 0 t2 ⟨1, .tc .waitLd⟩ (some t3) :=
  ⟨_, rfl, rfl, rfl⟩
/-- The thread's trace up to the fence: the load, the wait at the load's `pc`, the fence. -/
theorem trace : Run Kc Ac L1 0 {} [⟨1, .tc (.ld 0 [v] .s32x32b)⟩, ⟨1, .tc .waitLd⟩,
    ⟨3, .tc .fenceBefore⟩] (some (next (next (setReg t3 2 (.bits 32 8))))) :=
  .step (run_rtg (K := Kc) (A := Ac) (L := L1) (g := 0) (n := 1) (t' := t1) rfl) load
    (.step .refl wait
      (.step (run_rtg (K := Kc) (A := Ac) (L := L1) (g := 0) (n := 1)
        (t' := next (setReg t3 2 (.bits 32 8))) rfl) ⟨_, rfl, rfl, rfl⟩ (.nil _)))

/-- With the same site listed but the check failing, the load is THREAD-TC's: no wait follows. -/
theorem load_unchecked :
    EStep Kn An L1 0 t1 ⟨1, .tc (.ld 0 [v] .s32x32b)⟩ (some (setRegs (next t1) [1] [v])) :=
  ⟨_, rfl, [v], rfl, rfl, rfl⟩

/-- The `NoWait` execution with the implicit wait at the load's position (`pc` 3). -/
@[simp] def waitAt : Event := ⟨3, .tc .waitLd⟩

def X : Execution :=
  exec [init, tst, waitSt, tld, waitAt, fBefore, arrive false, exit]
    [poll false, fAfter, mma, exit] 6

theorem obs : MbarExec L X (0, 6) (1, 0) :=
  ⟨bar, 0, 1, false, .cluster, false, .cluster, ⟨6, rfl⟩, ⟨⟨7, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- The assumed wait orders the load before the MMA, as the explicit one does in `Fenced`. -/
theorem load_before : TcMma.ReadBefore L X .ld (0, 3) (1, 2) :=
  .inl ⟨(0, 4), ⟨3, rfl⟩, rfl, by decide, .inr ⟨(0, 5), po' (by decide) (by decide), ⟨5, rfl⟩,
    ExecOrder.of_obs (f := (1, 1)) (po' (by decide) (by decide)) obs
      (baseCausalityPo (by decide) (by decide)) ⟨8, rfl⟩ (po' (by decide) (by decide))⟩⟩

/-- The Tensor Memory writes are the store and the MMA. -/
theorem writers {e : EvId} {cell : TcMma.Cell} (h : TcMma.TmemWrite L X e cell) :
    e = (0, 1) ∨ e = (1, 2) := by
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, _, _, _, ⟨pc, h⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, ⟨pc, h⟩, -⟩
  all_goals
    obtain ⟨g, i⟩ := e
    by_cases hg : g = 0
    · subst g
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
    · by_cases h1 : g = 1
      · subst g
        rcases i with _ | _ | _ | _ | i <;> simp [Execution.get, X, exec] at h ⊢
      · simp [Execution.get, X, exec, hg, h1] at h

/-- The store, completed by `wait::st`, is ordered before the load. -/
theorem store_before : TcMma.WriteBefore L X (0, 1) (0, 3) :=
  .inr (.inl ⟨⟨0, [v], _, 1, rfl⟩,
    .inl ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide, .inl (baseCausalityPo (by decide) (by decide))⟩⟩)

/-- The store is a stable source of the loaded cell: the load is ordered. -/
theorem stable : TcMma.ReadSource L X .ld (0, 1) (0, 3) cell0 := by
  rw [TcMma.readSource_ld]
  refine ⟨by decide, .inr (.inl ⟨0, [v], .s32x32b, 0, ⟨1, rfl⟩, by decide, cell0_eq.symm⟩),
    store_before, ?_, ?_⟩
  · intro w hw
    rcases writers hw with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr load_before)
  · rintro cta r hr
    simp [X, exec] at hr

end Assumed

end
end PTX.Tests.TcLdOrder
