-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.Plain
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Keep tests: weak outcomes without fences (MEM-READ-AXIOMS)

Each test runs a litmus program of relaxed `.cta` loads and stores of shared memory in one CTA,
with the threads selected by `%tid.x`, and proves that the weak outcome is allowed: the execution
with that outcome is `Consistent` (the traces are runs of the kernel and every rule of the model
holds) and `Complete` (every thread exited). A model change that forbids one of these outcomes
breaks the build.

* `sb_allowed`: store buffering, both loads read the initial content.
* `mp_allowed`: message passing, the flag load reads the new flag and the data load the old data.
* `lb_allowed`: load buffering, each load reads the other thread's later store.
* `iriw_allowed`: independent reads of independent writes, the two readers see the two stores in
  opposite orders.

The unspecified shared bytes hold 0 (`init`), so a load of the initial content returns the bytes
of the 32-bit value 0 (`zero`) and a load of a store of 1 the bytes of 1 (`oneR`).
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

namespace WeakMemory

/-- One CTA of two threads. -/
def L2 : Launch := { grid := 1, block := 2, params := fun _ => none }

/-- The shared bytes 0–15 of CTA 0 are allocated with unspecified content. -/
def mem0 : Mem0 := fun l => if l.space = .shared ∧ l.cta = 0 ∧ l.addr < 16 then some none else none

/-- `st.relaxed.cta.shared.u32 [sym + off], 1`. -/
def stA (off : Nat) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .relaxed, scope := some .cta,
    elem := .int .u 32, addr := ⟨.sharedSym off, 0⟩, srcs := [.imm 1] }
/-- `ld.relaxed.cta.shared.u32 %r2, [sym + off]`. -/
def ldA (off : Nat) : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .relaxed, scope := some .cta,
    elem := .int .u 32, addr := ⟨.sharedSym off, 0⟩, dsts := [some 2] }
def st (off : Nat) : Instr := { op := .mem (stA off) }
def ld (off : Nat) : Instr := { op := .mem (ldA off) }
def exitI : Instr := { op := .exit }
/-- `setp.eq.u32 %p1, %tid.x, t`. -/
def isTid (t : Nat) : Instr :=
  { op := .int ⟨.setp .eq none, .int .u 32, false, [some 1], [.sreg ⟨.tid, some .x⟩, .imm t]⟩ }
def braIf (target : Nat) : Instr := { guard := some (1, false), op := .bra target false }

/-- The relaxed access of the four shared bytes at `off`. -/
def acc (off : Nat) : Acc := { loc := ⟨.shared, 0, off⟩, size := 4, relaxed := true }
/-- The bytes of the value 1. -/
def one : List Byte := (Value.bits 32 1).toBytes
/-- The bytes a read of the 32-bit value `n` returns. -/
def word (n : BitVec 64) : List (Option Byte) := (Value.bits 32 n).toBytes.map some
/-- The bytes a read of the initial content returns. -/
def zero : List (Option Byte) := word 0
/-- The bytes a read of a store of 1 returns. -/
def oneR : List (Option Byte) := word 1

theorem rebuild_word (n : BitVec 64) : rebuild 3 (word n) = .ok (.bits 32 n) := by
  have : word n = some (Value.bits 32 n, 0) :: (word n).tail := rfl
  rw [this]
  simp only [rebuild]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)]
  rfl

/-! ## SB: store buffering without fences -/

/-- T0 `st [x], 1; ld [y]`, T1 `st [y], 1; ld [x]`, with `x` at 0 and `y` at 4. -/
def sbK : Kernel :=
  { name := "sb", params := [], sharedBytes := 16,
    code := [isTid 0, braIf 5, st 4, ld 0, exitI, st 0, ld 4, exitI] }

/-- Both loads read the initial content. -/
def sbTr : Nat → List Event
  | 0 => [⟨5, .wr (acc 0) one⟩, ⟨6, .rd (acc 4) zero⟩, ⟨7, .exit⟩]
  | 1 => [⟨2, .wr (acc 4) one⟩, ⟨3, .rd (acc 0) zero⟩, ⟨4, .exit⟩]
  | _ => []

/-- The unspecified shared bytes hold the 32-bit value 0 in every aligned word. -/
def init : Loc → Byte := fun l => (.bits 32 0, l.addr % 4)

def sbX : Execution := plain sbTr (fun _ _ => none) init

/-- Closes the goals about the state after a load of `word n`: its next instruction and its
position. -/
macro "load_done" : tactic =>
  `(tactic| (simp only [afterAccessLoad, zero, oneR, rebuild_word, bind, Except.bind,
    extendLoaded, ldA, pure, Except.pure, MemAccess.regs, skip]; rfl))

theorem sb_produces (g : Nat) (hg : g < L2.threads) : Produces sbK [] L2 g (sbTr g) := by
  refine ⟨none, ?_⟩
  rcases g with _ | _ | g
  · refine run_tau rfl (run_tau rfl (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.step .refl ⟨_, rfl, zero, rfl, rfl, rfl⟩ (.last .refl ⟨.exit, ?_, ?_, rfl⟩)))) <;>
      load_done
  · refine run_tau rfl (run_tau rfl (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.step .refl ⟨_, rfl, zero, rfl, rfl, rfl⟩ (.last .refl ⟨.exit, ?_, ?_, rfl⟩)))) <;>
      load_done
  · simp [L2, Launch.threads] at hg

theorem sb_kinds : PlainKinds sbX := by
  rintro ⟨g, n⟩ pc k h
  rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
    simp [Execution.get, sbX, plain, sbTr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [acc]

/-- A read of the initial content of a word at offset 0 or 4 reads `zero`. -/
theorem init_read {X : Execution} (hX : X.initial = init) {off k : Nat} (ho : off = 0 ∨ off = 4)
    (hk : k < 4) (c : Option Byte) (hc : mem0 ((acc off).loc.at k) = some c) :
    zero[k]? = some (X.initialByte c ((acc off).loc.at k)) := by
  have hn : c = none := by
    rcases ho with rfl | rfl <;> interval_cases k <;> simp [mem0, acc, Loc.at] at hc <;>
      exact hc.symm
  subst hn
  rcases ho with rfl | rfl <;> interval_cases k <;> simp only [Execution.initialByte, hX] <;> rfl

theorem sb_consistent : Consistent L2 sbK [] mem0 sbX := by
  refine consistent_plain sb_kinds (by decide) sb_produces ?_ ?_ ?_ ?_
  · intro g hg
    rcases g with _ | _ | g
    · simp [L2, Launch.threads] at hg
    · simp [L2, Launch.threads] at hg
    · rfl
  · intro e a bs hr
    obtain ⟨⟨g, n⟩, rfl, ⟨pc, h⟩ | ⟨new, pc, h⟩⟩ :=
      Execution.NoTma.memReads_thread plain_emptyAsync hr <;>
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
      simp [Execution.get, plain, sbTr] at h <;> obtain ⟨-, rfl, rfl⟩ := h <;>
      exact ⟨rfl, fun k hk => init_read rfl (by simp) hk⟩
  · exact noFuture_plain sb_kinds (by simp)
  · refine hidden_plain sb_kinds ?_
    rintro ⟨g, n⟩ ⟨g', n'⟩ a bs a' bs' ⟨pc, hr⟩ ⟨pc', hw⟩ hg hn k hk hc
    simp only at hg hn
    subst hg
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;> rcases n' with _ | _ | _ | n' <;>
      simp [Execution.get, plain, sbTr] at hr hw
    all_goals
      obtain ⟨-, rfl, -⟩ := hr
      obtain ⟨-, rfl, -⟩ := hw
      simp [acc, Acc.Covers, Loc.InRange, Loc.at] at hk hc
      try omega

/-- SB: both loads read the initial content in a complete possible execution. -/
theorem sb_allowed : Consistent L2 sbK [] mem0 sbX ∧ Complete L2 sbX ∧
    sbX.get (0, 1) = some ⟨6, .rd (acc 4) zero⟩ ∧ sbX.get (1, 1) = some ⟨3, .rd (acc 0) zero⟩ :=
  ⟨sb_consistent, complete_plain sb_kinds (fun g hg => by
    rcases g with _ | _ | g
    · exact ⟨7, rfl⟩
    · exact ⟨4, rfl⟩
    · simp [L2, Launch.threads] at hg), rfl, rfl⟩

/-- A read of a store of 1 at offset `off` reads `oneR`. -/
theorem one_read {X : Execution} {w : EvId} {pc off k : Nat}
    (hw : X.get w = some ⟨pc, .wr (acc off) one⟩) (hk : k < 4) :
    ∃ a' bs', X.MemWrites (.thread w) a' bs' ∧ a'.Covers ((acc off).loc.at k) ∧
      oneR[k]? = some (wbyte a' bs' ((acc off).loc.at k)) := by
  refine ⟨acc off, one, .inl ⟨pc, hw⟩, ?_, ?_⟩
  · simp [acc, Acc.Covers, Loc.InRange, Loc.at]; omega
  · simp only [wbyte, acc, Loc.at]
    interval_cases k <;> simp <;> rfl

/-! ## MP: message passing without fences -/

/-- T0 `st [x], 1; st [y], 1`, T1 `ld [y]; ld [x]`. -/
def mpK : Kernel :=
  { name := "mp", params := [], sharedBytes := 16,
    code := [isTid 0, braIf 5, ld 4, ld 0, exitI, st 0, st 4, exitI] }

/-- The flag load reads 1 from T0's flag store and the data load reads the initial content. -/
def mpTr : Nat → List Event
  | 0 => [⟨5, .wr (acc 0) one⟩, ⟨6, .wr (acc 4) one⟩, ⟨7, .exit⟩]
  | 1 => [⟨2, .rd (acc 4) oneR⟩, ⟨3, .rd (acc 0) zero⟩, ⟨4, .exit⟩]
  | _ => []

def mpRf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref := fun r _ =>
  if r = .thread (1, 0) then some (.thread (0, 1)) else none

def mpX : Execution := plain mpTr mpRf init

theorem mp_produces (g : Nat) (hg : g < L2.threads) : Produces mpK [] L2 g (mpTr g) := by
  refine ⟨none, ?_⟩
  rcases g with _ | _ | g
  · exact run_tau rfl (run_tau rfl (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.step .refl ⟨_, rfl, rfl, rfl⟩ (.last .refl ⟨.exit, rfl, rfl, rfl⟩))))
  · refine run_tau rfl (run_tau rfl (run_read rfl rfl (bs := oneR) rfl
      (run_read (a := acc 0) (k := ?k) ?h1 ?h2 (bs := zero) rfl (run_exit_last ?h3 ?h4))))
    case h1 => load_done
    case h2 => load_done
    case h3 => load_done
    case h4 => load_done
  · simp [L2, Launch.threads] at hg

theorem mp_kinds : PlainKinds mpX := by
  rintro ⟨g, n⟩ pc k h
  rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
    simp [Execution.get, mpX, plain, mpTr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [acc]

theorem mp_consistent : Consistent L2 mpK [] mem0 mpX := by
  refine consistent_plain mp_kinds (by decide) mp_produces ?_ ?_ ?_ ?_
  · intro g hg
    rcases g with _ | _ | g
    · simp [L2, Launch.threads] at hg
    · simp [L2, Launch.threads] at hg
    · rfl
  · intro e a bs hr
    obtain ⟨⟨g, n⟩, rfl, ⟨pc, h⟩ | ⟨new, pc, h⟩⟩ :=
      Execution.NoTma.memReads_thread plain_emptyAsync hr <;>
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
      simp [Execution.get, plain, mpTr] at h <;> obtain ⟨-, rfl, rfl⟩ := h
    · refine ⟨rfl, fun k hk => ?_⟩
      simp only [plain, mpRf, ite_true]
      exact one_read (w := (0, 1)) (pc := 6) rfl hk
    · refine ⟨rfl, fun k hk => ?_⟩
      have hne : AsyncCopy.Ref.thread (1, 1) ≠ .thread (1, 0) := by simp
      simp only [plain, mpRf, hne, ite_false]
      exact init_read rfl (by simp) hk
  · refine noFuture_plain mp_kinds fun i k w h => ?_
    simp only [mpRf] at h
    split_ifs at h with hi
    cases h
    cases hi
    exact ⟨(0, 1), rfl, by simp⟩
  · refine hidden_plain mp_kinds ?_
    rintro ⟨g, n⟩ ⟨g', n'⟩ a bs a' bs' ⟨pc, hr⟩ ⟨pc', hw⟩ hg hn k hk hc
    simp only at hg hn
    subst hg
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;> rcases n' with _ | _ | _ | n' <;>
      simp [Execution.get, plain, mpTr] at hr hw

/-- MP: the flag load reads 1 and the data load the initial content in a complete possible
execution. -/
theorem mp_allowed : Consistent L2 mpK [] mem0 mpX ∧ Complete L2 mpX ∧
    mpX.get (1, 0) = some ⟨2, .rd (acc 4) oneR⟩ ∧
    mpX.rf (.thread (1, 0)) 0 = some (.thread (0, 1)) ∧
    mpX.get (1, 1) = some ⟨3, .rd (acc 0) zero⟩ ∧ mpX.rf (.thread (1, 1)) 0 = none :=
  ⟨mp_consistent, complete_plain mp_kinds (fun g hg => by
    rcases g with _ | _ | g
    · exact ⟨7, rfl⟩
    · exact ⟨4, rfl⟩
    · simp [L2, Launch.threads] at hg), rfl, rfl, rfl, by simp [mpX, plain, mpRf]⟩

/-! ## LB: load buffering without fences -/

/-- T0 `ld [x]; st [y], 1`, T1 `ld [y]; st [x], 1`. -/
def lbK : Kernel :=
  { name := "lb", params := [], sharedBytes := 16,
    code := [isTid 0, braIf 5, ld 4, st 0, exitI, ld 0, st 4, exitI] }

/-- Each load reads 1 from the other thread's store, which follows the other thread's load. -/
def lbTr : Nat → List Event
  | 0 => [⟨5, .rd (acc 0) oneR⟩, ⟨6, .wr (acc 4) one⟩, ⟨7, .exit⟩]
  | 1 => [⟨2, .rd (acc 4) oneR⟩, ⟨3, .wr (acc 0) one⟩, ⟨4, .exit⟩]
  | _ => []

def lbRf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref := fun r _ =>
  if r = .thread (0, 0) then some (.thread (1, 1))
  else if r = .thread (1, 0) then some (.thread (0, 1)) else none

def lbX : Execution := plain lbTr lbRf init

theorem lb_produces (g : Nat) (hg : g < L2.threads) : Produces lbK [] L2 g (lbTr g) := by
  refine ⟨none, ?_⟩
  rcases g with _ | _ | g
  · refine run_tau rfl (run_tau rfl (run_read rfl rfl (bs := oneR) rfl
      (run_write (a := acc 4) (t' := ?t) ?h1 ?h2 (run_exit_last ?h3 ?h4))))
    case h1 => load_done
    case h2 => load_done
    case h3 => rfl
    case h4 => rfl
  · refine run_tau rfl (run_tau rfl (run_read rfl rfl (bs := oneR) rfl
      (run_write (a := acc 0) (t' := ?u) ?h1 ?h2 (run_exit_last ?h3 ?h4))))
    case h1 => load_done
    case h2 => load_done
    case h3 => rfl
    case h4 => rfl
  · simp [L2, Launch.threads] at hg

theorem lb_kinds : PlainKinds lbX := by
  rintro ⟨g, n⟩ pc k h
  rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
    simp [Execution.get, lbX, plain, lbTr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [acc]

theorem lb_consistent : Consistent L2 lbK [] mem0 lbX := by
  refine consistent_plain lb_kinds (by decide) lb_produces ?_ ?_ ?_ ?_
  · intro g hg
    rcases g with _ | _ | g
    · simp [L2, Launch.threads] at hg
    · simp [L2, Launch.threads] at hg
    · rfl
  · intro e a bs hr
    obtain ⟨⟨g, n⟩, rfl, ⟨pc, h⟩ | ⟨new, pc, h⟩⟩ :=
      Execution.NoTma.memReads_thread plain_emptyAsync hr <;>
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;>
      simp [Execution.get, plain, lbTr] at h <;> obtain ⟨-, rfl, rfl⟩ := h
    · refine ⟨rfl, fun k hk => ?_⟩
      simp only [plain, lbRf, ite_true]
      exact one_read (w := (1, 1)) (pc := 3) rfl hk
    · refine ⟨rfl, fun k hk => ?_⟩
      have hne : AsyncCopy.Ref.thread (1, 0) ≠ .thread (0, 0) := by simp
      simp only [plain, lbRf, hne, ite_true, ite_false]
      exact one_read (w := (0, 1)) (pc := 6) rfl hk
  · refine noFuture_plain lb_kinds fun i k w h => ?_
    simp only [lbRf] at h
    split_ifs at h with h0 h1 <;> cases h
    · cases h0; exact ⟨(1, 1), rfl, by simp⟩
    · cases h1; exact ⟨(0, 1), rfl, by simp⟩
  · refine hidden_plain lb_kinds ?_
    rintro ⟨g, n⟩ ⟨g', n'⟩ a bs a' bs' ⟨pc, hr⟩ ⟨pc', hw⟩ hg hn k hk hc
    simp only at hg hn
    subst hg
    rcases g with _ | _ | g <;> rcases n with _ | _ | _ | n <;> rcases n' with _ | _ | _ | n' <;>
      simp [Execution.get, plain, lbTr] at hr hw <;> omega

/-- LB: each load reads 1 from the other thread's later store in a complete possible
execution. -/
theorem lb_allowed : Consistent L2 lbK [] mem0 lbX ∧ Complete L2 lbX ∧
    lbX.get (0, 0) = some ⟨5, .rd (acc 0) oneR⟩ ∧
    lbX.rf (.thread (0, 0)) 0 = some (.thread (1, 1)) ∧
    lbX.get (1, 0) = some ⟨2, .rd (acc 4) oneR⟩ ∧
    lbX.rf (.thread (1, 0)) 0 = some (.thread (0, 1)) :=
  ⟨lb_consistent, complete_plain lb_kinds (fun g hg => by
    rcases g with _ | _ | g
    · exact ⟨7, rfl⟩
    · exact ⟨4, rfl⟩
    · simp [L2, Launch.threads] at hg), rfl, by simp [lbX, plain, lbRf], rfl,
    by simp [lbX, plain, lbRf]⟩

/-! ## IRIW: independent reads of independent writes without fences -/

/-- One CTA of four threads. -/
def L4 : Launch := { grid := 1, block := 4, params := fun _ => none }

/-- T0 `st [x], 1`, T1 `st [y], 1`, T2 `ld [x]; ld [y]`, T3 `ld [y]; ld [x]`. -/
def iriwK : Kernel :=
  { name := "iriw", params := [], sharedBytes := 16,
    code := [isTid 0, braIf 14, isTid 1, braIf 12, isTid 2, braIf 9, ld 4, ld 0, exitI,
      ld 0, ld 4, exitI, st 4, exitI, st 0, exitI] }

/-- T2 sees the store to `x` and not the store to `y`; T3 sees them in the other order. -/
def iriwTr : Nat → List Event
  | 0 => [⟨14, .wr (acc 0) one⟩, ⟨15, .exit⟩]
  | 1 => [⟨12, .wr (acc 4) one⟩, ⟨13, .exit⟩]
  | 2 => [⟨9, .rd (acc 0) oneR⟩, ⟨10, .rd (acc 4) zero⟩, ⟨11, .exit⟩]
  | 3 => [⟨6, .rd (acc 4) oneR⟩, ⟨7, .rd (acc 0) zero⟩, ⟨8, .exit⟩]
  | _ => []

def iriwRf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref := fun r _ =>
  if r = .thread (2, 0) then some (.thread (0, 0))
  else if r = .thread (3, 0) then some (.thread (1, 0)) else none

def iriwX : Execution := plain iriwTr iriwRf init

theorem iriw_produces (g : Nat) (hg : g < L4.threads) : Produces iriwK [] L4 g (iriwTr g) := by
  refine ⟨none, ?_⟩
  rcases g with _ | _ | _ | _ | g
  · exact run_tau rfl (run_tau rfl (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.last .refl ⟨.exit, rfl, rfl, rfl⟩)))
  · exact run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (.step .refl ⟨_, rfl, rfl, rfl⟩
      (.last .refl ⟨.exit, rfl, rfl, rfl⟩)))))
  · refine run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl
      (run_read rfl rfl (bs := oneR) rfl
      (run_read (a := acc 4) (k := ?k2) ?a1 ?a2 (bs := zero) rfl (run_exit_last ?a3 ?a4))))))))
    case a1 => load_done
    case a2 => load_done
    case a3 => load_done
    case a4 => load_done
  · refine run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl (run_tau rfl
      (run_read rfl rfl (bs := oneR) rfl
      (run_read (a := acc 0) (k := ?k3) ?b1 ?b2 (bs := zero) rfl (run_exit_last ?b3 ?b4))))))))
    case b1 => load_done
    case b2 => load_done
    case b3 => load_done
    case b4 => load_done
  · exact absurd hg (by simp [L4, Launch.threads])

theorem iriw_kinds : PlainKinds iriwX := by
  rintro ⟨g, n⟩ pc k h
  rcases g with _ | _ | _ | _ | g <;> rcases n with _ | _ | _ | n <;>
    simp [Execution.get, iriwX, plain, iriwTr] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [acc]

theorem iriw_consistent : Consistent L4 iriwK [] mem0 iriwX := by
  refine consistent_plain iriw_kinds (by decide) iriw_produces ?_ ?_ ?_ ?_
  · intro g hg
    rcases g with _ | _ | _ | _ | g
    iterate 4 exact absurd hg (by simp [L4, Launch.threads])
    rfl
  · intro e a bs hr
    obtain ⟨⟨g, n⟩, rfl, ⟨pc, h⟩ | ⟨new, pc, h⟩⟩ :=
      Execution.NoTma.memReads_thread plain_emptyAsync hr <;>
    rcases g with _ | _ | _ | _ | g <;> rcases n with _ | _ | _ | n <;>
      simp [Execution.get, plain, iriwTr] at h <;> obtain ⟨-, rfl, rfl⟩ := h
    · refine ⟨rfl, fun k hk => ?_⟩
      simp only [plain, iriwRf, ite_true]
      exact one_read (w := (0, 0)) (pc := 14) rfl hk
    · refine ⟨rfl, fun k hk => ?_⟩
      have h0 : AsyncCopy.Ref.thread (2, 1) ≠ .thread (2, 0) := by simp
      have h1 : AsyncCopy.Ref.thread (2, 1) ≠ .thread (3, 0) := by simp
      simp only [plain, iriwRf, h0, h1, ite_false]
      exact init_read rfl (by simp) hk
    · refine ⟨rfl, fun k hk => ?_⟩
      have h0 : AsyncCopy.Ref.thread (3, 0) ≠ .thread (2, 0) := by simp
      simp only [plain, iriwRf, h0, ite_true, ite_false]
      exact one_read (w := (1, 0)) (pc := 12) rfl hk
    · refine ⟨rfl, fun k hk => ?_⟩
      have h0 : AsyncCopy.Ref.thread (3, 1) ≠ .thread (2, 0) := by simp
      have h1 : AsyncCopy.Ref.thread (3, 1) ≠ .thread (3, 0) := by simp
      simp only [plain, iriwRf, h0, h1, ite_false]
      exact init_read rfl (by simp) hk
  · refine noFuture_plain iriw_kinds fun i k w h => ?_
    simp only [iriwRf] at h
    split_ifs at h with h0 h1 <;> cases h
    · cases h0; exact ⟨(0, 0), rfl, by simp⟩
    · cases h1; exact ⟨(1, 0), rfl, by simp⟩
  · refine hidden_plain iriw_kinds ?_
    rintro ⟨g, n⟩ ⟨g', n'⟩ a bs a' bs' ⟨pc, hr⟩ ⟨pc', hw⟩ hg hn k hk hc
    simp only at hg hn
    subst hg
    rcases g with _ | _ | _ | _ | g <;> rcases n with _ | _ | _ | n <;>
      rcases n' with _ | _ | _ | n' <;> simp [Execution.get, plain, iriwTr] at hr hw

/-- IRIW: the two readers see the two independent stores in opposite orders in a complete
possible execution. -/
theorem iriw_allowed : Consistent L4 iriwK [] mem0 iriwX ∧ Complete L4 iriwX ∧
    iriwX.get (2, 0) = some ⟨9, .rd (acc 0) oneR⟩ ∧ iriwX.get (2, 1) = some ⟨10, .rd (acc 4) zero⟩ ∧
    iriwX.get (3, 0) = some ⟨6, .rd (acc 4) oneR⟩ ∧ iriwX.get (3, 1) = some ⟨7, .rd (acc 0) zero⟩ :=
  ⟨iriw_consistent, complete_plain iriw_kinds (fun g hg => by
    rcases g with _ | _ | _ | _ | g
    · exact ⟨15, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨8, rfl⟩
    · exact absurd hg (by simp [L4, Launch.threads])), rfl, rfl, rfl, rfl⟩

end WeakMemory

end

end PTX.Tests.Progress
