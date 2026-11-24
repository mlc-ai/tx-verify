-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure
public import Kernels.InklingRelDecode.Proof.Thread.LedgerB0
public import Kernels.InklingRelDecode.Proof.Thread.ShapeBarOrd

@[expose] public section

/-!
# The `bar.sync 0` events of a thread without a count, as a table of its abstract states

`dN0`, `wN0` give, for a state of the default-partition machine and of the worker machine, the
number of the thread's earlier `bar.sync 0` events (without a thread count) in every run: the
two of the common start, and the last one of the epilogue or of the exit role. `dB0`, `wB0` say
that the state's own instruction is `bar.sync 0` (`d_b0`, `w_b0`: `b0At = 1`). A successor's
count is the state's plus its instruction's (`d_next_n0`, `w_next_n0`).

* default partition: 0 up to the first `bar.sync 0`, 1 after it, 2 after the second, 3 after the
  epilogue's last (its `dealloc` and `exit`);
* worker: 0 up to the first, 1 after it, 2 after the second (the dispatch loop, the roles, the
  exit role's `bar`), 3 at the exit role's `ret`.

The other facts of the file are static: the audit that the kernel's `bar.sync` are aligned only on
barrier 0 (`kernel_barSync_aligned`), the count of a `bar.sync 0` state (at most two, and two
outside the common start), and the count at the exits (three).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### The tables -/

/-- Whether a default-partition state's instruction is `bar.sync 0`. -/
def dB0 : DComp.St → Bool
  | .dstart d =>
    match d.site with
    | .bar0 | .bar1 => true
    | _ => false
  | .pro _ => false
  | .sm _ => false
  | .epi d =>
    match d.site with
    | .bar3 => true
    | _ => false

/-- The number of earlier `bar.sync 0` of a default-partition state. -/
def dN0 : DComp.St → Nat
  | .dstart d =>
    match d.site with
    | .alloc | .allocWr | .bar0 => 0
    | .ld0 | .bar1 => 1
    | _ => 2
  | .pro _ => 2
  | .sm _ => 2
  | .epi d =>
    match d.site with
    | .dealloc | .exit => 3
    | _ => 2

theorem d_b0 (s : DComp.St) : b0At (DComp.pc s) = 1 ↔ dB0 s = true := by
  cases s with
  | dstart d =>
    have h := dstart_b0 d.site
    simp only [DComp.pc, dB0]
    cases hs : d.site <;> simp_all
  | pro d =>
    have h := pro_b0 d.site
    simp only [DComp.pc, dB0]
    simp [h]
  | sm d =>
    have h := sm_b0 d.site
    simp only [DComp.pc, dB0]
    simp [h]
  | epi d =>
    have h := epi_b0 d.site
    simp only [DComp.pc, dB0]
    cases hs : d.site <;> simp_all

/-- Whether a worker state's instruction is `bar.sync 0`. -/
def wB0 : WComp.WSt → Bool
  | .worker w =>
    match w.site with
    | .bar0 | .bar1 | .toExit => true
    | _ => false
  | .idle _ => false
  | .loader .. => false
  | .mma .. => false
  | .exit x =>
    match x.site with
    | .bar => true
    | .ret => false

/-- The number of earlier `bar.sync 0` of a worker state. -/
def wN0 : WComp.WSt → Nat
  | .worker w =>
    match w.site with
    | .bar0 => 0
    | .ld0 | .bar1 => 1
    | _ => 2
  | .exit x =>
    match x.site with
    | .bar => 2
    | .ret => 3
  | _ => 2

theorem w_b0 (s : WComp.WSt) : b0At (WComp.pc s) = 1 ↔ wB0 s = true := by
  cases s with
  | worker w =>
    have h := worker_b0 w.site
    simp only [WComp.pc, wB0]
    cases hs : w.site <;> simp_all
  | idle d =>
    have h := idle_b0 d.site
    simp only [WComp.pc, wB0]
    simp [h]
  | loader d P =>
    have h := loader_b0 d.site
    simp only [WComp.pc, wB0]
    simp [h]
  | mma d P =>
    have h := mma_b0 d.site
    simp only [WComp.pc, wB0]
    simp [h]
  | exit x =>
    have h := exit_b0 x.site
    simp only [WComp.pc, wB0]
    cases hs : x.site <;> simp_all

/-! ### The successors keep the count -/

/-- **An epilogue step** adds its own instruction's `bar.sync 0`. -/
theorem epi_next_n0 {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d')) :
    dN0 (.epi d') = dN0 (.epi d) + bInc (dB0 (.epi d)) := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    (simp only [dN0, dB0, bInc, Epi.D.stores, Epi.stNext]
     (try split_ifs) <;> simp_all)

/-- **A step of the default-partition machine** adds its own instruction's `bar.sync 0`. -/
theorem d_next_n0 {L : Launch} {g : Nat} {Q : Params} {s s' : DComp.St} {e : Event}
    (h : DComp.next L g Q s e = some (some s')) : dN0 s' = dN0 s + bInc (dB0 s) := by
  cases s with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, ha, hf⟩ := mapInv h
    obtain ⟨site, tm⟩ := d
    cases site <;> simp only [DStart.next] at ha <;> (repeat' split at ha) <;>
      simp only [Option.some.injEq, reduceCtorEq] at ha <;> (try subst ha) <;>
      (try subst hf) <;> simp_all [dN0, dB0, bInc, ProA.D.start]
  | pro d =>
    obtain ⟨st, dt⟩ := d
    by_cases hb : st = ProA.Site.bar18
    · subst hb
      simp only [DComp.next, DComp.proNext, ite_true] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [dN0, dB0, bInc]
      · simp at h
    · simp only [DComp.next, DComp.proNext, hb, ite_false] at h
      obtain ⟨a, ha, rfl⟩ := mapInv h
      simp [dN0, dB0, bInc]
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [dN0, dB0, bInc, Epi.D.start, Epi.D.startSk, Epi.D.entry]
        split_ifs <;> simp_all
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := mapInv h
      simp [dN0, dB0, bInc]
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, ha, rfl⟩ := mapInv h
    exact epi_next_n0 ha

/-- A role's first state has made the two `bar.sync 0` of the common start. -/
theorem roleStart_n0 {L : Launch} {g : Nat} {P : Loader.Pro} {s : Worker.Site}
    {s' : WComp.WSt} (h : WComp.roleStart L g P s = some (some s')) : wN0 s' = 2 := by
  cases s <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [wN0]

/-- **A step of the worker machine** adds its own instruction's `bar.sync 0`. -/
theorem w_next_n0 {L : Launch} {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) : wN0 s' = wN0 s + bInc (wB0 s) := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    by_cases hl : site = .ldRole
    · subst hl
      simp only [WComp.next, WComp.dispatch] at h
      split at h
      · have := roleStart_n0 h
        rw [this]
        simp [wN0, wB0, bInc]
      · simp at h
      · simp at h
    · have h' : (Worker.next L g ⟨site, P⟩ e).map (Option.map WComp.WSt.worker) =
          some (some s') := by
        cases site <;> first | exact absurd rfl hl | exact h
      obtain ⟨a, ha, rfl⟩ := mapInv h'
      obtain ⟨st, P'⟩ := a
      cases site <;> simp only [Worker.next] at ha <;> (repeat' split at ha) <;>
        (try simp only [Option.some.injEq, reduceCtorEq, Worker.D.mk.injEq] at ha) <;>
        (try obtain ⟨rfl, rfl⟩ := ha) <;> simp_all [wN0, wB0, bInc]
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wN0, wB0, bInc])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wN0, wB0, bInc])
  | loader d P =>
    obtain ⟨d0, pro, i, n, p0, p1, ln⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wN0, wB0, bInc])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wN0, wB0, bInc])
  | mma d P =>
    obtain ⟨d0, i, n, tm, pro⟩ := d
    cases d0 <;> simp only [WComp.next] at h
    all_goals first
      | (obtain ⟨a, ha, rfl⟩ := mapInv h
         simp [wN0, wB0, bInc])
      | (simp only [Option.some.injEq] at h
         subst h
         simp [wN0, wB0, bInc])
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [WComp.next] at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [wN0, wB0, bInc]
    · simp at h

/-! ### Static facts of the tables -/

/-- **The `bar.sync` of the kernel are of an immediate barrier, and aligned exactly on barrier 0**
(an audit of the program text): `bar.sync 0` is aligned, `barrier.sync 1` is not. -/
theorem kernel_barSync_aligned : kernel.code.all (fun ins =>
    match ins.op with
    | .barSync (.imm i) al => decide ((i = 0 ∨ i = 1) ∧ (al = true ↔ i = 0))
    | .barSync .. => false
    | _ => true) = true := by
  decide +kernel

/-- **A `bar.sync 0` has at most two earlier** (the two of the common start, for the last). -/
theorem d_b0_le {s : DComp.St} (h : dB0 s = true) : dN0 s ≤ 2 := by
  cases s with
  | dstart d => cases hs : d.site <;> simp_all [dB0, dN0]
  | pro d => simp [dB0] at h
  | sm d => simp [dB0] at h
  | epi d => cases hs : d.site <;> simp_all [dB0, dN0]

theorem w_b0_le {s : WComp.WSt} (h : wB0 s = true) : wN0 s ≤ 2 := by
  cases s with
  | worker w => cases hs : w.site <;> simp_all [wB0, wN0]
  | idle d => simp [wB0] at h
  | loader d P => simp [wB0] at h
  | mma d P => simp [wB0] at h
  | exit x => cases hs : x.site <;> simp_all [wB0, wN0]

/-- **The default partition's exit** has made three `bar.sync 0`. -/
theorem d_exit_n0 (d : Epi.D) (h : d.site = .exit) : dN0 (.epi d) = 3 := by
  simp [dN0, h]

/-- **The exit role's `ret`** has made three `bar.sync 0`. -/
theorem w_exit_n0 (x : WComp.ExitD) (h : x.site = .ret) : wN0 (.exit x) = 3 := by
  simp [wN0, h]

end
end PTX.Kernels.InklingRelDecode.Proof.Ledger
