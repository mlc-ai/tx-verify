-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerStart
public import Kernels.InklingRelDecode.Proof.Thread.MmaSound
public import Lemmas.Flow.Compose

@[expose] public section

/-!
# The worker thread (warps 4 to 7) as one code machine: states and successors

A thread of warp 4 or above runs the worker's prologue and dispatch (`Worker.lean`, pc 12 to
2343) and then one of four roles, which `brx.idx` selects by the role byte the thread reads from
`global_smem + 213332 + warp`:

* index 0, warp 6: the KV loader (`Loader.lean`, pc 2344 to 2420);
* index 1, warp 7: the MMA warp (`Mma.lean`, pc 2422 to 2555);
* index 2, warps 4 and 5: the idle role (`WorkerIdle.lean`, pc 2333 to 2336);
* index 3: the exit (`bar.sync 0`, `tcgen05.dealloc` and `ret`, pc 2853 to 2855).

Every role ends at the dispatch loop's head (pc 2337), which is `Worker.Site.loop`; the exit
ends the thread. This file states the thread's composed machine: its states (`WSt`), the
registers live at each (`facts`), the invariant that ties a role's inherited registers to the
dispatch's (`Inv`), and the successors (`next`).

The roles return to the dispatch with the registers `Pro.val L g P` of the `Pro` they were
handed (`Worker.handoff L g P`, `WorkerHandoff.lean`), so a role's state carries that `Pro`
(`.loader d P`, `.mma d P`): `Rest L g P` (`Inv`) then lets `Worker.reenter` turn the role's
return into the worker's `loop` state. The dispatch reads its own successor out of the worker's
table (`Worker.next` at `.ldRole`) and follows it on every warp: none of the role machines
depends on the warp (the MMA warp's broadcast operand is the inherited warp index, and its tests
of the received word are followed both ways). That the role is the warp's is a fact of the role
table's value (`Interface.RoleReads`), not of the machine. The one condition the dispatch keeps
is the Tensor Memory base word at the MMA role's entry (`baseOk`): a word without room for the
512 columns would make the role's `tcgen05.mma` with A in Tensor Memory undefined behaviour
(`tmemOffset`), so the machine does not enter the role with it (`some none`).

The exit is the thread's last path: the `bar.sync 0` at pc 2853, the skipped, `%p3`-guarded
`tcgen05.dealloc` at pc 2854 and the `ret` at pc 2855, which no event follows (`next = none`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The warp index of a thread of the CTA (`%r3`, `shr.u32 %r1, 5`). -/
abbrev warpOf (L : Launch) (g : Nat) : Nat := Worker.warpOf L g

/-! ### The exit's states -/

/-- The events of the exit: the `bar.sync 0` at pc 2853 and the `ret` at pc 2855 (the
`tcgen05.dealloc` at pc 2854 is guarded by `%p3`, false for warps 4 to 7, and is skipped). -/
inductive ExitSite where
  | bar
  | ret
  deriving DecidableEq

def ExitSite.pc : ExitSite → Nat
  | .bar => Flow.bar_37
  | .ret => Flow.exit_0

/-- An exit state: the next event and the inherited registers (the exit reads only `%p3` and
`%r2`, the Tensor Memory base word). -/
structure ExitD where
  site : ExitSite
  P : Pro

/-! ### The composed states -/

/-- A worker thread's states: the prologue and dispatch (`Worker.D`), and the role it dispatched
to, which carries the `Pro` the dispatch handed it. -/
inductive WSt where
  | worker (w : Worker.D)
  | idle (d : Worker.Idle.D)
  | loader (d : Loader.D) (P : Pro)
  | mma (d : Mma.D) (P : Pro)
  | exit (x : ExitD)

/-- The inherited registers a role is handed: the worker's registers at the dispatch loop's
head (`Worker.handoff`). -/
abbrev handoffPro (L : Launch) (g : Nat) (P : Pro) : Pro := Worker.handoff L g P

/-- A 32-bit value as a number: the Tensor Memory base word the prologue reads at pc 13. -/
def tmOf : Value → Option Nat
  | .bits 32 x => some x.toNat
  | _ => none

theorem tmOf_spec {v : Value} {n : Nat} (h : tmOf v = some n) : v = b32 n := by
  cases v with
  | bits w x =>
    by_cases hw : w = 32
    · subst hw
      simp only [tmOf, Option.some.injEq] at h
      subst h
      simp [b32]
    · simp [tmOf, hw] at h
  | _ => simp [tmOf] at h

/-! ### Registers and their values -/

/-- The registers live at a state (the loader's table at another pc; the exit's are the
worker's). -/
def valueOf (L : Launch) (g : Nat) (x : ExitD) (r : Nat) : Value :=
  Worker.valueOf L g ⟨.loop, x.P⟩ r

def exitFactsAt (L : Launch) (g : Nat) (pc : Nat) (x : ExitD) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g x)

abbrev exitFacts (L : Launch) (g : Nat) (x : ExitD) : List (Nat × Value) :=
  exitFactsAt L g x.site.pc x

/-- The registers live at `pc`, with their values in state `d`. -/
def facts (L : Launch) (g : Nat) : WSt → List (Nat × Value)
  | .worker w => Worker.facts L g w
  | .idle d => Worker.Idle.facts L g d
  | .loader d _ => Loader.facts L g d
  | .mma d _ => Mma.facts L d
  | .exit x => exitFacts L g x

/-- The program counter of a state. -/
def pc : WSt → Nat
  | .worker w => w.site.pc
  | .idle d => d.site.pc
  | .loader d _ => d.site.pc
  | .mma d _ => d.site.pc
  | .exit x => x.site.pc

/-- The sub-step of a state: nonzero only between the two elements of the loader's vector
load. -/
def sub : WSt → Nat
  | .loader d _ => Loader.sub d
  | _ => 0

/-- The accumulator of a state: the first element of the loader's vector load. -/
def acc : WSt → List Value
  | .loader d _ => Loader.acc d
  | _ => []

/-! ### The invariant -/

/-- The invariant of the composed states: the worker's own (`Worker.Inv`); a role's inherited
registers are the `Pro` it carries, which satisfies `Rest` (so a role's return to the dispatch
is the worker's `loop` state), except the loader's two loaded words (`%r1444`, `%r6`, registers
1905 and 467); the MMA role's Tensor Memory base is the word the prologue read (except `%r10`,
register 471, which holds the word the MMA role loads) and its warp index (`%r3`) is the
thread's; and every state is a thread of warp 4 or above of a 256-thread CTA. -/
def Inv (L : Launch) (g : Nat) : WSt → Prop
  | .worker w => Worker.Inv L g w
  | .idle d => 4 ≤ warpOf L g ∧ g % L.block < 256 ∧ Worker.Pins d.P
  | .loader d P => Loader.Inv L g d ∧ Loader.ProEq L g P d ∧
      Worker.Rest L g P ∧
      4 ≤ warpOf L g ∧ g % L.block < 256
  | .mma d P => Mma.Inv d ∧ (∀ r, r ≠ 471 → d.pro r = Pro.val L g P r) ∧ Worker.Rest L g P ∧
      Pro.val L g P 463 = b32 d.tm ∧ d.pro 464 = b32 (warpOf L g) ∧ 4 ≤ warpOf L g ∧
      g % L.block < 256
  | .exit _ => 4 ≤ warpOf L g ∧ g % L.block < 256

/-! ### The successors -/

/-- The Tensor Memory base word the worker inherited (`%r2`) has room for the 512 columns: a
32-bit value `tm` with `tm + 512 ≤ 2 ^ 16` (the column field, its low 16 bits). -/
def baseOk (P : Pro) : Prop := ∃ tm, tmOf (P.rest 463) = some tm ∧ tm + 512 ≤ 2 ^ 16

/-- The state a role byte sends the warp to, on every warp: the loader, the MMA role, the idle
role, the exit or the bad path. The MMA role is entered only with a Tensor Memory base word with
room for the 512 columns (`baseOk`; the allocation's word is 0, `Interface.baseWordRead_of`); with
any other word the machine stops following the thread (`some none`). -/
def roleStart (L : Launch) (g : Nat) (P : Pro) : Worker.Site → Option (Option WSt)
  | .toLoader =>
    let Q := handoffPro L g P
    some (some (.loader (Loader.D.start L g Q) Q))
  | .toMma =>
    match tmOf (P.rest 463) with
    | some tm =>
      if tm + 512 ≤ 2 ^ 16 then
        let Q := handoffPro L g P
        some (some (.mma ⟨.setMaxReg, 0, 0, tm, Pro.val L g Q⟩ Q))
      else some none
    | none => some none
  | .toIdle => some (some (.idle (Worker.Idle.D.start P)))
  | .toExit => some (some (.exit ⟨.bar, P⟩))
  | .bad0 => some (some (.worker ⟨.bad0, P⟩))
  | _ => some none

/-- The dispatch: the successor the worker's table gives the load of the role byte
(`Worker.next` at `.ldRole`), turned into the role's first state. -/
def dispatch (L : Launch) (g : Nat) (P : Pro) (e : Event) : Option (Option WSt) :=
  match Worker.next L g ⟨.ldRole, P⟩ e with
  | some (some d') => roleStart L g P d'.site
  | some none => some none
  | none => none

/-- The abstract successor after event `e`: the worker's own successor, except at the dispatch
(which enters a role) and at the end of a role (which returns to the dispatch loop's head, or
ends the thread). -/
def next (L : Launch) (g : Nat) : WSt → Event → Option (Option WSt)
  | .worker ⟨.ldRole, P⟩, e => dispatch L g P e
  | .worker w, e => (Worker.next L g w e).map (Option.map .worker)
  | .idle d, e =>
    match d.site with
    | .inc => some (some (.worker ⟨.loop, Worker.bumpPro d.P⟩))
    | _ => (Worker.Idle.next d e).map (Option.map .idle)
  | .loader d P, e =>
    match d.site with
    | .setMaxInc => some (some (.worker ⟨.loop, Worker.bumpPro P⟩))
    | _ => (Loader.next L g d e).map (Option.map (fun d' => .loader d' P))
  | .mma d P, e =>
    match d.site with
    | .setMaxRegInc => some (some (.worker ⟨.loop, Worker.bumpPro P⟩))
    | _ => (Mma.next L g d e).map (Option.map (fun d' => .mma d' P))
  | .exit x, _e =>
    match x.site with
    | .bar => some (some (.exit ⟨.ret, x.P⟩))
    | .ret => none

/-- The composed machine of a worker thread of the launch `L` whose parameters are `Q`. -/
@[reducible] def code (L : Launch) (g : Nat) (Q : Params) : Flow.Code kernel asms L g where
  D := WSt
  init := .worker (Worker.D.start (Worker.startPro Q))
  pc := pc
  facts := facts L g
  sub := sub
  acc := acc
  inv := Inv L g
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof.WComp
