-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bar
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.SegFree
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The idle warp of warpgroup 1 (`wg1Idle`)

Warp 6 of warpgroup 1 — shared with the unelected lanes of warps 4 and 5 — runs the empty main
loop of `kernel.cuh:618`. The role reads the launch's batch count `b` from `param_0` and, when
the exit guard `%p66 = (%ctaid.y ≥ b)` does not hold (it never does for a CTA of the grid), the
two optional per-batch length pointers. It loads the per-batch lengths with `ld.global.nc` where
a pointer is non-null, passes the named barrier `barrier.sync 12, 384` (the whole CTA: a count
equal to the block size is the CTA barrier, which is why the event carries no count) and returns
at pc 3611. The role's pc range is 2587 to 2605 (`Roles.lean`); every instruction between the two
`.nc` loads and the barrier is local.

## The events

The role's only event instructions are the two `ld.global.nc.s32` loads (pcs 2596 and 2601), the
barrier (pc 2604) and the kernel's single `ret` (pc 3611). The `ld.param`s, the integer
instructions and the branches are local steps, which the machine takes inside its segments: the
null-pointer branches are one step each on the predicate value the table states (`bra_to`), not
sites. The machine's states are one per event (`Site`); its initial state (`startSite`) is read
off the launch's data, since the exit guard and the two null tests are functions of `L` alone:
the exit guard is `%p66 = %ctaid.y ≥ b`, and the two length pointers are the 64-bit words at
bytes 80 and 144 of `param_0`, the null pointer being the zero word. The path from the hand-off
at 2587 to the first event is therefore fixed per launch (`start_of_entry`).

The `.nc` loads read content no operation of the kernel writes; they are the two sites of
`Assumptions.ncReadOnly` in this pc range (`Data/Sites.lean`: 2596 and 2601 are in `ncLoads`),
and `loadTmpl` gives them `readNC` events rather than ordinary reads. A load whose bytes do not
rebuild to a value faults the thread and the machine stops; the loaded word is dead at the next
instruction (`%r463`/`%r464` are not live), so the successor does not depend on it.

## What the machine needs from the hand-off

`Entry` is the hand-off state at pc 2587: the thread is about to execute the role's first
instruction with the two registers live there, `%r460 = %ctaid.y` and the register 2991 (`%rd2`)
holding the symbolic parameter-space pointer of `param_0`. `start_of_entry` runs the local prefix
from there to `startSite`, and `sound_of_entry` assembles the machine's `Sound` from that hand-off
and the launch's `{}`-to-entry run (the prologue's and the warpgroup-1 head's machines). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread

open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ## Launch data the role reads -/

/-- The thread's CTA in the launch. -/
abbrev ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- `%ctaid.y` of the thread's CTA: the batch of the kernel's `(s_q, b, 1)` grid. -/
abbrev ctaidY (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).y % 2 ^ 32

/-- The little-endian `n`-byte word at byte `off` of the scalar parameter object `param_0`; a
byte the launch does not supply counts as zero. -/
abbrev paramWord (L : Launch) (off n : Nat) : Nat := paramNat L (param "0") off n

/-- The value of the role's exit guard `setp.ge.s32 %p66, %ctaid.y, b`. -/
abbrev geBatch (L : Launch) (g : Nat) : Bool :=
  compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (ctaidY L g)))
    (truncBits 32 (BitVec.ofNat 64 (paramWord L 0 4)))

/-- The value of `setp.eq.b64 %p, %rd, 0` on the 64-bit word at byte `off` of `param_0`:
`true` exactly for the null pointer. -/
abbrev ptrIsNull (L : Launch) (off : Nat) : Bool :=
  compare .eq .b 64 (truncBits 64 (BitVec.ofNat 64 (paramWord L off 8)))
    (truncBits 64 (BitVec.ofInt 64 0))

theorem paramNat_lt (L : Launch) (name : String) (off : Nat) :
    ∀ n, paramNat L name off n < 256 ^ n
  | 0 => by simp [paramNat]
  | n + 1 => by
    have ih := paramNat_lt L name (off + 1) n
    have hb : ((L.paramBytes name off).getD 0).toNat < 256 := by
      cases h : L.paramBytes name off with
      | none => simp
      | some b => rw [Option.getD_some]; simpa using b.isLt
    have hpos : 0 < 256 ^ n := pow_pos (by norm_num) n
    simp only [paramNat]
    rw [pow_succ]
    omega

/-- A 64-bit word of `param_0` is an address below `2 ^ 64`. -/
theorem paramWord_lt (L : Launch) (off : Nat) : paramWord L off 8 < 2 ^ 64 := by
  have h := paramNat_lt L (param "0") off 8
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rwa [e] at h

theorem paramWord_four {L : Launch} {off x : Nat}
    (h : ∀ k < 4, L.paramBytes (param "0") (off + k) = some (leByte x k)) :
    paramWord L off 4 = x % 2 ^ 32 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [paramWord, paramNat, h0, h1, show off + 1 + 1 = off + 2 by omega,
    h2, show off + 2 + 1 = off + 3 by omega, h3, Option.getD_some, leByte, BitVec.toNat_ofNat]
  omega

theorem paramWord_eight {L : Launch} {off x : Nat}
    (h : ∀ k < 8, L.paramBytes (param "0") (off + k) = some (leByte x k)) :
    paramWord L off 8 = x % 2 ^ 64 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [paramWord, paramNat, h0, h1, show off + 1 + 1 = off + 2 by omega,
    h2, show off + 2 + 1 = off + 3 by omega, h3, show off + 3 + 1 = off + 4 by omega,
    h4, show off + 4 + 1 = off + 5 by omega, h5, show off + 5 + 1 = off + 6 by omega,
    h6, show off + 6 + 1 = off + 7 by omega, h7, Option.getD_some, leByte, BitVec.toNat_ofNat]
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The batch count word of `param_0` is `b`, modulo `2 ^ 32`. -/
theorem paramWord_b (hpre : Pre P L mem0) : paramWord L 0 4 = P.b % 2 ^ 32 :=
  paramWord_four fun k hk => by simpa using hpre.paramB k hk

theorem paramWord_80_zero (hpre : Pre P L mem0) (h : P.topkLenBase = none) :
    paramWord L 80 8 = 0 := by
  have hb := hpre.paramTopkLen
  rw [h] at hb
  obtain ⟨hbytes, -⟩ := hb
  have e := paramWord_eight (x := 0) fun k hk => by simpa [leByte] using hbytes k hk
  rw [e]
  exact Nat.zero_mod _

theorem paramWord_80_some (hpre : Pre P L mem0) {x : Nat} (h : P.topkLenBase = some x) :
    paramWord L 80 8 = x % 2 ^ 64 := by
  have hb := hpre.paramTopkLen
  rw [h] at hb
  obtain ⟨hptr, -, -⟩ := hb
  exact paramWord_eight fun k hk => by simpa using hptr k hk

theorem paramWord_144_zero (hpre : Pre P L mem0) (h : P.extraTopkLenBase = none) :
    paramWord L 144 8 = 0 := by
  have hb := hpre.paramExtraTopkLen
  rw [h] at hb
  obtain ⟨hbytes, -⟩ := hb
  have e := paramWord_eight (x := 0) fun k hk => by simpa [leByte] using hbytes k hk
  rw [e]
  exact Nat.zero_mod _

theorem paramWord_144_some (hpre : Pre P L mem0) {x : Nat}
    (h : P.extraTopkLenBase = some x) : paramWord L 144 8 = x % 2 ^ 64 := by
  have hb := hpre.paramExtraTopkLen
  rw [h] at hb
  obtain ⟨hptr, -, -⟩ := hb
  exact paramWord_eight fun k hk => by simpa using hptr k hk

/-- The pointer word at byte `off` of the bytes of `x` is four-byte aligned. -/
theorem paramWord_mod4_of {off x : Nat}
    (h : ∀ k < 8, L.paramBytes (param "0") (off + k) = some (leByte x k)) (hx : x % 4 = 0) :
    paramWord L off 8 % 4 = 0 := by
  rw [paramWord_eight h, Nat.mod_mod_of_dvd x (show 4 ∣ 2 ^ 64 by decide)]
  exact hx

/-- The `topk_length` pointer word is four-byte aligned: the launch gives a null pointer as
zero bytes and a non-null one as an address divisible by four. -/
theorem paramWord_80_mod4 (hpre : Pre P L mem0) : paramWord L 80 8 % 4 = 0 := by
  cases h : P.topkLenBase with
  | none => rw [paramWord_80_zero hpre h, Nat.zero_mod]
  | some x =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    obtain ⟨hptr, hal, -⟩ := hb
    exact paramWord_mod4_of (fun k hk => by simpa using hptr k hk) hal

/-- The `extra_topk_length` pointer word is four-byte aligned. -/
theorem paramWord_144_mod4 (hpre : Pre P L mem0) : paramWord L 144 8 % 4 = 0 := by
  cases h : P.extraTopkLenBase with
  | none => rw [paramWord_144_zero hpre h, Nat.zero_mod]
  | some x =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    obtain ⟨hptr, hal, -⟩ := hb
    exact paramWord_mod4_of (fun k hk => by simpa using hptr k hk) hal

/-- The address of the per-batch length is four-byte aligned: the pointer word is, and the
byte offset `4 * batch` is a multiple of four. -/
theorem paramAddr_mod4 {w : Nat} (h : paramWord L w 8 % 4 = 0) (g : Nat) :
    (paramWord L w 8 + 4 * ctaidY L g) % 2 ^ 64 % 4 = 0 := by
  rw [Nat.mod_mod_of_dvd _ (show 4 ∣ 2 ^ 64 by decide)]
  omega

/-! ## The assumption list at the role's instructions -/

theorem asms_ncLoads_2596 : asms.any (·.ncLoads 2596) = true := by decide +kernel

theorem asms_ncLoads_2601 : asms.any (·.ncLoads 2601) = true := by decide +kernel

theorem paramPointers_localRule_none {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites) :
    Assumptions.paramPointers.localRule L g t op = none := by
  simp [Assumptions.paramPointers, h1, h2]

/-- No assumption of the kernel's list has a local rule for one of the role's integer
instructions. -/
theorem asms_localRule_int {L : Launch} {g : Nat} {t : TState} {i : IntInstr}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites)
    (h3 : t.pc ∉ Assumptions.sharedBitsSites)
    (hp : Assumptions.peerPackRule t (.int i) = none) :
    ∀ a ∈ asms, a.localRule L g t (.int i) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · exact paramPointers_localRule_none h1 h2
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule, h3, hp]
  · rfl

/-- No assumption of the kernel's list has a local rule for the role's moves. -/
theorem asms_localRule_move {L : Launch} {g : Nat} {t : TState} {m : MoveInstr}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites)
    (hdead : Assumptions.deadPackWords t.pc = none) :
    ∀ a ∈ asms, a.localRule L g t (.move m) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · exact paramPointers_localRule_none h1 h2
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule_of_none hdead]
  · rfl

/-- No assumption of the kernel's list has a local rule for the role's branches. -/
theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites) :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · exact paramPointers_localRule_none h1 h2
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-- No assumption of the kernel's list has a local rule for the role's `ld.param`s. -/
theorem asms_localRule_mem {L : Launch} {g : Nat} {t : TState} {a : MemAccess}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites) :
    ∀ b ∈ asms, b.localRule L g t (.mem a) = none := by
  intro b hb
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · exact paramPointers_localRule_none h1 h2
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-! ## The sites -/

/-- The role's event instructions: the two `ld.global.nc` reads of the per-batch lengths, the
named barrier `12` over the whole CTA, and the kernel's `ret`. -/
inductive Site where
  /-- The `topk_length` read (pc 2596, PTX 4805), when its pointer is non-null. -/
  | loadTopk
  /-- The `extra_topk_length` read (pc 2601, PTX 4813), when its pointer is non-null. -/
  | loadExtra
  /-- `barrier.sync 12, 384` (pc 2604, PTX 4819): the named barrier over every thread of the
  CTA (a count of `L.block` is the whole CTA). -/
  | sync
  /-- The kernel's single `ret` (pc 3611, PTX 6676). -/
  | exit
  deriving DecidableEq, Repr

def Site.pc : Site → Nat
  | .loadTopk => Flow.load_41
  | .loadExtra => Flow.load_42
  | .sync => Flow.bar_14
  | .exit => Flow.exit_0

/-- The role's first event: the exit test, then the two null-pointer tests of the length
pointers, decide it. -/
def startSite (L : Launch) (g : Nat) : Site :=
  if geBatch L g then .exit
  else if ptrIsNull L 80 then (if ptrIsNull L 144 then .sync else .loadExtra)
  else .loadTopk

/-- The successor of a state on an event. A length read whose bytes rebuild to no value faults
the thread and the machine stops; the loaded word is dead at the next instruction, so the
successor does not depend on it. -/
def next (L : Launch) : Site → Event → Option (Option Site)
  | .loadTopk, e => match e.kind with
    | .nc _ bs => match rebuild 3 bs with
      | .ok _ => some (some (if ptrIsNull L 144 then .sync else .loadExtra))
      | .error _ => none
    | _ => none
  | .loadExtra, e => match e.kind with
    | .nc _ bs => match rebuild 3 bs with
      | .ok _ => some (some .sync)
      | .error _ => none
    | _ => none
  | .sync, e => match e.kind with
    | .bar _ _ _ => some (some .exit)
    | _ => none
  | .exit, _ => none

/-! ## The value table -/

/-- The registers of the role, as functions of the launch and the thread: the batch `%ctaid.y`
(460), the `param_0` pointer (2991), the words and addresses of the two length reads and the
barrier's id and count. -/
def values (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(460, b32 (ctaidY L g)), (2991, .ptr 64 false (.param (param "0")) 0),
   (920, b32 (paramWord L 0 4)), (66, .pred (geBatch L g)),
   (3015, b64 (paramWord L 80 8)), (3016, b64 (paramWord L 144 8)),
   (67, .pred (ptrIsNull L 80)), (68, .pred (ptrIsNull L 144)),
   (3107, b64 (4 * ctaidY L g)),
   (3106, b64 ((paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (3109, b64 (4 * ctaidY L g)),
   (3108, b64 ((paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (923, b32 12), (924, b32 384)]

def valueOf (L : Launch) (g : Nat) (r : Nat) : Value := ((values L g).lookup r).getD (b32 0)

/-- The registers live at `pc`, valued by the table. -/
def factsAt (L : Launch) (g pc : Nat) : List (Nat × Value) :=
  factsFrom (Flow.live pc) (valueOf L g)

abbrev facts (L : Launch) (g : Nat) (s : Site) : List (Nat × Value) := factsAt L g s.pc

/-- The hand-off facts at the role's entry (pc 2587): the registers live there. -/
abbrev entryFacts (L : Launch) (g : Nat) : List (Nat × Value) := factsAt L g 2587

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "idle_values" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- Evaluate a segment of the role from `h` and close the facts of its end state. -/
syntax "idle_seg" term:max : tactic

macro_rules
  | `(tactic| idle_seg $h) => `(tactic|
      seg_fp $h using
        try idle_values
        all_goals seg_close [paramWord])

/-! ## The code machine -/

/-- The code machine of the role. Its invariant is `True`: the entry facts and the launch's
data decide every step, and which threads run the role is the warpgroup-1 head's business. -/
def code (L : Launch) (g : Nat) : PTX.Flow.Code kernel asms L g where
  D := Site
  init := startSite L g
  pc := Site.pc
  facts := facts L g
  inv := fun _ => True
  next := next L

/-- What one step of the machine owes. -/
abbrev Step (L : Launch) (g : Nat) (s : Site) (u : TState) (e : Event) : Prop :=
  ((code L g).next s e = some none ∨ ∃ d' : Site, ∃ t', (code L g).next s e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code L g).Good (some d') t') ∨
    ((code L g).next s e = none ∧
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-! ## Local steps -/

section
variable {t : TState}

/-- A branch on a test the table states, as one step to the successor's facts. -/
theorem bra_to {pc target p b : Nat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc (factsAt L g pc)) (hp : p ∈ Flow.live pc) (hv : valueOf L g p = .pred pick)
    (hb : b = if pick then target else pc + 1) (hl : ∀ r ∈ Flow.live b, r ∈ Flow.live pc)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b (factsAt L g b) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.bra target false) = none := by
    intro a ha
    exact asms_localRule_bra (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha
  obtain ⟨t', hr, ht⟩ :=
    run_bra (K := kernel) (A := asms) (L := L) (g := g) hc pick h
      (hv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hp)) hL hsf
  rw [← hb] at ht
  exact ⟨t', hr, At.mono ht (holds_factsFrom_mono ht.2.2.2.2 hl)⟩

/-- The `ld.param` access of a by-value parameter object through a 64-bit pointer register. -/
def paramLoad (ty : DType) (off r d : Nat) : MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 1, ext := .same,
    addr := { base := .reg r 64, off := (off : Int) }, dsts := [some d] }

/-- A parameter-space pointer register names a by-value parameter object: `paramObjectOf`
resolves it to the object's name when the access lies inside the object and is aligned. -/
theorem paramObjectOf_ok {L : Launch} {t : TState} {r : Nat} {p : String} {off : Int} {n : Nat}
    {decl : ParamObjectDecl} {base : Nat}
    (hrp : t.regs r = some (.ptr 64 false (.param p) 0))
    (hobj : L.paramObjects p = some (decl, base))
    (ho : 0 ≤ off) (hs : off.toNat + n ≤ decl.bytes)
    (hn : 0 < n) (ha : off.toNat % n = 0) (hal : decl.alignment % n = 0) :
    paramObjectOf L t r off n = .ok p := by
  simp only [paramObjectOf, readReg, hrp, hobj, ho, hs, hn, ha, hal, pure, Except.pure,
    bind, Except.bind, ite_true, and_true]

/-- `ld.param` of one element of a by-value parameter object named by a register: the bytes the
launch supplies, read as `paramNat`. The register base is the parameter-space pointer the
prologue leaves in `%rd2` (`paramObjectOf`). -/
theorem exec_ldParamReg {A : List Assumption} {L : Launch} {g w off r d : Nat} {t : TState}
    {p : String} {ty : DType} {decl : ParamObjectDecl} {base : Nat}
    (hrp : t.regs r = some (.ptr 64 false (.param p) 0))
    (hobj : L.paramObjects p = some (decl, base))
    (hbound : 0 ≤ (off : Int) ∧ off + w / 8 ≤ decl.bytes)
    (halign : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ decl.alignment % (w / 8) = 0)
    (hsup : ParamSupplied L p off (w / 8))
    (hA : Assumption.SegFreePc A t.pc := by seg_free)
    (hL : ∀ b ∈ A, b.localRule L g t (.mem (paramLoad ty off r d)) = none)
    (hw : ty.width = w := by rfl)
    (hr : (paramLoad ty off r d).rule = some .threadMove := by rfl) :
    execLocalA A L g t (.mem (paramLoad ty off r d)) =
      .ok (PTX.next (setReg t d (paramElem w w (paramNat L p off (w / 8))))) := by
  subst hw
  have ho : (off : Int).toNat = off := Int.toNat_natCast off
  have hpo : paramObjectOf L t r (off : Int) (ty.width / 8) = .ok p :=
    paramObjectOf_ok hrp hobj hbound.1 (by simpa using hbound.2) (by simpa using halign.1)
      (by simpa using halign.2.1) (by simpa using halign.2.2)
  have hsup' : ParamSupplied L p off (ty.width / 8 * [d].length) := by simpa using hsup
  have hregs : ([some d].filterMap id) = [d] := rfl
  rw [hA.exec rfl, execLocalRule_of_none hL, execLocal_mem hr]
  simp only [paramLoad, execMove, MemAccess.regs, hregs, Nat.mul_one, hpo, bind, Except.bind,
    ho]
  rw [loadParamObject_eq (ds := [d]) (t := t) (off := off) hsup']
  rfl

/-- A local step that writes the registers `ws` with their table values reaches the next
instruction with the table's facts, when every register live there is written or was live. -/
theorem at_written {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (factsAt L g pc)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, t'.regs r = some (valueOf L g r))
    (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ ws ∨ r ∈ Flow.live pc) :
    At t' (pc + 1) (factsAt L g (pc + 1)) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm
  · rw [hfr r hm]
    rcases hl r hr with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom h')

/-- An `ld.param` of one register of `param_0` through the pointer register 2991, as one step
to the next instruction's facts. -/
theorem ld_obj {pc w off d r : Nat} {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem (paramLoad ty off r d)⟩)
    (hrp : t.regs r = some (.ptr 64 false (.param (param "0")) 0))
    (hobj : L.paramObjects (param "0") = some (scalarsParam, P.param0Base))
    (hsup : ParamSupplied L (param "0") off (w / 8)) (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0) (h : At t pc (factsAt L g pc))
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf L g d)
    (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [d] ∨ x ∈ Flow.live pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (hsf : Assumption.SegFreePc asms pc := by seg_free_pc)
    (hw : ty.width = w := by rfl) (hr : (paramLoad ty off r d).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g (pc + 1)) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (paramLoad ty off r d)) = none := by
    intro b hb
    exact asms_localRule_mem (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) b hb
  refine ⟨_, run_local hc rfl h (exec_ldParamReg hrp hobj ⟨by omega, hsze⟩ hal hsup
    (Assumption.SegFreePc.of_eq h.1 hsf) hL hw hr), at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [setReg, PTX.next, h.1]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [setReg, PTX.next, hv]
  · intro x hx
    simp only [List.mem_singleton] at hx
    simp [setReg, PTX.next, Function.update_of_ne hx]

/-- After a `.nc` load whose bytes rebuild to a value, the thread is at the next instruction
with the table's facts: the loaded register is dead there. -/
theorem at_afterNC {t u : TState} {pc d : Nat} {v : Value}
    (h : At t pc (factsAt L g pc))
    (hu : u = { setReg t d v with pc := t.pc + 1, sub := 0, acc := [] })
    (hdead : d ∉ Flow.live (pc + 1))
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ Flow.live pc) :
    At u (pc + 1) (factsAt L g (pc + 1)) := by
  subst hu
  have hne : ∀ r ∈ Flow.live (pc + 1), r ≠ d := by
    intro r hr he
    exact hdead (he ▸ hr)
  refine ⟨by simp [h.1], rfl, rfl, ?_, holds_of_pointwise fun r hr => ?_⟩
  · simp [setReg]; exact h.2.2.2.1
  · show Function.update t.regs d (some v) r = some (valueOf L g r)
    rw [Function.update_of_ne (hne r hr)]
    exact holds_mem h.2.2.2.2 (mem_factsFrom (hl r hr))

/-! ## The event instructions -/

/-- The `.nc` load instruction of `.loadTopk`: an `s32` word through register 3106 into 921. -/
abbrev ncLoadTopk : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, vec := 1, ext := .same,
    nc := true, addr := { base := .reg 3106 64, off := 0 }, dsts := [some 921] }

/-- The `.nc` load instruction of `.loadExtra`: an `s32` word through register 3108 into 922. -/
abbrev ncLoadExtra : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, vec := 1, ext := .same,
    nc := true, addr := { base := .reg 3108 64, off := 0 }, dsts := [some 922] }

/-- The `topk_length` read is the `ld.global.nc` of the address `topk_length + 4 * batch`, as
the assumption `ncReadOnly` allows it (site 2596). -/
theorem event_loadTopk (hpre : Pre P L mem0) {t : TState}
    (h : At t Site.loadTopk.pc (facts L g .loadTopk)) :
    eventTmpl asms L g t (.mem ncLoadTopk) =
      .readNC { loc := ⟨.global, 0, (paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64⟩, size := 4 }
        (afterLoad t [921]) := by
  have h3106 : t.regs 3106 = some (b64 ((paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf L g) (r := 3106)
      (by table_decide))
    simpa [facts, factsAt, valueOf, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hr : ncLoadTopk.rule = some .threadAccess := by decide
  have hl : ncLoadTopk.locSpace? = some .global := by decide
  have hnc : asms.any (·.ncLoads t.pc) = true := by rw [h.1]; exact asms_ncLoads_2596
  have h1 := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t) (d := 921)
    (base := 3106) (w := 32) (a := (paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)
    h.2.1 h3106 (Nat.mod_lt _ (by decide)) (by decide)
    (paramAddr_mod4 (paramWord_80_mod4 hpre) g) hnc
  have h2 : memTmpl asms L g t ncLoadTopk = loadTmpl asms L g t .global true 32 [921] 3106 0 :=
    memTmpl_direct_weakLoad (A := asms) (L := L) (g := g) (t := t) (a := ncLoadTopk)
      (sp := .global) (base := 3106) (w := 64) hr hl rfl rfl rfl
  show memTmpl asms L g t ncLoadTopk = _
  rw [h2, h1]

/-- The `extra_topk_length` read is the `ld.global.nc` of
`extra_topk_length + 4 * batch`, as the assumption `ncReadOnly` allows it (site 2601). -/
theorem event_loadExtra (hpre : Pre P L mem0) {t : TState}
    (h : At t Site.loadExtra.pc (facts L g .loadExtra)) :
    eventTmpl asms L g t (.mem ncLoadExtra) =
      .readNC { loc := ⟨.global, 0, (paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64⟩, size := 4 }
        (afterLoad t [922]) := by
  have h3108 : t.regs 3108 = some (b64 ((paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf L g) (r := 3108)
      (by table_decide))
    simpa [facts, factsAt, valueOf, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hr : ncLoadExtra.rule = some .threadAccess := by decide
  have hl : ncLoadExtra.locSpace? = some .global := by decide
  have hnc : asms.any (·.ncLoads t.pc) = true := by rw [h.1]; exact asms_ncLoads_2601
  have h1 := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t) (d := 922)
    (base := 3108) (w := 32) (a := (paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)
    h.2.1 h3108 (Nat.mod_lt _ (by decide)) (by decide)
    (paramAddr_mod4 (paramWord_144_mod4 hpre) g) hnc
  have h2 : memTmpl asms L g t ncLoadExtra = loadTmpl asms L g t .global true 32 [922] 3108 0 :=
    memTmpl_direct_weakLoad (A := asms) (L := L) (g := g) (t := t) (a := ncLoadExtra)
      (sp := .global) (base := 3108) (w := 64) hr hl rfl rfl rfl
  show memTmpl asms L g t ncLoadExtra = _
  rw [h2, h1]

/-- The barrier's count word is the block size, so the event is the CTA-wide arrival on the
named barrier `12`: `barrier.sync 12, 384` is `everyone_sync` of the kernel. -/
theorem event_sync (h : At t Site.sync.pc (facts L g .sync)) (hb : L.block = 384) :
    eventTmpl asms L g t (.barSyncN (.reg 923) (.reg 924) false) =
      .bar 12 (PTX.next t) none .sync := by
  have hm := h.2.2.2.2
  have h923 : t.regs 923 = some (b32 12) := by
    have := holds_mem hm (mem_factsFrom (val := valueOf L g) (r := 923) (by table_decide))
    simpa [facts, factsAt, valueOf, PTX.Flow.lookupLit, Option.getD_some] using this
  have h924 : t.regs 924 = some (b32 384) := by
    have := holds_mem hm (mem_factsFrom (val := valueOf L g) (r := 924) (by table_decide))
    simpa [facts, factsAt, valueOf, PTX.Flow.lookupLit, Option.getD_some] using this
  have h12 : readBits L g t 32 (.reg 923) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h923 (by decide)
  have h384 : readBits L g t 32 (.reg 924) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h924 (by decide)
  simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
    show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
    show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hb,
    show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and,
    or_true, reduceCtorEq]

/-! ## The steps of the machine -/

/-- The batch register `%r460` of a state at `pc` where it is live. -/
theorem reg460 {pc : Nat} (h : At t pc (factsAt L g pc)) (hp : 460 ∈ Flow.live pc)
    : t.regs 460 = some (b32 (ctaidY L g)) := by
  have := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf L g) (r := 460) hp)
  simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using this

/-- The `param_0` pointer register `%rd2` of a state at `pc` where it is live. -/
theorem reg2991 {pc : Nat} (h : At t pc (factsAt L g pc)) (hp : 2991 ∈ Flow.live pc) :
    t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
  have := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf L g) (r := 2991) hp)
  simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using this

/-- The `mul.wide.u32` of `%ctaid.y` by four, as one step: the byte offset of the per-batch
length in the pointer array. -/
theorem mul_wide4 {pc d r : Nat}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.mul .wide, .int .u 32, false, [some d],
      [.reg r, .imm 4]⟩⟩) (h : At t pc (factsAt L g pc)) (hr : t.regs r = some (b32 (ctaidY L g)))
    (hv : valueOf L g d = b64 (4 * ctaidY L g))
    (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [d] ∨ x ∈ Flow.live pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (h3 : pc ∉ Assumptions.sharedBitsSites) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt L g (pc + 1)) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.int ⟨.mul .wide, .int .u 32, false, [some d],
      [.reg r, .imm 4]⟩) = none :=
    asms_localRule_int (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2)
      (by rw [h.1]; exact h3) rfl
  have hexec : execLocalA asms L g t (.int ⟨.mul .wide, .int .u 32, false, [some d],
      [.reg r, .imm 4]⟩) = .ok (PTX.next (setReg t d (b64 (4 * ctaidY L g)))) := by
    rw [Assumption.SegFreePc.exec (A := asms) (by seg_free_pc) rfl, execLocalRule_of_none hL,
      execLocal_int rfl]
    have hk : ((DType.int IType.u 32).kind? == some IType.s) = false := rfl
    simp only [execInt, hr, readBits, readReg, b32, hk, bind, Except.bind, pure, Except.pure,
      Bool.false_eq_true, ↓reduceIte]
    refine congrArg (fun v : Value => Except.ok (PTX.next (setReg t d v))) ?_
    have hcy : ctaidY L g < 2 ^ 32 := Nat.mod_lt _ (by decide)
    simp only [b64, Value.bits.injEq, true_and, DType.width, Nat.reduceMul]
    norm_bits
  refine ⟨_, run_local hc rfl h hexec, at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [setReg, PTX.next, h.1]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [setReg, PTX.next, hv]
  · intro x hx
    simp only [List.mem_singleton] at hx
    simp [setReg, PTX.next, Function.update_of_ne hx]
end

/-- The launch supplies the `topk_length` pointer word. -/
theorem supplied_topk (hpre : Pre P L mem0) : ParamSupplied L (param "0") 80 8 := by
  cases h : P.topkLenBase with
  | none =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    obtain ⟨hbytes, -⟩ := hb
    exact fun k hk => ⟨0, hbytes k hk⟩
  | some x =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

/-- The launch supplies the `extra_topk_length` pointer word. -/
theorem supplied_extra (hpre : Pre P L mem0) : ParamSupplied L (param "0") 144 8 := by
  cases h : P.extraTopkLenBase with
  | none =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    obtain ⟨hbytes, -⟩ := hb
    exact fun k hk => ⟨0, hbytes k hk⟩
  | some x =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

/-- The local code after the `topk_length` read: the extra pointer's null test selects the
successor. -/
theorem step_loadTopk (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Site.loadTopk.pc (facts L g .loadTopk))
    (hc : kernel.code[Site.loadTopk.pc]? = some ins)
    (hf : Fires Site.loadTopk.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .loadTopk u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_41)
  rw [event_loadTopk hpre h] at hf
  obtain ⟨bs, -, he, hu⟩ := hf
  have hu' : u = afterLoad t [921] bs := Option.some.inj hu
  cases hrb : rebuild 3 bs with
  | error f =>
    refine Or.inr ⟨?_, Machine.dead_of_fault (f := f) ?_⟩
    · rw [he]; simp [code, next, hrb]
    · rw [hu']; simp [afterLoad, hrb]
  | ok v =>
    have hat : At u 2597 (factsAt L g 2597) := by
      rw [hu', afterLoad_ok h.2.1 h.2.2.1 hrb]
      exact at_afterNC h rfl (by table_decide) (by table_decide)
    obtain ⟨t1, hr1, h1⟩ :
        ∃ t1, run kernel asms L g 1 u = some t1 ∧ At t1 2598 (factsAt L g 2598) := by
      idle_seg hat
    cases hx : ptrIsNull L 144
    · -- the extra pointer is null: the barrier follows
      obtain ⟨t2, hr2, h2⟩ := bra_to (pc := 2598) (target := 2602) (p := 68)
        (pick := ptrIsNull L 144) Flow.code_2598 h1 (by table_decide) (by idle_values)
        (b := 2599) (by rw [hx]; decide) (by table_decide) (by decide) (by decide)
      obtain ⟨tw, hrw, hw⟩ : ∃ tw, run kernel asms L g 1 t2 = some tw ∧
          At tw 2600 (factsAt L g 2600) :=
        mul_wide4 (pc := 2599) (d := 3109) (r := 460) Flow.code_2599 h2
          (reg460 h2 (by table_decide)) (by idle_values) (by table_decide) (by decide)
          (by decide) (by decide)
      obtain ⟨t3, hr3, h3⟩ :
          ∃ t3, run kernel asms L g 1 tw = some t3 ∧ At t3 2601 (factsAt L g 2601) := by
        idle_seg hw
      have hc := run_comp hr1 hr2
      have hc := run_comp hc hrw
      have hc := run_comp hc hr3
      refine Or.inl (Or.inr ⟨.loadExtra, t3, ?_, run_rtg hc, ⟨h3, trivial⟩⟩)
      rw [he]
      simp [code, next, hrb, hx]
    · obtain ⟨t2, hr2, h2⟩ := bra_to (pc := 2598) (target := 2602) (p := 68)
        (pick := ptrIsNull L 144) Flow.code_2598 h1 (by table_decide) (by idle_values)
        (b := 2602) (by rw [hx]; decide) (by table_decide) (by decide) (by decide)
      obtain ⟨t3, hr3, h3⟩ :
          ∃ t3, run kernel asms L g 2 t2 = some t3 ∧ At t3 2604 (factsAt L g 2604) := by
        idle_seg h2
      refine Or.inl (Or.inr ⟨.sync, t3, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3),
        ⟨h3, trivial⟩⟩)
      rw [he]
      simp [code, next, hrb, hx]

/-- The local code after the `extra_topk_length` read: the barrier. -/
theorem step_loadExtra (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Site.loadExtra.pc (facts L g .loadExtra))
    (hc : kernel.code[Site.loadExtra.pc]? = some ins)
    (hf : Fires Site.loadExtra.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .loadExtra u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_42)
  rw [event_loadExtra hpre h] at hf
  obtain ⟨bs, -, he, hu⟩ := hf
  have hu' : u = afterLoad t [922] bs := Option.some.inj hu
  cases hrb : rebuild 3 bs with
  | error f =>
    refine Or.inr ⟨?_, Machine.dead_of_fault (f := f) ?_⟩
    · rw [he]; simp [code, next, hrb]
    · rw [hu']; simp [afterLoad, hrb]
  | ok v =>
    have hat : At u 2602 (factsAt L g 2602) := by
      rw [hu', afterLoad_ok h.2.1 h.2.2.1 hrb]
      exact at_afterNC h rfl (by table_decide) (by table_decide)
    obtain ⟨t1, hr1, h1⟩ :
        ∃ t1, run kernel asms L g 2 u = some t1 ∧ At t1 2604 (factsAt L g 2604) := by
      idle_seg hat
    refine Or.inl (Or.inr ⟨.sync, t1, ?_, run_rtg hr1, ⟨h1, trivial⟩⟩)
    rw [he]
    simp [code, next, hrb]

/-- After the barrier the thread returns at the kernel's single `ret`. -/
theorem step_sync (hpre : Pre P L mem0) {t u : TState} {e : Event} {ins : Instr}
    (h : At t Site.sync.pc (facts L g .sync))
    (hc : kernel.code[Site.sync.pc]? = some ins)
    (hf : Fires Site.sync.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .sync u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_14)
  rw [event_sync h hpre.block] at hf
  obtain ⟨he, hu⟩ := hf
  have hu' : u = PTX.next t := Option.some.inj hu
  obtain ⟨t1, hr1, h1⟩ :
      ∃ t1, run kernel asms L g 1 u = some t1 ∧ At t1 3611 (factsAt L g 3611) := by
    rw [hu']
    idle_seg (At.next h)
  refine Or.inl (Or.inr ⟨.exit, t1, ?_, run_rtg hr1, ⟨h1, trivial⟩⟩)
  rw [he]
  simp [code, next]

/-- The `ret` has no continuing event. -/
theorem step_exit {t u : TState} {e : Event} {ins : Instr}
    (_h : At t Site.exit.pc (facts L g .exit))
    (hc : kernel.code[Site.exit.pc]? = some ins)
    (hf : Fires Site.exit.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g .exit u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  obtain ⟨-, hu⟩ := hf
  exact absurd hu (by simp)

/-! ## The machine's obligations -/

/-- Each site is an event instruction with its guard, and every continuing event of a site
reaches its successor's facts. -/
theorem stepAt (hpre : Pre P L mem0) (d : Site) : (code L g).StepAt d := by
  constructor
  · intro _
    cases d with
    | loadTopk => exact ⟨_, Flow.code_load_41, rfl, trivial⟩
    | loadExtra => exact ⟨_, Flow.code_load_42, rfl, trivial⟩
    | sync => exact ⟨_, Flow.code_bar_14, rfl, trivial⟩
    | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩
  · intro t e u ins h _ hc hf
    cases d with
    | loadTopk => exact step_loadTopk hpre h hc hf
    | loadExtra => exact step_loadExtra hpre h hc hf
    | sync => exact step_sync hpre h hc hf
    | exit => exact step_exit h hc hf

/-- Every site's obligations, as `Code.Sound.steps`. -/
theorem steps (hpre : Pre P L mem0) : ∀ d : Site, (code L g).StepAt d :=
  stepAt hpre

/-! ## The entry and the machine's soundness -/

/-- The hand-off state of the role: thread `t` is about to execute the instruction at pc 2587,
with the two registers live there. The prologue and the warpgroup-1 head must supply it
(`Prologue.values` gives exactly these two values at pc 2587). -/
structure Entry (L : Launch) (g : Nat) (t : TState) : Prop where
  pc : t.pc = 2587
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  regs : Holds t.regs (entryFacts L g)

theorem Entry.at {L : Launch} {g : Nat} {t : TState} (h : Entry L g t) :
    At t 2587 (entryFacts L g) :=
  ⟨h.pc, h.sub, h.acc, h.fault, h.regs⟩

/-- The local prefix from the hand-off reaches the machine's first event. -/
theorem start_of_entry (hpre : Pre P L mem0) {t : TState} (hentry : Entry L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code L g).AtD (code L g).init t' ∧ (code L g).inv (code L g).init := by
  have h0 : At t 2587 (factsAt L g 2587) := hentry.at
  obtain ⟨t1, hr1, h1⟩ := ld_obj (pc := 2587) (w := 32) (off := 0) (d := 920) (r := 2991)
    (ty := .int .b 32) Flow.code_2587 (reg2991 h0 (by table_decide)) hpre.param0Object
    (fun k hk => ⟨_, hpre.paramB k hk⟩) (by decide) (by decide) h0
    (by rw [paramElem_of_ne (by decide)]; rfl) (by table_decide) (by decide) (by decide)
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2589 (factsAt L g 2589) := by
    idle_seg h1
  cases hg : geBatch L g
  case true =>
    obtain ⟨t3, hr3, h3⟩ := bra_to (pc := 2589) (target := 3611) (p := 66)
      (pick := geBatch L g) Flow.code_2589 h2 (by table_decide) (by idle_values)
      (b := 3611) (by rw [hg]; decide) (by table_decide) (by decide) (by decide)
    have hc := run_comp hr1 hr2
    have hc := run_comp hc hr3
    refine ⟨t3, run_rtg hc, ?_, trivial⟩
    rw [show (code L g).init = .exit by
      show startSite L g = .exit
      simp [startSite, hg]]
    exact h3
  case false =>
    obtain ⟨t3, hr3, h3⟩ := bra_to (pc := 2589) (target := 3611) (p := 66)
      (pick := geBatch L g) Flow.code_2589 h2 (by table_decide) (by idle_values)
      (b := 2590) (by rw [hg]; decide) (by table_decide) (by decide) (by decide)
    obtain ⟨t4, hr4, h4⟩ := ld_obj (pc := 2590) (w := 64) (off := 80) (d := 3015) (r := 2991)
      (ty := .int .b 64) Flow.code_2590 (reg2991 h3 (by table_decide)) hpre.param0Object
      (supplied_topk hpre) (by decide) (by decide) h3
      (by rw [paramElem_of_ne (by decide)]; rfl) (by table_decide) (by decide) (by decide)
    obtain ⟨t5, hr5, h5⟩ := ld_obj (pc := 2591) (w := 64) (off := 144) (d := 3016)
      (r := 2991) (ty := .int .b 64) Flow.code_2591 (reg2991 h4 (by table_decide))
      hpre.param0Object (supplied_extra hpre) (by decide) (by decide) h4
      (by rw [paramElem_of_ne (by decide)]; rfl) (by table_decide) (by decide) (by decide)
    obtain ⟨t6, hr6, h6⟩ : ∃ t6, run kernel asms L g 1 t5 = some t6 ∧
        At t6 2593 (factsAt L g 2593) := by
      idle_seg h5
    have hc := run_comp hr1 hr2
    have hc := run_comp hc hr3
    have hc := run_comp hc hr4
    have hc := run_comp hc hr5
    have hc := run_comp hc hr6
    cases ht : ptrIsNull L 80
    case false =>
      obtain ⟨t7, hr7, h7⟩ := bra_to (pc := 2593) (target := 2597) (p := 67)
        (pick := ptrIsNull L 80) Flow.code_2593 h6 (by table_decide) (by idle_values)
        (b := 2594) (by rw [ht]; decide) (by table_decide) (by decide) (by decide)
      obtain ⟨t8, hr8, h8⟩ := mul_wide4 (pc := 2594) (d := 3107) (r := 460) Flow.code_2594
        h7 (reg460 h7 (by table_decide)) (by idle_values) (by table_decide) (by decide)
        (by decide) (by decide)
      obtain ⟨t9, hr9, h9⟩ : ∃ t9, run kernel asms L g 1 t8 = some t9 ∧
          At t9 2596 (factsAt L g 2596) := by
        idle_seg h8
      have hc := run_comp hc hr7
      have hc := run_comp hc hr8
      have hc := run_comp hc hr9
      refine ⟨t9, run_rtg hc, ?_, trivial⟩
      rw [show (code L g).init = .loadTopk by
        show startSite L g = .loadTopk
        simp [startSite, hg, ht]]
      exact h9
    case true =>
      obtain ⟨t7, hr7, h7⟩ := bra_to (pc := 2593) (target := 2597) (p := 67)
        (pick := ptrIsNull L 80) Flow.code_2593 h6 (by table_decide) (by idle_values)
        (b := 2597) (by rw [ht]; decide) (by table_decide) (by decide) (by decide)
      obtain ⟨t8, hr8, h8⟩ : ∃ t8, run kernel asms L g 1 t7 = some t8 ∧
          At t8 2598 (factsAt L g 2598) := by
        idle_seg h7
      have hc := run_comp hc hr7
      have hc := run_comp hc hr8
      cases he : ptrIsNull L 144
      case false =>
        obtain ⟨t9, hr9, h9⟩ := bra_to (pc := 2598) (target := 2602) (p := 68)
          (pick := ptrIsNull L 144) Flow.code_2598 h8 (by table_decide) (by idle_values)
          (b := 2599) (by rw [he]; decide) (by table_decide) (by decide) (by decide)
        obtain ⟨t10, hr10, h10⟩ := mul_wide4 (pc := 2599) (d := 3109) (r := 460)
          Flow.code_2599 h9 (reg460 h9 (by table_decide)) (by idle_values) (by table_decide)
          (by decide) (by decide) (by decide)
        obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 1 t10 = some t11 ∧
            At t11 2601 (factsAt L g 2601) := by
          idle_seg h10
        have hc := run_comp hc hr9
        have hc := run_comp hc hr10
        have hc := run_comp hc hr11
        refine ⟨t11, run_rtg hc, ?_, trivial⟩
        rw [show (code L g).init = .loadExtra by
          show startSite L g = .loadExtra
          simp [startSite, hg, ht, he]]
        exact h11
      case true =>
        obtain ⟨t9, hr9, h9⟩ := bra_to (pc := 2598) (target := 2602) (p := 68)
          (pick := ptrIsNull L 144) Flow.code_2598 h8 (by table_decide) (by idle_values)
          (b := 2602) (by rw [he]; decide) (by table_decide) (by decide) (by decide)
        obtain ⟨t10, hr10, h10⟩ : ∃ t10, run kernel asms L g 2 t9 = some t10 ∧
            At t10 2604 (factsAt L g 2604) := by
          idle_seg h9
        have hc := run_comp hc hr9
        have hc := run_comp hc hr10
        refine ⟨t10, run_rtg hc, ?_, trivial⟩
        rw [show (code L g).init = .sync by
          show startSite L g = .sync
          simp [startSite, hg, ht, he]]
        exact h10

/-- **The machine's obligations.** The `start` field is the part of `Code.Sound` that a role
cannot prove on its own: it asks for a thread run from `{}` to the machine's first event, which
crosses the prologue's events. `start_of_entry` supplies the role's own part of it (the local
prefix from the hand-off at pc 2587), and `sound_of_entry` composes the two. -/
theorem sound (hpre : Pre P L mem0)
    (hstart : ∃ t, Relation.ReflTransGen (Tau kernel asms L g) {} t ∧
      (code L g).AtD (code L g).init t ∧ (code L g).inv (code L g).init) :
    (code L g).Sound :=
  ⟨hstart, steps hpre⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread
