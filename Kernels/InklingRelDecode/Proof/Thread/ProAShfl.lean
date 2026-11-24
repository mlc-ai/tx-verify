-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProABase

@[expose] public section

/-! # The bit of a received word (`and.b32 %r, %rRecv, 1`)

Each broadcast of the warp index in the prologue (`psh0` … `psh2`) writes the received word to its
register as the shuffle returned it (`Dat.sh0` …), and the first instruction after the election
that follows reads it: `and.b32 %r234, %r232, 1` (pc 206, 247, 289). The segment evaluator reads
only literal registers, so this one instruction is proved here: a word that reads as the 32-bit
number `m` (`Raw.word32Of`) gives the table's value `wAnd32 (ofNat m) 1` (`seg_and1`), and a word
without bits faults (`dead_and1`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- `shW` of a word that reads as `m`. -/
theorem shW_of {v : Value} {m : Nat} (h : Raw.word32Of v = some m) : shW v = m := by
  simp [shW, h]

/-- `shW` is a 32-bit number. -/
theorem shW_lt (v : Value) : shW v < 2 ^ 32 := by
  unfold shW
  cases h : Raw.word32Of v with
  | none => simp
  | some m => simpa using Raw.word32Of_lt h

/-- **The bit of a received word that reads as `m`**: one step from the facts `F` (which hold
the word in `src`) to the facts `G` after the write of `wAnd32 (ofNat m) 1` to `dst`. -/
theorem seg_and1 {pc src dst : Nat} {F G : List (Nat × Value)} {v : Value} {m : Nat}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some dst],
      [.reg src, .imm 1]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hv : (src, v) ∈ F) (hw : Raw.word32Of v = some m)
    (hG : ∀ R, Holds R F → Holds (Function.update R dst
      (some (.bits 32 (wAnd32 (BitVec.ofNat 64 m) (BitVec.ofInt 64 1))))) G) :
    Seg kernel asms L g 1 pc F (pc + 1) G := by
  refine Raw.seg_int1 (d := dst) hc rfl rfl hsf (fun t h => ?_) hG
  have hreg : t.regs src = some v := holds_mem h.2.2.2.2 hv
  have hb := Raw.readBits_word32 (L := L) (g := g) hreg hw
  simp only [execInt, hb, DType.width, bind, Except.bind, pure, Except.pure]
  rfl

/-- **A received word without bits faults** at the `and.b32` that reads it. -/
theorem dead_and1 {pc src dst : Nat} {F : List (Nat × Value)} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some dst],
      [.reg src, .imm 1]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hv : (src, v) ∈ F) (hw : Raw.word32Of v = none)
    {t : TState} (h : At t pc F) :
    Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t := by
  refine Raw.dead_int1 hc rfl rfl hsf (fun t' h' => ?_) h
  obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g) (holds_mem h'.2.2.2.2 hv) hw
  exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩

/-- The received word of the broadcast of block `b`. -/
def shOf (dt : Dat) : Nat → Value
  | 0 => dt.sh0
  | 1 => dt.sh1
  | _ => dt.sh2

/-- **The half of the K/V preload that block `b`'s copies fill**: bit 0 of the word its broadcast
of the warp index received. -/
def half (dt : Dat) (b : Nat) : Nat := shW (shOf dt b) % 2

theorem half_lt (dt : Dat) (b : Nat) : half dt b < 2 := Nat.mod_lt _ (by omega)

theorem shW_bit (v : Value) : (shW v % 2 ^ 32) &&& (1 % 2 ^ 32) = shW v % 2 := by
  rw [Nat.mod_eq_of_lt (shW_lt v), Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32), Nat.and_one_is_mod]

/-- The election after the broadcast of block `b`. -/
def pelSite : Nat → Site
  | 0 => .pel0_0
  | 1 => .pel1_0
  | _ => .pel2_0

/-- The state is the election after a broadcast whose received word has no bits: the `and.b32`
after the election faults. -/
def PelDead (d : D) : Prop := ∃ b < 3, d.site = pelSite b ∧ Raw.word32Of (shOf d.dt b) = none

/-- A step of the prologue: `Step`, or the event leaves a fault (a received word without bits,
`dead_and1`, at a `PelDead` state), where the machine's successor is `none`, or the event leads
into the fault of `add.s32 %r30, %r2, 256` (pc 319) on a base word without an outcome
(`addOk`), where the successor is `none` too. -/
def StepD (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  Step L g d e u ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u ∧
      PelDead d) ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u ∧
      addOk d.dt.w = false)

/-- A step whose successor is gated on the base word (it goes past pc 319 when `c` holds): a
conditional piece (`SegD`) to the successor's site gives a `Step` when the add has an outcome,
and the thread is dead otherwise. -/
theorem stepD_gate {pc : Nat} {F : List (Nat × Value)} {c : Bool} {d d' : D} {e : Event}
    {u : TState} (hn1 : (c = true → addOk d.dt.w = true) → next L g d e = some (some d'))
    (hn2 : c = true → addOk d.dt.w = false → next L g d e = none)
    (hi : Inv L g d') (hs0 : sub d' = 0) (hU : At u pc F)
    (hs : ∃ n, SegD kernel asms L g n pc F d'.site.pc (facts L g d')
      (c = true → addOk d.dt.w = true)) : StepD L g d e u := by
  obtain ⟨n, hs⟩ := hs
  by_cases hc : c = true → addOk d.dt.w = true
  · obtain ⟨t', hr, ht'⟩ := (hs u hU).1 hc
    exact .inl (.inr ⟨d', t', hn1 hc, run_rtg hr,
      ⟨ht'.1, hs0 ▸ ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi⟩)
  · have h1 : c = true := by
      by_contra h
      exact hc fun h' => absurd h' h
    have h2 : addOk d.dt.w = false := by
      cases ha : addOk d.dt.w
      · rfl
      · exact absurd (fun _ => ha) hc
    exact .inr (.inr ⟨hn2 h1 h2, (hs u hU).2 hc, h2⟩)

/-- The facts between an election and the copy it guards: the guard `p` holds `c` (the table
states `true`, the value on the path that issues the copy), the other registers live at `pc` hold
the table's values. -/
def factsX (L : Launch) (g : Nat) (p pc : Nat) (c : Bool) (dt : Dat) : List (Nat × Value) :=
  (p, .pred c) :: Flow.factsFrom ((Flow.live pc).erase p) (valueOf L g dt)

/-- The facts `factsX` after a write of the table's value to a register other than the guard. -/
theorem holds_factsX {R : Nat → Option Value} {p pc pc' d : Nat} {c : Bool} {dt : Dat}
    {x : Value} (h : Holds R (factsX L g p pc c dt)) (hdp : d ≠ p) (hx : valueOf L g dt d = x)
    (hl : ∀ r ∈ (Flow.live pc').erase p, r = d ∨ r ∈ (Flow.live pc).erase p) :
    Holds (Function.update R d (some x)) (factsX L g p pc' c dt) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, Raw.holds_set_live h2 hx hl⟩
  rw [Function.update_of_ne (Ne.symm hdp)]
  exact h1

/-! ### Block 0: `and.pred` (pc 205), the bit (pc 206), the copy registers (pc 207 to 210) -/

theorem seg_205_206 (L : Launch) (g : Nat) (dt : Dat) (a b : Bool) :
    Seg kernel asms L g 1 205 ((59, Value.pred a) :: (58, Value.pred b) :: factsAt L g 205 dt) 206
      (factsX L g 54 206 (a && b) dt) :=
  fun t h => by
    cases a <;> cases b <;> pro_seg h [v_p54]

theorem seg_206_207 (L : Launch) (g : Nat) (dt : Dat) (c : Bool) {m : Nat}
    (hw : Raw.word32Of dt.sh0 = some m) :
    Seg kernel asms L g 1 206 (factsX L g 54 206 c dt) 207 (factsX L g 54 207 c dt) := by
  refine seg_and1 (m := m) (src := 693) (dst := 695) Flow.code_206
    (asms_segFree (by decide +kernel))
    (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel))) ?_
    (fun R hR => holds_factsX hR (by decide) ?_ (by decide +kernel))
  · simpa [valueOf, table, PTX.Flow.lookupLit] using hw
  · simp [valueOf, table, PTX.Flow.lookupLit, v_r234, v_r232, shW_of hw]

theorem seg_207_211_hit (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 4 207 (factsX L g 54 207 true dt) 211 (factsAt L g 211 dt) :=
  fun t h => by
    pro_seg h [v_r235, v_r221, v_r236, v_r222]

theorem seg_207_212_miss (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 5 207 (factsX L g 54 207 false dt) 212 (factsAt L g 212 dt) :=
  fun t h => by
    pro_seg h [v_r235, v_r221, v_r236, v_r222]

/-! ### Block 1: `and.pred` (pc 246), the bit (pc 247), the copy registers (pc 248 to 252) -/

theorem seg_246_247 (L : Launch) (g : Nat) (dt : Dat) (a b : Bool) :
    Seg kernel asms L g 1 246 ((59, Value.pred a) :: (68, Value.pred b) :: factsAt L g 246 dt) 247
      (factsX L g 64 247 (a && b) dt) :=
  fun t h => by
    cases a <;> cases b <;> pro_seg h [v_p64]

theorem seg_247_248 (L : Launch) (g : Nat) (dt : Dat) (c : Bool) {m : Nat}
    (hw : Raw.word32Of dt.sh1 = some m) :
    Seg kernel asms L g 1 247 (factsX L g 64 247 c dt) 248 (factsX L g 64 248 c dt) := by
  refine seg_and1 (m := m) (src := 714) (dst := 716) Flow.code_247
    (asms_segFree (by decide +kernel))
    (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel))) ?_
    (fun R hR => holds_factsX hR (by decide) ?_ (by decide +kernel))
  · simpa [valueOf, table, PTX.Flow.lookupLit] using hw
  · simp [valueOf, table, PTX.Flow.lookupLit, v_r255, v_r253, shW_of hw]

theorem seg_248_253_hit (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 5 248 (factsX L g 64 248 true dt) 253 (factsAt L g 253 dt) :=
  fun t h => by
    pro_seg h [v_r256, v_r257, v_r241, v_r258, v_r242]

theorem seg_248_254_miss (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 6 248 (factsX L g 64 248 false dt) 254 (factsAt L g 254 dt) :=
  fun t h => by
    pro_seg h [v_r256, v_r257, v_r241, v_r258, v_r242]

/-! ### Block 2: `and.pred` (pc 288), the bit (pc 289), the copy registers (pc 290 to 294) -/

theorem seg_288_289 (L : Launch) (g : Nat) (dt : Dat) (a b : Bool) :
    Seg kernel asms L g 1 288 ((59, Value.pred a) :: (77, Value.pred b) :: factsAt L g 288 dt) 289
      (factsX L g 73 289 (a && b) dt) :=
  fun t h => by
    cases a <;> cases b <;> pro_seg h [v_p73]

theorem seg_289_290 (L : Launch) (g : Nat) (dt : Dat) (c : Bool) {m : Nat}
    (hw : Raw.word32Of dt.sh2 = some m) :
    Seg kernel asms L g 1 289 (factsX L g 73 289 c dt) 290 (factsX L g 73 290 c dt) := by
  refine seg_and1 (m := m) (src := 736) (dst := 738) Flow.code_289
    (asms_segFree (by decide +kernel))
    (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel))) ?_
    (fun R hR => holds_factsX hR (by decide) ?_ (by decide +kernel))
  · simpa [valueOf, table, PTX.Flow.lookupLit] using hw
  · simp [valueOf, table, PTX.Flow.lookupLit, v_r277, v_r275, shW_of hw]

theorem seg_290_295_hit (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 5 290 (factsX L g 73 290 true dt) 295 (factsAt L g 295 dt) :=
  fun t h => by
    pro_seg h [v_r278, v_r279, v_r263, v_r280, v_r264]

theorem seg_290_296_miss (L : Launch) (g : Nat) (dt : Dat) :
    Seg kernel asms L g 6 290 (factsX L g 73 290 false dt) 296 (factsAt L g 296 dt) :=
  fun t h => by
    pro_seg h [v_r278, v_r279, v_r263, v_r280, v_r264]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
