-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.WindowEntry

@[expose] public section

/-! # Windows given as lists of intervals

A set `S` of positions (a list of intervals) that local steps enter only from inside (a position
outside `S` has no local step and no skipped guard that lands in it) and never leave, and whose
instructions write no register of `R`: `winOk S R` is a Boolean scan of the code. A state of a lane
at a position of `S` is then reached from a state after an event at a position of `S` or just
before it, and the registers `R` are those of that state (`win_back`, `win_keep`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- The position is in one of the intervals. -/
def inS (S : List (Nat × Nat)) (pc : Nat) : Bool := S.any fun p => decide (p.1 ≤ pc ∧ pc ≤ p.2)

/-- A check of every instruction of the code, in one pass. -/
def scanCode (f : Nat → Instr → Bool) : List Instr → Nat → Bool
  | [], _ => true
  | i :: is, n => f n i && scanCode f is (n + 1)

theorem scanCode_get {f : Nat → Instr → Bool} : ∀ {l : List Instr} {n k : Nat} {ins : Instr},
    scanCode f l n = true → l[k]? = some ins → f (n + k) ins = true
  | [], _, _, _, _, h => by simp at h
  | i :: is, n, 0, ins, h, hk => by
    simp only [scanCode, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact h.1
  | i :: is, n, k + 1, ins, h, hk => by
    simp only [scanCode, Bool.and_eq_true] at h
    have := scanCode_get h.2 (by simpa using hk)
    rwa [show n + 1 + k = n + (k + 1) by omega] at this

/-- The positions a local step of the instruction may land at. -/
def succs (pc : Nat) (op : Op) : List Nat :=
  (match op with
    | .bra tgt _ => [tgt]
    | .brx _ ts _ => (pc + 1) :: ts
    | _ => [pc + 1]) ++ (if Assumptions.emuSites.contains pc then [pc + 11] else [])

/-- **The forward scan**: inside `S` local steps stay in `S`, write no register of `R` (and no
software `exp2` block is inside) and a skipped guard lands in `S`. -/
def fwdOk (S : List (Nat × Nat)) (R : List Nat) : Bool :=
  scanCode (fun pc ins =>
      !inS S pc || ((ins.guard.isNone || inS S (pc + 1)) && (!ins.op.isLocal ||
        ((succs pc ins.op).all (inS S) && R.all (fun r => !(writesRegs ins.op).contains r) &&
          !Assumptions.emuSites.contains pc)))) kernel.code 0

/-- **The entry scan**: outside `S` a local step or a skipped guard lands in `S` only at `lo`. -/
def enterOk (S : List (Nat × Nat)) (lo : Nat) : Bool :=
  scanCode (fun pc ins =>
      inS S pc || ((ins.guard.isNone || !inS S (pc + 1) || pc + 1 == lo) &&
        (!ins.op.isLocal || (succs pc ins.op).all (fun q => !inS S q || q == lo)))) kernel.code 0

/-- **The window scan**: `S` is left by no local step and entered by none (`lo = 0` is no
position of the code that a step reaches: there is none). -/
def winOk (S : List (Nat × Nat)) (R : List Nat) : Bool := fwdOk S R && enterOk S 0

/-- The positions of events whose continuation is in `S` or whose own position is. -/
def eventsOf (S : List (Nat × Nat)) : List Instr → Nat → List Nat
  | [], _ => []
  | i :: is, n => (if !i.op.isLocal && (inS S n || inS S (n + 1)) then [n] else []) ++
      eventsOf S is (n + 1)

/-- The positions of events whose continuation is in `S` or whose own position is. -/
def entryEvents (S : List (Nat × Nat)) : List Nat := eventsOf S kernel.code 0

theorem mem_eventsOf {S} : ∀ {l : List Instr} {n k : Nat} {ins : Instr}, l[k]? = some ins →
    ins.op.isLocal = false → (inS S (n + k) = true ∨ inS S (n + k + 1) = true) →
    n + k ∈ eventsOf S l n
  | [], _, _, _, h, _, _ => by simp at h
  | i :: is, n, 0, ins, h, hl, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [eventsOf, hl, Bool.not_false, Bool.true_and, Bool.or_eq_true,
      List.mem_append]
    exact .inl (by simpa using hs)
  | i :: is, n, k + 1, ins, h, hl, hs => by
    simp only [eventsOf, List.mem_append]
    exact .inr (by
      have := mem_eventsOf (S := S) (n := n + 1) (k := k) (by simpa using h) hl (by
        rwa [show n + 1 + k = n + (k + 1) by omega])
      rwa [show n + 1 + k = n + (k + 1) by omega] at this)

/-- **A local step, by cases**: a skipped guard, or a local instruction landing at one of its
positions and writing only its registers. -/
theorem win_cases {u u1 : TState} (ht : Tau kernel Assumptions.all L g u u1) :
    ∃ ins, kernel.code[u.pc]? = some ins ∧
      u.fault = none ∧
      ((ins.guard.isSome = true ∧ u1.pc = u.pc + 1 ∧ ∀ r, u1.regs r = u.regs r) ∨
       (ins.op.isLocal = true ∧ u1.pc ∈ succs u.pc ins.op ∧
        ∀ r, r ∉ writesRegs ins.op → (Assumptions.emuSites.contains u.pc = true → r ∉ emuW u.pc) →
          u1.regs r = u.regs r)) := by
  unfold Tau out at ht
  cases hf : u.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[u.pc]? with
    | none => simp [hc] at ht
    | some ins =>
      simp only [hc] at ht
      refine ⟨ins, rfl, rfl, ?_⟩
      cases hg : guardHolds u ins.guard with
      | error e => simp [hg] at ht
      | ok b =>
        simp only [hg] at ht
        cases b with
        | false =>
          simp only [Out.tau.injEq] at ht
          subst ht
          refine .inl ⟨?_, rfl, fun _ => rfl⟩
          cases hq : ins.guard with
          | none => simp [hq, guardHolds, pure, Except.pure] at hg
          | some _ => rfl
        | true =>
          by_cases hl : ins.op.isLocal = true
          · simp only [hl, ↓reduceIte] at ht
            cases he : execLocalA Assumptions.all L g u ins.op with
            | error e => simp [he] at ht
            | ok t' =>
              simp only [he, Out.tau.injEq] at ht
              subst ht
              refine .inr ⟨hl, ?_, localA_regs he⟩
              rcases localA_pc_emu he with (h | h) | ⟨h, hs⟩
              · cases hop : ins.op <;> simp_all [succs, nextPc]
              · cases hop : ins.op <;> simp_all [succs, BrxTarget]
              · rw [h]
                exact List.mem_append_right _ (by simp; exact List.contains_iff_mem.mp hs)
          · simp [hl] at ht

/-- **A local step from inside the window stays inside and keeps the registers `R`.** -/
theorem win_fwd {S R} (hw : fwdOk S R = true) {u u1 : TState}
    (ht : Tau kernel Assumptions.all L g u u1) (h : inS S u.pc = true) :
    inS S u1.pc = true ∧ ∀ r ∈ R, u1.regs r = u.regs r := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases ht
  have := scanCode_get hw hc
  rw [Nat.zero_add] at this
  simp only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.all_eq_true, Option.isNone_iff_eq_none] at this
  obtain ⟨hg, hl⟩ := this
  rcases hk with ⟨hs, hp, hr⟩ | ⟨hl', hp, hr⟩
  · have hs' : ins.guard ≠ none := by simpa [Option.isSome_iff_ne_none] using hs
    exact ⟨by rw [hp]; exact hg.resolve_left hs', fun r _ => hr r⟩
  · rcases hl with hl | ⟨⟨hs, hR⟩, hemu⟩
    · simp [hl'] at hl
    · refine ⟨by simpa using hs _ hp, fun r hrR => hr r ?_ fun hq => absurd
        (List.contains_iff_mem.mp hq) (by simpa using hemu)⟩
      have := hR r hrR
      simpa using this

/-- **Local steps from inside the window stay inside and keep the registers `R`.** -/
theorem win_keep {S R} (hw : fwdOk S R = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (hu : inS S u.pc = true) :
    inS S v.pc = true ∧ ∀ r ∈ R, v.regs r = u.regs r := by
  induction h with
  | refl => exact ⟨hu, fun _ _ => rfl⟩
  | tail _ ht ih =>
    obtain ⟨a, b⟩ := win_fwd hw ht ih.1
    exact ⟨a, fun r hr => (b r hr).trans (ih.2 r hr)⟩

/-- **A local step into the window comes from the window** (or lands at `lo`, from outside). -/
theorem win_back {S lo} (hw : enterOk S lo = true) {u u1 : TState}
    (ht : Tau kernel Assumptions.all L g u u1) (h : inS S u1.pc = true) (hn : inS S u.pc = false) :
    u1.pc = lo := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases ht
  have := scanCode_get hw hc
  rw [Nat.zero_add] at this
  simp only [hn, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.all_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at this
  obtain ⟨hg, hl⟩ := this
  rcases hk with ⟨hs, hp, hr⟩ | ⟨hl', hp, hr⟩
  · rw [hp] at h ⊢
    rcases hg with (hg | hg) | hg
    · simp [hg] at hs
    · rw [hg] at h; cases h
    · exact hg
  · rcases hl with hl | hl
    · simp [hl'] at hl
    · rcases hl _ hp with hq | hq
      · rw [h] at hq; cases hq
      · exact hq

/-- **The first entry into the window** lands at `lo`. -/
theorem first_entry {S lo} (hw : enterOk S lo = true) {u v : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v) (hu : inS S u.pc = false)
    (hv : inS S v.pc = true) : ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) u w ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) w v ∧ w.pc = lo ∧
      inS S w.pc = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rw [hu] at hv; cases hv
  | head ht hr ih =>
    rename_i a b
    by_cases hb : inS S b.pc = true
    · exact ⟨b, .single ht, hr, win_back hw ht hb hu, hb⟩
    · obtain ⟨w, h1, h2, h3, h4⟩ := ih (by simpa using hb)
      exact ⟨w, .head ht h1, h2, h3, h4⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
