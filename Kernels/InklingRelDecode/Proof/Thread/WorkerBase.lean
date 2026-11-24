-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderBase

@[expose] public section

/-! # Helpers of the worker's step lemmas

Three facts the loader's helpers (`LoaderBase`) do not give. A guarded instruction whose guard
is false is skipped (the worker's prologue passes `tcgen05.alloc` and
`tcgen05.relinquish_alloc_permit`, which only the first warp executes), a branch under the
negation of a predicate (`@!%p4 bra`), and the event of a load with an extension (the role
byte is read by `ld.shared.b8` into a 32-bit register, zero-extended: Table 28 of the manual),
which `Lemmas/Flow/Next.lean` states only for loads without one. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- After a load with an extension that `accessLoc` locates, the thread is in
`afterAccessLoad` for the bytes read. -/
theorem fires_load_ext {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {a : MemAccess} {pc : Nat} {e : Event} (hk : a.kind = .load) (hnc : a.nc = false)
    (hl : a.locSpace? = none)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
  have hnotAtomic : a.rule ≠ some .threadAtomic := by
    rw [MemAccess.rule, hk]
    repeat' split
    all_goals simp_all
  have hacc : Fires pc (accessTmpl A L g t a) e (some u) → ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧
      u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
    intro hf
    rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
      ⟨r, k, hn, -⟩
    · rw [h] at hf
      exact absurd hf.2 (by simp)
    · rw [h] at hf
      obtain ⟨bs, -, rfl, hu⟩ := hf
      exact ⟨_, bs, rfl, Option.some.inj hu⟩
    · simp [hnc] at hn
  simp only [eventTmpl, memTmpl, hl] at hf
  split at hf
  · rename_i r sp ab hr hloc hbase
    simp at hloc
  · rename_i hrule
    exact absurd hrule hnotAtomic
  · split at hf
    · exact hacc hf
    · exact absurd hf.2 (by simp)

/-- A guarded instruction whose guard is false is skipped: one step, every fact kept. -/
theorem run_skip {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc p : Nat} {neg : Bool} {op : Op} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, neg), op⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick)) (hg : (pick != neg) = false) :
    ∃ u, run K A L g 1 t = some u ∧ At u (pc + 1) F := by
  refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, hg, bind, Except.bind,
    pure, Except.pure]

/-- A branch under the negation of a predicate fact keeps every register fact. -/
theorem run_bra_neg {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick))
    (hL : ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ u, run K A L g 1 t = some u ∧ At u (if pick then pc + 1 else target) F := by
  cases pick with
  | true =>
    exact run_skip hc true h hp rfl
  | false =>
    refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal]

/-- An unguarded `brx.idx` on a register holding a 32-bit word takes the entry of its table at
the word's index; every register fact is kept. -/
theorem run_brx {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc r target k : Nat} {targets : List Nat} {uni : Bool} {F : List (Nat × Value)}
    {x : BitVec 64}
    (hc : K.code[pc]? = some ⟨none, .brx (.reg r) targets uni⟩) (h : At t pc F)
    (hp : t.regs r = some (.bits 32 x)) (hk : (truncBits 32 x).toNat = k)
    (ht : targets[k]? = some target)
    (hL : ∀ a ∈ A, a.localRule L g t (.brx (.reg r) targets uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ u, run K A L g 1 t = some u ∧ At u target F := by
  refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
    Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal,
    readBits, hk, ht]

namespace Seg
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A guarded instruction whose guard fact is false, as a one-step piece. -/
theorem skip {pc p : Nat} {neg pick : Bool} {op : Op} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, neg), op⟩) (hp : (p, Value.pred pick) ∈ F)
    (hg : (pick != neg) = false) : Seg K A L g 1 pc F (pc + 1) F :=
  fun _ h => run_skip hc pick h (holds_mem h.2.2.2.2 hp) hg

/-- A branch under the negation of a predicate fact, as a one-step piece. -/
theorem bra_neg {pc target p : Nat} {uni pick : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : (p, Value.pred pick) ∈ F)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (if pick then pc + 1 else target) F :=
  fun t h => run_bra_neg hc pick h (holds_mem h.2.2.2.2 hp) (hL t h.1) hA

/-- An unguarded `brx.idx` on a register fact holding a 32-bit word, as a one-step piece. -/
theorem brx {pc r target k : Nat} {targets : List Nat} {uni : Bool} {F : List (Nat × Value)}
    {x : BitVec 64} (hc : K.code[pc]? = some ⟨none, .brx (.reg r) targets uni⟩)
    (hp : (r, Value.bits 32 x) ∈ F) (hk : (truncBits 32 x).toNat = k)
    (ht : targets[k]? = some target)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.brx (.reg r) targets uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F target F :=
  fun t h => run_brx hc h (holds_mem h.2.2.2.2 hp) hk ht (hL t h.1) hA

end Seg

end

end PTX.Flow
