-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartStep

@[expose] public section

/-! # The common start's steps: the base word, the second barrier, the relinquishment

The load of the Tensor Memory base word (`step_ld0`: the thread stores the 32-bit word below
`2 ^ 32` it reads in `%r2`; any other value leaves the machine), the second `bar.sync 0`
(`step_bar1`: warp 0 goes on to the relinquishment; the other warps skip it and run
`shr.u32 %r3, %r1, 5`), and the relinquishment (`step_relinq`, then the same `shr.u32`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- `ArgsOk` does not depend on the Tensor Memory base word. -/
theorem argsOk_tm {a b : Nat} (h : ProA.ArgsOk L g (inh L g Q a)) :
    ProA.ArgsOk L g (inh L g Q b) :=
  ⟨h.tid, h.splitsPos, h.splitsRange, h.splitIdx, h.p0, h.p6, h.p8, h.p9, h.p10, h.p11, h.p15,
    h.p16, h.p17, h.p25⟩

/-- The registers of the table other than `%r2` do not depend on the base word. -/
theorem valueOf_tm_ne {a b : Value} {r : Nat}
    (h : r ∈ [3, 462, 464, 465, 528, 529, 530, 531, 532, 534, 1949, 2020]) :
    valueOf L g Q a r = valueOf L g Q b r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem valueOf_463 (tm : Value) : valueOf L g Q tm 463 = tm := rfl

/-- A segment of the machine's code from `pc` with facts `F` to the site of `d'`. -/
abbrev SegTo (L : Launch) (g : Nat) (Q : Params) (pc : Nat) (F : List (Nat × Value)) (d' : D) :
    Prop := ∃ k, Seg kernel asms L g k pc F d'.site.pc (facts L g Q d')

/-- A segment of the machine as a step. -/
theorem step_of_seg {d' : D} {F : List (Nat × Value)} {pc : Nat}
    (hn : next L g d e = some (some d')) (hi : Inv L g Q d') (hs0 : d'.site.sub = 0)
    (hu : At u pc F) (hs : SegTo L g Q pc F d') : Step L g Q d e u := by
  obtain ⟨k, hs⟩ := hs
  obtain ⟨t', hr, ht'⟩ := hs u hu
  exact .inl (.inr ⟨d', t', hn, run_rtg hr,
    ⟨ht'.1, hs0 ▸ ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi⟩)

/-- The table's values at a state, evaluated. -/
macro "ds_values" : tactic =>
  `(tactic| simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none,
    Loader.natOf_b32, Loader.natOf64_b64, Nat.reduceEqDiff, ↓reduceIte])

/-- Close one equation between a computed and a stated register value. -/
syntax "ds_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ds_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | (dsimp only [Loader.baseW, Loader.addW, Loader.rdW]
         all_goals (try simp only [kind_s_beq_s, kind_u_beq_s, kind_b_beq_s, ↓reduceIte]))
      | (simp only [Value.pred.injEq, $extra,*]
         nf_simp [PTX.compare, decide_eq_decide, ne_eq, decide_eq_false_iff_not,
           decide_eq_true_eq]
         omega)
      | seg_close [Loader.natOf_b32, Loader.natOf64_b64, $extra,*]
      | (nf_simp [intBits, intOf, toSigned, Loader.natOf_b32, Loader.natOf64_b64, $extra,*]
         all_goals (try split_ifs)
         all_goals omega))

/-- Evaluate a segment of the machine from `h` and close the facts of its end state. -/
syntax "ds_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ds_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
          Option.getD_none, Loader.natOf_b32, Loader.natOf64_b64, Nat.reduceEqDiff,
          ↓reduceIte, $extra,*]
        all_goals ds_close [$extra,*])

/-! ### The load of the Tensor Memory base word -/

theorem step_ld0 (hs : d.site = .ld0) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess, kernel.code[13]? = some ⟨none, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = [463] :=
    ⟨_, Flow.code_13, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [ha5, afterLoad_ok h.2.1 h.2.2.1 hv]
    refine .inl (.inr ⟨⟨.bar1, v⟩, _, by simp only [next, hv], .refl, ?_,
      ⟨argsOk_tm hi.args, by simp⟩⟩)
    refine ⟨by simp [h.1, Site.pc], rfl, rfl, h.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
    by_cases hr4 : r = 463
    · subst hr4
      simp [valueOf_463, setReg]
    · have hl : r ∈ Flow.live Flow.load_0 := by
        have : ∀ r ∈ Flow.live Flow.bar_1, r = 463 ∨ r ∈ Flow.live Flow.load_0 := by
          table_decide
        exact (this r hr).resolve_left hr4
      have hk : ∀ r ∈ Flow.live Flow.load_0,
          r ∈ [3, 462, 464, 465, 528, 529, 530, 531, 532, 534, 1949, 2020] := by
        table_decide
      have h1 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)
      simp only [setReg, Function.update_of_ne hr4]
      rw [valueOf_tm_ne (hk r hl)] at h1
      exact h1

/-! ### The second barrier and the relinquishment -/

/-- The register `%p3` of a thread outside warp 0 is false. -/
theorem p3_false' {tm : Value} (hl : ¬ g % L.block < 32) :
    (3, Value.pred false) ∈ factsAt L g Q tm 14 :=
  tbl_mem (by live_dec) (by simp [valueOf, table, hl])

/-- `shr.u32 %r3, %r1, 5` (pc 16), from the facts of the barrier or the relinquishment: the
facts of the shuffle's site. -/
theorem seg_shr {tm : Value} (ha : ProA.ArgsOk L g (inh L g Q (ProA.shW tm))) :
    Seg kernel asms L g 1 16 (factsAt L g Q tm 16) 17 (factsAt L g Q tm 17) := by
  intro t h
  have h128 : g % L.block < 128 := ha.tid
  ds_seg h [warpOf]

/-- The second barrier: warp 0 goes on to the relinquishment; the other warps skip it (its
guard `%p3` is false) and run `shr.u32` to the shuffle. -/
theorem step_bar1 (hs : d.site = .bar1) (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  by_cases hl : g % L.block < 32
  · exact step_adv (d' := ⟨.relinq, tm⟩) (by simp [next, hl]) (hi.to _ (by simp [hl])) rfl h
      rfl rfl rfl rfl (by live_dec)
  · have hA : Seg kernel asms L g 1 15 (factsAt L g Q tm 14) 16 (factsAt L g Q tm 14) :=
      Seg.skip Flow.code_15 (p3_false' hl) (by simp)
    have hB := seg_shr (L := L) (g := g) (Q := Q) hi.args
    have hC : Seg kernel asms L g 1 16 (factsAt L g Q tm 14) 17 (factsAt L g Q tm 17) :=
      hB.weaken_start fun _ hR => holds_factsFrom_mono hR (by live_dec)
    exact step_of_seg (d' := ⟨.shfl, tm⟩) (by simp [next, hl]) (hi.to _ (by simp)) rfl
      (At.next (h.at rfl)) ⟨1 + 1, Seg.comp hA hC⟩

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
