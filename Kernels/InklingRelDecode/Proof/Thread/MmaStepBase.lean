-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaSegsLoop
public import Lemmas.Flow.Step.Combinators

@[expose] public section

/-! # The MMA warp's invariant across its control code, and the broadcast test

`Env` and the invariant's loop bounds are extracted from the invariant and the shared window of
the precondition; the invariant after the loop's control code (`inv_iterNext`, `inv_afterQk`);
the step of a broadcast of the warp index and its test of the received word (`stepOk_bcast`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr} {tm0 : Nat} {pro0 : Nat → Value}

theorem pre_shared (hpre : Pre P L mem0) : L.sharedBase + 213340 ≤ 2 ^ 18 := by
  have := hpre.sharedRange
  unfold sharedBytes at this
  omega

/-- A QK or PV site is not before the loop. -/
theorem not_pre_of_qk {s : Site} (h : QkSite s) : ¬ PreSite s := by
  cases s <;> simp_all [QkSite, PreSite]

theorem not_pre_of_pv {s : Site} (h : PvSite s) : ¬ PreSite s := by
  cases s <;> simp_all [PvSite, PreSite]

/-- The shape facts of a loop state. -/
theorem env_of (hpre : Pre P L mem0) (hi : Inv d) (hn : d.n ≤ 2147483646) (hin : d.i ≤ d.n)
    (hs : ¬ PreSite d.site) : Env L d := ⟨pre_shared hpre, hn, by omega, hi.tm, hi.wd hs⟩

/-- A QK site is in an iteration below `num_iters`. -/
theorem env_qk (hpre : Pre P L mem0) (hi : Inv d) (hs : QkSite d.site) :
    Env L d ∧ d.i < d.n :=
  ⟨env_of hpre hi (hi.qk hs).2 (hi.qk hs).1.le (not_pre_of_qk hs), (hi.qk hs).1⟩

/-- A PV site is in an iteration from 1 to `num_iters`. -/
theorem env_pv (hpre : Pre P L mem0) (hi : Inv d) (hs : PvSite d.site) :
    Env L d ∧ 1 ≤ d.i ∧ d.i ≤ d.n :=
  ⟨env_of hpre hi (hi.pv hs).2.2 (hi.pv hs).2.1 (not_pre_of_pv hs), (hi.pv hs).1, (hi.pv hs).2.1⟩

set_option hygiene false in
/-- The word fact of the invariant at a site of the same loop state: from the state's own when
the state is past the loop's entry, vacuous at a site before it. It names the invariant
hypothesis of the step lemmas, `hi`. -/
macro "inv_wd" : tactic => `(tactic| first
  | exact fun _ => hi.wd (fun h => h)
  | (intro h; exact absurd trivial h)
  | (intro _; exact hi.wd (by simp_all [PreSite, QkSite, PvSite]))
  | (intro _; exact hi.wd (not_pre_of_qk (by assumption)))
  | (intro _; exact hi.wd (not_pre_of_pv (by assumption))))

/-- The `barrier.sync 1` clause of the invariant at a site other than `barrier.sync 1`. -/
macro "inv_wd0" : tactic => `(tactic| first
  | exact fun h => by cases h
  | (intro h; simp_all))

set_option hygiene false in
/-- The end-of-loop clause of the invariant at a site of the same loop state: vacuous at a site
that is not after the loop, the state's own after it. It names the invariant hypothesis `hi`. -/
macro "inv_fin0" : tactic => `(tactic| first
  | exact fun h => False.elim h
  | exact fun _ => hi.fin0 trivial)

/-- The invariant at another site of the same loop state. -/
theorem inv_site (hi : Inv d) (s : Site) (h0 : PreSite s → d.i = 0)
    (hq : QkSite s → d.i < d.n ∧ d.n ≤ 2147483646)
    (hp : PvSite s → 1 ≤ d.i ∧ d.i ≤ d.n ∧ d.n ≤ 2147483646)
    (hw : ¬ PreSite s → Raw.word32Of (d.pro 471) = some d.n := by inv_wd)
    (hw0 : s = .bar0 → ∀ m, Raw.word32Of (d.pro 471) = some m → m = d.n := by inv_wd0)
    (hf0 : EndSite s → d.i = 0 → d.n = 0 ∨ 2147483646 < d.n := by inv_fin0) :
    Inv { d with site := s } :=
  ⟨hi.n, hi.tm, hi.col, h0, hq, hp, hw, hw0, hf0⟩

/-- A site that is neither before the loop nor in it. -/
theorem inv_far (hi : Inv d) (s : Site) (h0 : ¬ PreSite s) (hq : ¬ QkSite s) (hp : ¬ PvSite s)
    (hd : ¬ PreSite d.site := by exact fun h => h)
    (hb : s ≠ .bar0 := by exact fun h => by cases h)
    (hf0 : EndSite s → d.i = 0 → d.n = 0 ∨ 2147483646 < d.n := by inv_fin0) :
    Inv { d with site := s } :=
  inv_site hi s (fun h => absurd h h0) (fun h => absurd h hq) (fun h => absurd h hp)
    (fun _ => hi.wd hd) (fun h => absurd h hb) hf0

theorem SegE.rtg {s b : Nat} {F G : List (Nat × Value)} (hs : SegE L g s F b G) (h : At t s F) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧ At t' b G := by
  obtain ⟨n, hn⟩ := hs
  exact hn.rtg h

/-! ### The invariant after the loop's control code -/

theorem inv_iterNext (hi : Inv d) (hn : d.n ≤ 2147483646) (hin : d.i ≤ d.n)
    (hd : ¬ PreSite d.site) : Inv (iterNext d) := by
  have hw := hi.wd hd
  by_cases he : d.i = d.n
  · rw [iterNext_fin he]
    exact ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun h => False.elim h, fun h => False.elim h,
      fun _ => hw, (fun h => by cases h), fun _ h => absurd h (Nat.succ_ne_zero _)⟩
  · by_cases hq : d.i + 1 < d.n
    · rw [iterNext_qk he hq]
      exact ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun _ => ⟨hq, hn⟩, fun h => False.elim h,
        fun _ => hw, (fun h => by cases h), fun h => False.elim h⟩
    · rw [iterNext_pv he hq]
      refine ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun h => False.elim h, fun _ => ?_,
        fun _ => hw, (fun h => by cases h), fun h => False.elim h⟩
      show 1 ≤ d.i + 1 ∧ d.i + 1 ≤ d.n ∧ d.n ≤ 2147483646
      omega

theorem inv_afterQk (hi : Inv d) (hn : d.n ≤ 2147483646) (hlt : d.i < d.n)
    (hd : ¬ PreSite d.site) : Inv (afterQk d) := by
  by_cases h0 : d.i = 0
  · rw [afterQk_zero h0]
    exact inv_iterNext hi hn hlt.le hd
  · rw [afterQk_pos h0]
    refine ⟨hi.n, hi.tm, hi.col, fun h => False.elim h, fun h => False.elim h, fun _ => ?_,
      fun _ => hi.wd hd, (fun h => by cases h), fun h => False.elim h⟩
    show 1 ≤ d.i ∧ d.i ≤ d.n ∧ d.n ≤ 2147483646
    omega

/-! ### The test of the broadcast word -/

/-- **The test of a received word** `v` that reads as the 32-bit number `m` (`setp.ne.b32 %p, %r,
7` at `pc`, after the broadcast at `pc - 1` wrote `v` to `%r`): the predicate is `m ≠ 7`, and the
facts are those of a state at the barrier after it, at a site whose test predicate is that
value. -/
theorem s_bcastTest {pc p r : Nat} {s : Site} {v : Value} {m : Nat}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32, false, [some p],
      [.reg r, .imm 7]⟩⟩)
    (hsf : Assumption.SegFreePc asms pc) (hw : Raw.word32Of v = some m)
    (hp : valueOf L { d with site := s } p = .pred (decide (m ≠ 7)))
    (hl : ∀ q ∈ Flow.live (pc + 1), q = p ∨ (q ∈ Flow.live (pc - 1) ∧ q ≠ 8 ∧ q ≠ 13)) :
    SegE L g pc ((r, v) :: factsAt L (pc - 1) d) (pc + 1)
      (factsAt L (pc + 1) { d with site := s }) := by
  refine ⟨1, Raw.seg_int1 (d := p) (v := .pred (decide (m ≠ 7))) hc rfl rfl hsf
    (fun t h => ?_) (fun R hR => ?_)⟩
  · have hreg : t.regs r = some v := holds_mem h.2.2.2.2 (List.mem_cons_self ..)
    have hb := Raw.readBits_word32 (L := L) (g := g) hreg hw
    have hm := Raw.word32Of_lt hw
    simp only [execInt, hb, DType.width, bind, Except.bind, pure, Except.pure]
    simp only [readBits, PTX.compare, DType.kind?, truncBits, pure, Except.pure,
      BitVec.toNat_ofNat, BitVec.toNat_ofInt, Option.getD_some]
    congr 4
    simp only [decide_eq_decide]
    omega
  · refine Flow.holds_of_pointwise fun q hq => ?_
    by_cases hqp : q = p
    · subst hqp
      simp [hp]
    · rcases hl q hq with h | ⟨h1, h8, h13⟩
      · exact absurd h hqp
      · rw [Function.update_of_ne hqp, valueOf_site L d s h8 h13]
        exact holds_mem hR (List.mem_cons_of_mem _ (Flow.mem_factsFrom h1))

/-- **A broadcast of the warp index and its test**: the shuffle at `d.site.pc` writes the received
word `v` to `%r`, and `setp.ne.b32 %p, %r, 7` follows. A word without bits faults at the test
(`hnone`); a word that reads as `m` reaches the barrier after the test at the site `sOk` when
`m = 7` and `sSkip` otherwise (`hsome`), whose predicate `%p` is `m ≠ 7` (`hp`). -/
theorem stepOk_bcast {r p : Nat} {sOk sSkip : Site}
    (hc' : kernel.code[d.site.pc]? = some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32),
      [some r], [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩⟩)
    (ht : kernel.code[d.site.pc + 1]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32, false,
      [some p], [.reg r, .imm 7]⟩⟩)
    (hsf : Assumption.SegFreePc asms (d.site.pc + 1))
    (hr : r ∉ Flow.live d.site.pc)
    (hnone : ∀ m av bv cv recv ok, Raw.word32Of recv = none →
      next L g d ⟨m, .shfl .idx av bv cv recv ok⟩ = none)
    (hsome : ∀ m av bv cv recv ok k, Raw.word32Of recv = some k →
      next L g d ⟨m, .shfl .idx av bv cv recv ok⟩ =
        some (some { d with site := if k = 7 then sOk else sSkip }))
    (hpc : ∀ k : Nat, (if k = 7 then sOk else sSkip).pc = d.site.pc + 1 + 1)
    (hp : ∀ k : Nat, valueOf L { d with site := if k = 7 then sOk else sSkip } p =
      .pred (decide (k ≠ 7)))
    (hl : ∀ q ∈ Flow.live (d.site.pc + 1 + 1),
      q = p ∨ (q ∈ Flow.live (d.site.pc + 1 - 1) ∧ q ≠ 8 ∧ q ≠ 13))
    (hinv : Inv d → ∀ k : Nat, Inv { d with site := if k = 7 then sOk else sSkip }) :
    (code asms L g tm0 pro0).StepOk d := by
  refine ⟨fun {t e u} ins h hi hc hf => ?_⟩
  have h : At t d.site.pc (facts L d) := h
  have hc : kernel.code[d.site.pc]? = some ins := hc
  have hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  have h1 := At.set (r := r) (v := recv) h (facts_ne hr)
  cases hw : Raw.word32Of recv with
  | none =>
    refine .inr ⟨hnone d.site.pc av bv cv recv ok hw, ?_⟩
    refine Raw.dead_int1 ht rfl rfl hsf (fun t' h' => ?_) h1
    obtain ⟨f, hf⟩ := Raw.readBits_word32_none (L := L) (g := g)
      (holds_mem h'.2.2.2.2 (List.mem_cons_self ..)) hw
    exact ⟨f, by simp only [execInt, hf, DType.width]; rfl⟩
  | some k =>
    have h1' : At (PTX.next (setReg t r recv)) (d.site.pc + 1)
        ((r, recv) :: factsAt L (d.site.pc + 1 - 1) d) := by simpa using h1
    have hs := s_bcastTest (L := L) (g := g) (d := d) (s := if k = 7 then sOk else sSkip) ht hsf
      hw (hp k) hl
    obtain ⟨t', hr', ht'⟩ := hs.rtg h1'
    refine .inl (.inr ⟨_, t', hsome d.site.pc av bv cv recv ok _ hw, hr', ?_, hinv hi k⟩)
    show At t' (if k = 7 then sOk else sSkip).pc (factsAt L (if k = 7 then sOk else sSkip).pc _)
    rw [hpc k]
    exact ht'

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
