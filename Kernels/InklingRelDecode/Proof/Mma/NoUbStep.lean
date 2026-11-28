-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.NoUbLoop
public import Kernels.InklingRelDecode.Proof.Mma.Steps
public import Kernels.InklingRelDecode.Proof.Mma.StepsPaths
import Kernels.InklingRelDecode.Proof.Mma.StepsElect
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Step.AdvancesTc
import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # The strict steps of the MMA warp's sites that leave through scalar spans

The sites `bar0`, the two broadcasts, the barrier crossings, the skips, the commits and the
elections, as strict steps: the loop bound and the base word have bit patterns, the broadcast
word too. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value}
local notation "MC" => (code L g regs w)
local notation "F" => liveFacts L regs w

/-- A site whose event always leads to `dst` through a strict span. -/
theorem crossing_for {d dst : D} {e : Event} {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins)
    (adv : ∀ {t u}, Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e (some u) →
      u = PTX.next t)
    (hn : next L g d e = some (some dst))
    (span : Inv d → SegE L g (d.site.pc + 1) ((MC).facts d) dst.site.pc ((MC).facts dst))
    (inv : Inv d → Inv dst) : (MC).StepFor d e := by
  intro t u ins' ht hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := adv hf
  obtain ⟨s, hτ, hgood⟩ := (span hi).land (C := MC) (d := dst)
    (At.next (Code.at_of_atD ht rfl rfl)) (inv hi) rfl rfl rfl rfl
  exact .inl (.inr ⟨dst, s, hn, hτ, hgood⟩)

/-- An election whose two outcomes continue through strict spans. -/
theorem choose_lane_for {d : D} {p r : Nat} (dest : Bool → D) (e : Event)
    (hc : kernel.code[d.site.pc]? = some ⟨none, .warp ⟨.elect, none, [some r, some p], [],
      some (.imm (-1))⟩⟩) (hr : r ≠ p) (fr : ∀ q ∈ (MC).facts d, q.1 ≠ r)
    (fp : ∀ q ∈ (MC).facts d, q.1 ≠ p)
    (hn : ∀ mask n ld, next L g d ⟨d.site.pc, .elect mask n ld⟩ =
      some (some (dest (laneOf L g == ld))))
    (sp : ∀ b ld, Inv d → SegE L g (d.site.pc + 1) ((p, .pred b) :: (r, b32 ld) :: (MC).facts d)
      (dest b).site.pc ((MC).facts (dest b)))
    (valid : ∀ b, Inv d → Inv (dest b)) : (MC).StepFor d e := by
  intro t u ins ht hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨mk, n, ld, rfl, rfl⟩ := fires_elect hf
  let b := laneOf L g == ld
  let t1 := setReg t r (b32 ld)
  obtain ⟨hpc, hsub, hacc, hfault, hR⟩ := Code.at_of_atD ht rfl rfl
  have h1 : At t1 d.site.pc ((r, b32 ld) :: (MC).facts d) :=
    ⟨hpc, hsub, hacc, hfault, Function.update_self .., holds_update hR fr⟩
  have fresh : ∀ q ∈ (r, b32 ld) :: (MC).facts d, q.1 ≠ p := by
    rintro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact fp q hq
  obtain ⟨s, hτ, hgood⟩ := (sp b ld hi).land (C := MC) (d := dest b)
    (At.set (v := .pred b) h1 fresh) (valid b hi) rfl rfl rfl rfl
  exact .inl (.inr ⟨dest b, s, hn mk n ld, hτ, hgood⟩)

private theorem compare_seven_s {pc r p : Nat} {v : Value} {Fs Gs : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32, false, [some p],
      [.reg r, .imm 7]⟩⟩) (hs : Assumptions.emuSites.contains pc = false) (hr : (r, v) ∈ Fs)
    (hv : v.regBits.isSome)
    (hw : ∀ R, Holds R Fs → Holds (Function.update R p (some (.pred (decide (low v ≠ 7))))) Gs) :
    SegE L g pc Fs (pc + 1) Gs := by
  apply scalarStepS hc rfl rfl hs (r := p) (v := .pred (decide (low v ≠ 7))) _ hw
  intro t hF
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.mp hv
  have hx := readBits_regBits (w := 32) (L := L) (g := g) (holds_mem hF hr) hx'
  have himm : readBits L g t 32 (.imm 7) = .ok 7 := rfl
  simp only [execInt, DType.width, himm, hx, bind, Except.bind, pure, Except.pure]
  rw [show truncBits 32 x = truncBits 32 (v.regBits.getD 0) by rw [hx']; rfl]
  congr 3
  refine congrArg Value.pred (?_ : _ = decide (low v ≠ 7))
  change decide ((low v : Int) ≠ 7) = decide (low v ≠ 7)
  simp only [decide_eq_decide]
  omega

private theorem keep_reg (d : D) (s : Site) {r : Nat} (h8 : r ≠ 8) (h13 : r ≠ 13) :
    valueOf L regs w { d with site := s } r = valueOf L regs w d r := by
  simp only [valueOf, values, D.limit, List.lookup_cons, beq_eq_false_iff_ne.mpr h8,
    beq_eq_false_iff_ne.mpr h13]
  rfl

private theorem broadcast_regs {R : Nat → Option Value} {d : D} {s : Site} {p : Nat} {b : Bool}
    (hR : Holds R (factsFrom (Flow.live d.site.pc) (valueOf L regs w d)))
    (hp : valueOf L regs w {d with site := s} p = .pred b)
    (hl : ∀ r ∈ Flow.live s.pc, r = p ∨ (r ∈ Flow.live d.site.pc ∧ r ≠ 8 ∧ r ≠ 13)) :
    Holds (Function.update R p (some (.pred b)))
      (factsFrom (Flow.live s.pc) (valueOf L regs w {d with site := s})) := by
  apply holds_of_pointwise
  intro r hr
  by_cases he : r = p
  · subst r
    rw [hp, Function.update_self]
  · obtain ⟨hm, h8, h13⟩ := (hl r hr).resolve_left he
    rw [Function.update_of_ne he, keep_reg d s h8 h13]
    exact holds_mem hR (mem_factsFrom hm)

local macro "bcast_facts" : tactic => `(tactic| (
  intro v R hR
  obtain ⟨_, hold⟩ := hR
  by_cases h : low v = 7 <;> simp only [h, ↓reduceIte, ne_eq, not_true_eq_false,
    not_false_eq_true, decide_false, decide_true] <;>
    apply broadcast_regs hold rfl (by dsimp only; decide +kernel)))

/-- A broadcast of the lane-7 word whose received word has a bit pattern. -/
theorem broadcast_for {d : D} {r p : Nat} {yes no : Site} (e : Event)
    (hc : kernel.code[d.site.pc]? = some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32),
      [some r], [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩⟩)
    (htest : kernel.code[d.site.pc + 1]? = some ⟨none, .int ⟨.setp .ne none, .int .b 32,
      false, [some p], [.reg r, .imm 7]⟩⟩)
    (hs : Assumptions.emuSites.contains (d.site.pc + 1) = false)
    (hr : ∀ x ∈ (MC).facts d, x.1 ≠ r)
    (succ : ∀ a b c v ok, next L g d ⟨d.site.pc, .shfl .idx a b c v ok⟩ =
      some (some {d with site := if low v = 7 then yes else no}))
    (hpc : yes.pc = d.site.pc + 2 ∧ no.pc = yes.pc)
    (hw : ∀ v R, Holds R ((r, v) :: (MC).facts d) →
      Holds (Function.update R p (some (.pred (decide (low v ≠ 7)))))
        ((MC).facts {d with site := if low v = 7 then yes else no}))
    (hinv : Inv d → Inv {d with site := yes} ∧ Inv {d with site := no})
    (typed : ∀ a b c v ok, e = ⟨d.site.pc, .shfl .idx a b c v ok⟩ → v.regBits.isSome) :
    (MC).StepFor d e := by
  intro t u ins ht hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨a, b, c, v, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  let dest := ({d with site := if low v = 7 then yes else no} : D)
  have pc : dest.site.pc = d.site.pc + 2 := by
    dsimp only [dest]
    split <;> first | exact hpc.left | exact hpc.right.trans hpc.left
  have valid : Inv dest := by
    dsimp only [dest]
    split <;> first | exact (hinv hi).left | exact (hinv hi).right
  have seg := compare_seven_s (L := L) (g := g) htest hs (List.mem_cons_self ..)
    (typed a b c v ok rfl) (hw v)
  rw [← pc] at seg
  obtain ⟨s, hτ, hgood⟩ := seg.land (C := MC) (d := dest)
    (At.set (Code.at_of_atD ht rfl rfl) hr) valid rfl rfl rfl rfl
  exact .inl (.inr ⟨dest, s, succ a b c v ok, hτ, hgood⟩)

theorem qk_broadcast_for (i : Nat) (v : Value) (e : Event)
    (typed : ∀ a b c x ok, e = ⟨Flow.shfl_13, .shfl .idx a b c x ok⟩ → x.regBits.isSome) :
    (MC).StepFor ⟨.qkShfl, i, v⟩ e := by
  intro t u ins ht hi hc hf
  refine broadcast_for (d := ⟨.qkShfl, i, v⟩) (r := 546) (p := 8)
    (yes := .qkBar2) (no := .qkSkip) e Flow.code_2464 Flow.code_2465
    (show Assumptions.emuSites.contains 2465 = false by decide) (by fact_free)
    (fun _ _ _ _ _ => rfl) ⟨rfl, rfl⟩ ?_ (fun h => ⟨h, h⟩) typed ins ht hi hc hf
  bcast_facts

theorem pv_broadcast_for (i : Nat) (v : Value) (e : Event)
    (typed : ∀ a b c x ok, e = ⟨Flow.shfl_14, .shfl .idx a b c x ok⟩ → x.regBits.isSome) :
    (MC).StepFor ⟨.pvShfl, i, v⟩ e := by
  intro t u ins ht hi hc hf
  refine broadcast_for (d := ⟨.pvShfl, i, v⟩) (r := 563) (p := 13)
    (yes := .pvBar2) (no := .pvSkip) e Flow.code_2512 Flow.code_2513
    (show Assumptions.emuSites.contains 2513 = false by decide) (by fact_free)
    (fun _ _ _ _ _ => rfl) ⟨rfl, rfl⟩ ?_ (fun h => ⟨h, h⟩) typed ins ht hi hc hf
  bcast_facts

variable {Q : Params} {m : Mem0}

theorem bar0_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event) (hv : v.regBits.isSome)
    (hw : w.regBits.isSome) : (MC).StepFor ⟨.bar0, i, v⟩ e := by
  let d : D := ⟨.bar0, i, v⟩
  intro t u ins ht hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2424)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have h0 := At.next (Code.at_of_atD ht rfl rfl)
  have live : F d 2424 = F d 2425 :=
    congrArg (fun rs => factsFrom rs (valueOf L regs w d))
      (by decide : Flow.live 2424 = Flow.live 2425)
  change At _ 2425 (F d 2424) at h0
  rw [live] at h0
  obtain ⟨s, hτ, hgood⟩ := (enter_loop_s (g := g) (regs := regs) (w := w) (d := d)
    hp.sharedRange hi hv hw).land (C := MC) (d := {d with site := startSite d.limit}) h0
    (inv_start_s d hi) rfl rfl rfl rfl
  exact .inl (.inr ⟨_, s, rfl, hτ, hgood⟩)

theorem qk_prepare_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hw : w.regBits.isSome) : (MC).StepFor ⟨.qkBar2, i, v⟩ e := by
  let d : D := ⟨.qkBar2, i, v⟩
  refine @crossing_for L g regs w d {d with site := .qkElect} e _ Flow.code_2466
    (by advances) rfl ?_ (fun hi => hi)
  intro hi
  obtain ⟨hb, hn⟩ := hi
  change i < low v at hb
  change low v ≤ 2147483646 at hn
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  apply SegE.comp (p := 2472) (G := liveFacts L regs w d 2472)
  · apply SegE.of_seg (n := 5)
    dsimp only [d, code, ↓reduceIte]
    mma_arithmetic_span
  · apply (qk_base_s hw).comp
    apply SegE.of_seg (n := 4)
    dsimp only [d, code, ↓reduceIte]
    mma_arithmetic_span

theorem pv_prepare_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hw : w.regBits.isSome) : (MC).StepFor ⟨.pvBar2, i, v⟩ e := by
  let d : D := ⟨.pvBar2, i, v⟩
  refine @crossing_for L g regs w d {d with site := .pvElect} e _ Flow.code_2514
    (by advances) rfl ?_ (fun hi => hi)
  intro hi
  obtain ⟨hz, hb, hn⟩ := hi
  change 0 < i at hz
  change i ≤ low v at hb
  change low v ≤ 2147483646 at hn
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  apply SegE.comp (p := 2523) (G := liveFacts L regs w d 2523)
  · apply SegE.of_seg (n := 8)
    dsimp only [d, code, ↓reduceIte]
    mma_arithmetic_span
  · apply (pv_base_s hw).comp
    apply SegE.of_seg (n := 1)
    dsimp only [d, code, ↓reduceIte]
    mma_arithmetic_span

theorem qk_notify_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.qkCommit, i, v⟩ e := by
  let d : D := ⟨.qkCommit, i, v⟩
  refine @crossing_for L g regs w d (afterQk d) e _ Flow.code_2499 fires_tcCommit rfl ?_
    (fun hi => inv_after hi.left hi.right)
  intro hi
  apply SegE.comp (p := 2500) (G := F d 2500)
  · exact SegE.of_seg (n := 0) (fun t ht => by dsimp only [d, code] at ht ⊢; seg_fp ht using rfl)
  · exact after_qk_s hp.sharedRange hi.left hi.right hv

theorem qk_skip_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.qkSkip, i, v⟩ e := by
  let d : D := ⟨.qkSkip, i, v⟩
  refine @crossing_for L g regs w d (afterQk d) e _ Flow.code_2466 (by advances) rfl ?_
    (fun hi => inv_after hi.left hi.right)
  intro hi
  apply SegE.comp (p := 2500) (G := F d 2500)
  · exact SegE.of_seg (n := 1) (fun t ht => by dsimp only [d, code] at ht ⊢; seg_fp ht using rfl)
  · exact after_qk_s hp.sharedRange hi.left hi.right hv

set_option hygiene false in
local macro "pv_back" : tactic => `(tactic| (
  intro hi
  apply SegE.comp (p := 2447) (G := F d 2447)
  · apply SegE.of_seg (n := 1)
    intro t ht
    dsimp only [code] at ht ⊢
    seg_fp ht using rfl
  · exact loop_back_s hp.sharedRange hi.right.left hi.right.right hv))

theorem pv_skip_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.pvSkip, i, v⟩ e := by
  let d : D := ⟨.pvSkip, i, v⟩
  refine @crossing_for L g regs w d (iterNext d) e _ Flow.code_2514 (by advances) rfl ?_
    (fun hi => inv_iter hi.right.left hi.right.right)
  pv_back

theorem pv_done_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.pvCommit2, i, v⟩ e := by
  let d : D := ⟨.pvCommit2, i, v⟩
  refine @crossing_for L g regs w d (iterNext d) e _ Flow.code_2548 fires_tcCommit rfl ?_
    (fun hi => inv_iter hi.right.left hi.right.right)
  pv_back

theorem qk_election_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.qkElect, i, v⟩ e := by
  let d : D := ⟨.qkElect, i, v⟩
  intro t u ins ht hi' hc hf
  refine choose_lane_for (d := d) (fun b => if b then {d with site := .qk 0} else afterQk d) e
    Flow.code_2477 (by decide) (by fact_free) (by fact_free) ?_ ?_ ?_ ins ht hi' hc hf
  · intro _ _ ld
    by_cases h : laneOf L g = ld <;> simp [next, d, h]
  · intro b ld hi
    have hs := hp.sharedRange
    unfold sharedBytes at hs
    cases b
    · apply SegE.comp (p := 2500) (G := liveFacts L regs w d 2500)
      · apply SegE.of_seg (n := 22)
        dsimp only [d, code, ↓reduceIte]
        mma_arithmetic_span
      · exact after_qk_s hp.sharedRange hi.left hi.right hv
    · apply SegE.of_seg (n := 5)
      dsimp only [d, code, ↓reduceIte]
      mma_arithmetic_span
  · intro b hi
    cases b
    · exact inv_after hi.left hi.right
    · exact hi

theorem pv_election_for (hp : Pre Q L m) (i : Nat) (v : Value) (e : Event)
    (hv : v.regBits.isSome) : (MC).StepFor ⟨.pvElect, i, v⟩ e := by
  let d : D := ⟨.pvElect, i, v⟩
  intro t u ins ht hi' hc hf
  refine choose_lane_for (d := d) (fun b => if b then {d with site := .pv 0} else iterNext d) e
    Flow.code_2525 (by decide) (by fact_free) (by fact_free) ?_ ?_ ?_ ins ht hi' hc hf
  · intro _ _ ld
    by_cases h : laneOf L g = ld <;> simp [next, d, h]
  · intro b ld hi
    have hs := hp.sharedRange
    unfold sharedBytes at hs
    cases b
    · apply SegE.comp (p := 2447) (G := liveFacts L regs w d 2447)
      · apply SegE.of_seg (n := 24)
        dsimp only [d, code, ↓reduceIte]
        mma_arithmetic_span
      · exact loop_back_s hp.sharedRange hi.right.left hi.right.right hv
    · apply SegE.of_seg (n := 4)
      dsimp only [d, code, ↓reduceIte]
      mma_arithmetic_span
  · intro b hi
    cases b
    · exact inv_iter hi.right.left hi.right.right
    · exact hi

end PTX.Kernels.InklingRelDecode.Proof.Mma
