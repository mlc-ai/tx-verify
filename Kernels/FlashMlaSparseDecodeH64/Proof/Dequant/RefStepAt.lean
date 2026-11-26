-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefArith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefNext
public import Lemmas.Flow.NcLoadU
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds

@[expose] public section

/-! # Warpgroup 2's reference invariant is kept by every step

`ref_step`: from a state with `Ref`, an event of the state's shape that the machine follows leads
to a state with `Ref` for the bumped counts; `ref_init`: the first state with no counts. -/

/-! # Warpgroup 2's reference invariant: the loop's barrier steps

The successful polls of the raw-ready and SV-done barriers and the two arrivals count one use of
the slot's barrier: block `i`'s counts with the site's increments go to those of the next site
(`use_rawReady`, `use_svDone`, `use_ready`, `use_free`); the raw-free arrival's next block starts
at `i + 1` (`use_free`). -/

/-! # Warpgroup 2's reference invariant: the step

`ref_step`, by the site: the set-up's events and the rows' reads, stores and fence leave the
slots' barrier counts alone; the four barrier sites of the loop each count one use of the slot's
barrier; the back-edge starts the next block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- Counts that agree on the polls and arrivals have the same slot counts. -/
theorem slot_congr {n n' : Cnt → Nat} (h : ∀ l, n' (.acq l) = n (.acq l) ∧
    n' (.arrive l) = n (.arrive l)) {b : Fin 2} {a s r f : Nat} :
    SlotCounts L g n b a s r f → SlotCounts L g n' b a s r f := by
  rintro ⟨h1, h2, h3, h4⟩
  exact ⟨(h _).1.trans h1, (h _).1.trans h2, (h _).2.trans h3, (h _).2.trans h4⟩

/-- A site of a row's body (after the polls, before the arrivals). -/
def Site.body : Site → Bool
  | .scale _ | .raw _ _ | .store _ _ | .fpx | .arrD => true
  | _ => false

theorem body_inc {s : Site} (h : s.body = true) :
    incR s = 1 ∧ incS s = 1 ∧ incD s = 0 ∧ incF s = 0 := by
  cases s <;> simp_all [Site.body, incR, incS, incD, incF]

theorem body_ne {s : Site} (h : s.body = true) :
    s ≠ .smr ∧ s ≠ .lenA ∧ s ≠ .lenB ∧ s ≠ .wq ∧ s ≠ .bar ∧ s ≠ .exit := by
  cases s <;> simp_all [Site.body]

theorem rawNext_body (r : Fin 4) (s : Fin 8) : (rawNext r s).body = true := by
  fin_cases r <;> fin_cases s <;> decide

theorem storeNext_body (r : Fin 4) (s : Fin 8) : (storeNext r s).body = true := by
  fin_cases r <;> fin_cases s <;> decide

/-- A step from a body site to a body site with the same ring bits and unchanged barrier
counts keeps the loop's counts. -/
theorem body_step {d d' : D} {n n' : Cnt → Nat} {i : Nat} (hw : LoopWords d' i)
    (h : LoopCounts L g d n i)
    (hd : d.site.body = true) (hd' : d'.site.body = true) (hsb : d'.sb = d.sb) (hpb : d'.pb = d.pb)
    (hc : ∀ l, n' (.acq l) = n (.acq l) ∧ n' (.arrive l) = n (.arrive l)) : Ref L g d' n' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨r1, s1, d1, f1⟩ := body_inc hd
  obtain ⟨r2, s2, d2, f2⟩ := body_inc hd'
  refine ref_loop (i := i) hw ⟨hsb.trans h1, hpb.trans h2, fun b => ?_⟩ (body_ne hd')
  have := slot_congr (L := L) (g := g) hc (h3 b)
  rw [r1, s1, d1, f1] at this
  rw [r2, s2, d2, f2]
  exact this

theorem loc_eq_iff {f f' : MbarFam} : MbarRow.loc L g f = MbarRow.loc L g f' ↔ f = f' :=
  ⟨loc_inj, fun h => h ▸ rfl⟩

/-- The ring bits of block `i + 1`. -/
theorem bits_succ (i : Nat) : (!decide (i % 2 = 1)) = decide ((i + 1) % 2 = 1) ∧
    (decide (i / 2 % 2 = 1) != decide (i % 2 = 1)) = decide ((i + 1) / 2 % 2 = 1) := by
  constructor <;> by_cases h1 : i % 2 = 1 <;> by_cases h2 : i / 2 % 2 = 1 <;>
    simp [h1, h2] <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {L : Launch} {g : Nat}

set_option hygiene false in
/-- Close one slot count after a use: unfold the increments, resolve the class test. -/
local macro "use_close" : tactic => `(tactic| (
  simp only [incR, incS, incD, incF, Nat.add_zero, Cnt.acq.injEq, Cnt.arrive.injEq,
    reduceCtorEq, loc_eq_iff, MbarFam.rawReady.injEq, MbarFam.svDone.injEq,
    MbarFam.dequantReady.injEq, MbarFam.rawFree.injEq, ↓reduceIte, Nat.add_zero, uses_succ,
    Nat.zero_add, Nat.add_zero]))

theorem use_rawReady {n : Cnt → Nat} {i : Nat} (h : ∀ b, SlotCounts L g n b (uses b (i + 0))
    (uses b (i + 0)) (uses b (i + 0)) (uses b (i + 0))) (b : Fin 2) :
    SlotCounts L g (fun c => n c + if c = .acq (MbarRow.loc L g (.rawReady (MbarRow.slot2 i)))
      then 1 else 0) b (uses b (i + 1)) (uses b (i + 0)) (uses b (i + 0)) (uses b (i + 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1, h2, h3, h4] <;> use_close

theorem use_svDone {n : Cnt → Nat} {i : Nat} (h : ∀ b, SlotCounts L g n b (uses b (i + 1))
    (uses b (i + 0)) (uses b (i + 0)) (uses b (i + 0))) (b : Fin 2) :
    SlotCounts L g (fun c => n c + if c = .acq (MbarRow.loc L g (.svDone (MbarRow.slot2 i)))
      then 1 else 0) b (uses b (i + 1)) (uses b (i + 1)) (uses b (i + 0)) (uses b (i + 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1, h2, h3, h4] <;> use_close

theorem use_ready {n : Cnt → Nat} {i : Nat} (h : ∀ b, SlotCounts L g n b (uses b (i + 1))
    (uses b (i + 1)) (uses b (i + 0)) (uses b (i + 0))) (b : Fin 2) :
    SlotCounts L g (fun c => n c +
      if c = .arrive (MbarRow.loc L g (.dequantReady (MbarRow.slot2 i))) then 1 else 0) b
      (uses b (i + 1)) (uses b (i + 1)) (uses b (i + 1)) (uses b (i + 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1, h2, h3, h4] <;> use_close

theorem use_free {n : Cnt → Nat} {i : Nat} (h : ∀ b, SlotCounts L g n b (uses b (i + 1))
    (uses b (i + 1)) (uses b (i + 1)) (uses b (i + 0))) (b : Fin 2) :
    SlotCounts L g (fun c => n c +
      if c = .arrive (MbarRow.loc L g (.rawFree (MbarRow.slot2 i))) then 1 else 0) b
      (uses b (i + 1 + 0)) (uses b (i + 1 + 0)) (uses b (i + 1 + 0)) (uses b (i + 1 + 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1, h2, h3, h4] <;> use_close

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem ref_init : Ref L g { site := .smr } (fun _ => 0) :=
  fun _ => ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The step of a set-up site (no barrier counted). -/
theorem setup_next (hp : Pre P L m) {d d' : D} {n : Cnt → Nat}
    (hq : n (.acq (MbarRow.loc L g .qUtccp)) = 0)
    (hs : ∀ b, SlotCounts L g n b 0 0 0 0) {e : Event}
    (hd : d.site = .smr ∨ d.site = .lenA ∨ d.site = .lenB)
    (hn : succ P L g d e = some (some d')) : Ref L g d' n := by
  refine ref_setup hq hs ?_
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  rcases hd with rfl | rfl | rfl
  · simp only [succ, afterSmr, batch_in hp g, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at hn
    subst hn
    unfold afterA
    split_ifs <;> simp
  · simp only [succ] at hn
    split at hn
    · unfold Code.ncNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        unfold afterA
        split_ifs <;> simp
      · simp at hn
      · simp at hn
    · simp at hn
  · simp only [succ] at hn
    split at hn
    · unfold Code.ncNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        simp
      · simp at hn
      · simp at hn
    · simp at hn

set_option hygiene false in
/-- Open a loop state's counts: block `i`, its bits `hsb`, `hpb` and slot counts `hc`. -/
local macro "loop_open" : tactic => `(tactic| (
  obtain ⟨i, hw, hsb, hpb, hc⟩ := hJ'
  dsimp only [incR, incS, incD, incF] at hsb hpb hc))

/-- **The reference invariant is kept by every step** the machine follows. -/
theorem ref_step (hp : Pre P L m) {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : Ref L g d n)
    (hev : Ev L g d e) (hn : succ P L g d e = some (some d')) :
    Ref L g d' (Code.bump cls n e) := by
  obtain ⟨hpc, hk⟩ := hev
  have hx : d.site ≠ .exit := by intro h; simp [succ, h] at hn
  have hin : inRole e = true := by
    have h1 := (Site.pc_range d.site).1
    have h2 := Site.pc_lt d.site hx
    simp only [inRole, decide_eq_true_eq]
    omega
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    intro h0
    simp [Code.bump, cls, hin, kindOf, hf] at h0
  have hu' : ∀ f, e.kind ≠ .ub f := fun f h => hu ⟨f, h⟩
  suffices key : n .ub = 0 → Ref L g d' (Code.bump cls n e) by
    intro h0
    exact key (by simp only [Code.bump] at h0; omega) h0
  intro hn0
  have hJ' := hJ hn0
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk hpc hu' hin ⊢
  cases site with
  | smr =>
    obtain ⟨inst, rfl⟩ := hk
    rw [bump_none rfl]
    exact setup_next hp hJ'.1 hJ'.2 (.inl rfl) hn
  | lenA | lenB =>
    rcases hk with ⟨a, bs, rfl⟩ | ⟨f, rfl⟩
    · rw [bump_none rfl]
      first
        | exact setup_next hp hJ'.1 hJ'.2 (.inr (.inl rfl)) hn
        | exact setup_next hp hJ'.1 hJ'.2 (.inr (.inr rfl)) hn
    · exact absurd rfl (hu' f)
  | wq =>
    rcases hk with ⟨ok, rfl⟩ | ⟨f, rfl⟩
    · cases ok
      · rw [bump_none rfl]
        simp only [succ, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact ref_setup hJ'.1 hJ'.2 (.inr (.inr rfl))
      · rw [bump_of hin rfl, q_loc hp]
        simp only [succ, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        unfold loopEntry
        split_ifs with hlt
        · refine ref_bar rfl fun b => ?_
          obtain ⟨h1, h2, h3, h4⟩ := hJ'.2 b
          have hb := b.isLt
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [h1, h2, h3, h4, loc_eq_iff, uses, rounds, hlt] <;> omega
        · obtain ⟨h1R, hR, hc0⟩ := blocks_pos (Bool.eq_false_iff.mpr hlt)
          refine ref_loop (i := 0) ⟨h1R, hR, hc0⟩ ⟨rfl, rfl, fun b => ?_⟩ (by simp)
          obtain ⟨h1, h2, h3, h4⟩ := hJ'.2 b
          have hb := b.isLt
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [h1, h2, h3, h4, loc_eq_iff, uses, incR, incS, incD, incF] <;> omega
    · exact absurd rfl (hu' f)
  | wraw =>
    loop_open
    rcases hk with ⟨ok, rfl⟩ | ⟨f, rfl⟩
    · cases ok
      · rw [bump_none rfl]
        simp only [succ, poll, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact ref_loop (i := i) hw ⟨hsb, hpb, hc⟩ (by simp)
      · rw [bump_of hin rfl, raw_loc hp, hsb, slotF_slot2]
        simp only [succ, poll, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact ref_loop (i := i) hw ⟨hsb, hpb, use_rawReady hc⟩ (by simp)
    · exact absurd rfl (hu' f)
  | wsv =>
    loop_open
    rcases hk with ⟨ok, rfl⟩ | ⟨f, rfl⟩
    · cases ok
      · rw [bump_none rfl]
        simp only [succ, poll, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact ref_loop (i := i) hw ⟨hsb, hpb, hc⟩ (by simp)
      · rw [bump_of hin rfl, sv_loc hp, hsb, slotF_slot2]
        simp only [succ, poll, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        exact ref_loop (i := i) hw ⟨hsb, hpb, use_svDone hc⟩ (by simp)
    · exact absurd rfl (hu' f)
  | arrD =>
    loop_open
    simp only [EvK] at hk
    subst hk
    rw [bump_of hin rfl, ready_loc hp, hsb, slotF_slot2]
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact ref_loop (i := i) hw ⟨hsb, hpb, use_ready hc⟩ (by simp)
  | arrF =>
    loop_open
    simp only [EvK] at hk
    subst hk
    rw [bump_of hin rfl, free_loc hp, hsb, slotF_slot2]
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨b1, b2⟩ := bits_succ i
    obtain ⟨hi, hR, hcnt⟩ := hw
    obtain ⟨c1, c2⟩ := cnt_next hi hR
    dsimp only at hi hR hcnt
    dsimp only [advance]
    rw [hcnt, c2]
    split_ifs with hlast
    · refine ref_loop (i := i + 1) ⟨by dsimp only; simp at hlast; omega, hR, by simp only [c1]⟩
        ⟨?_, ?_, use_free hc⟩ (by simp)
      · simp only [hsb, b1]
      · simp only [hsb, hpb, b2]
    · refine ref_bar rfl fun b => ?_
      have hl : i + 1 = rounds l0 l1 := by simpa using hlast
      rw [← hl]
      exact use_free hc b
  | bar =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    simp only [EvK] at hk
    subst hk
    intro _ b
    obtain ⟨h1, h2, h3, h4⟩ := hJ' b
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Code.bump, cls, kindOf, h1, h2, h3, h4]
  | exit => exact absurd rfl hx
  | scale r =>
    loop_open
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    · rw [bump_none rfl]
      simp only [succ, Option.some.injEq] at hn
      subst hn
      unfold scaleNext
      split_ifs
      · exact body_step (i := i) hw ⟨hsb, hpb, hc⟩ rfl rfl rfl rfl fun _ => ⟨rfl, rfl⟩
      · exact body_step (i := i) hw ⟨hsb, hpb, hc⟩ rfl rfl rfl rfl fun _ => ⟨rfl, rfl⟩
    · exact absurd rfl (hu' f)
  | raw r j =>
    loop_open
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    · rw [bump_none rfl]
      simp only [succ, dataRd, Option.some.injEq] at hn
      subst hn
      exact body_step (d := ⟨.raw r j, el, ac, l0, l1, cnt, sb, pb⟩) (i := i) hw ⟨hsb, hpb, hc⟩ rfl
        (rawNext_body r j) rfl rfl fun _ => ⟨rfl, rfl⟩
    · exact absurd rfl (hu' f)
  | store r j =>
    loop_open
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    · rw [bump_of hin rfl]
      simp only [succ, Option.some.injEq] at hn
      subst hn
      exact body_step (d := ⟨.store r j, el, ac, l0, l1, cnt, sb, pb⟩) (i := i) hw ⟨hsb, hpb, hc⟩
        rfl (storeNext_body r j) rfl rfl fun _ => ⟨by simp, by simp⟩
    · exact absurd rfl (hu' f)
  | fpx =>
    loop_open
    simp only [EvK] at hk
    subst hk
    rw [bump_none rfl]
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact body_step (i := i) hw ⟨hsb, hpb, hc⟩ rfl rfl rfl rfl fun _ => ⟨rfl, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
