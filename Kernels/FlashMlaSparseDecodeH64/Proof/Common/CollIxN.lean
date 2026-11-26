-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Time

@[expose] public section

/-! # The index warp's shuffle count

A state of the index warp has made `ixN` shuffles: the three of the startup and the head, two
per block done (`blockOf`, the arrivals on the four slots of `valid_coord_ready`), and those of
its own block before its site (`soff`: the first shuffle of a block is made at `sA1`/`sB1`, the
second at `sA2`/`sB2`, and from the coordinate store on both are). A step on an event of the
state's shape adds one exactly at a shuffle (`ixN_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The shuffles of the current block made before a site. -/
def soff : IxSite → Nat
  | .sA2 | .sB2 => 1
  | .stA | .bA | .arrA | .stB | .bB | .arrB => 2
  | _ => 0

/-- **The shuffles a state has made.** -/
def ixN (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Nat :=
  3 + 2 * blockOf L g n + soff d.site

@[simp] theorem soff_lenA : soff .lenA = 0 := rfl
@[simp] theorem soff_lenB : soff .lenB = 0 := rfl
@[simp] theorem soff_pre : soff .pre = 0 := rfl
@[simp] theorem soff_pf : soff .pf = 0 := rfl
@[simp] theorem soff_wA : soff .wA = 0 := rfl
@[simp] theorem soff_sA1 : soff .sA1 = 0 := rfl
@[simp] theorem soff_sA2 : soff .sA2 = 1 := rfl
@[simp] theorem soff_stA : soff .stA = 2 := rfl
@[simp] theorem soff_bA : soff .bA = 2 := rfl
@[simp] theorem soff_arrA : soff .arrA = 2 := rfl
@[simp] theorem soff_xpre : soff .xpre = 0 := rfl
@[simp] theorem soff_xpf : soff .xpf = 0 := rfl
@[simp] theorem soff_wB : soff .wB = 0 := rfl
@[simp] theorem soff_sB1 : soff .sB1 = 0 := rfl
@[simp] theorem soff_sB2 : soff .sB2 = 1 := rfl
@[simp] theorem soff_stB : soff .stB = 2 := rfl
@[simp] theorem soff_bB : soff .bB = 2 := rfl
@[simp] theorem soff_arrB : soff .arrB = 2 := rfl
@[simp] theorem soff_bar : soff .bar = 0 := rfl
@[simp] theorem soff_exit : soff .exit = 0 := rfl

theorem soff_of_incW {s : IxSite} (h : incW s = 0) : soff s = 0 := by
  cases s <;> simp_all [incW, soff]

theorem incW_ixNoMain (c : IxCtl) : incW (ixNoMain c).1 = 0 := by
  obtain ⟨-, -, h⟩ := zero_noMain c
  exact h

theorem incW_ixLens (c : IxCtl) : incW (ixLens c).1 = 0 := by
  unfold ixLens; dsimp only; split
  · exact incW_ixNoMain _
  · rfl

theorem incW_ixAfterA (P : Params) (c : IxCtl) : incW (ixAfterA P c).1 = 0 := by
  unfold ixAfterA; split
  · exact incW_ixLens c
  · rfl

theorem incW_mainEnd (c : IxCtl) : incW (mainEnd c).1 = 0 := by
  obtain ⟨-, -, h, -⟩ := keeps_mainEnd c
  exact h

theorem incW_xEnd (c : IxCtl) : incW (xEnd c).1 = 0 := by
  obtain ⟨-, -, h, -⟩ := keeps_xEnd c
  exact h

theorem incW_afterPre (P : Params) (L : Launch) (g : Nat) (c : IxCtl) :
    incW (afterPre P L g c).1 = 0 := by
  obtain ⟨-, -, h⟩ := zero_afterPre (P := P) (L := L) (g := g) c
  exact h

theorem incW_afterXpre (L : Launch) (g : Nat) (c : IxCtl) : incW (afterXpre L g c).1 = 0 := by
  obtain ⟨-, -, h, -⟩ := keeps_afterXpre (L := L) (g := g) c
  exact h

/-- **The block of the counts is the invariant's block**, at any poll state. -/
theorem blockOf_eq' {n : Cnt → Nat} {i w : Nat} (hc : RingCounts L g n i w) :
    blockOf L g n = i := by
  unfold blockOf
  rw [(hc 0).2, (hc 1).2, (hc 2).2, (hc 3).2]
  exact ring_sum i

/-- A class other than an arrival keeps the blocks. -/
theorem blockOf_ixQuiet {e : Event} (n : Cnt → Nat) (hq : ∀ l, kindOf e ≠ some (.arrive l)) :
    blockOf L g (Code.bump cls n e) = blockOf L g n := by
  unfold blockOf
  rw [bump_eq (hq _), bump_eq (hq _), bump_eq (hq _), bump_eq (hq _)]

/-- An arrival on a slot's `coordReady` finishes a block. -/
theorem blockOf_ready {e : Event} {s : Fin 4} (n : Cnt → Nat) (hin : inRole e = true)
    (hk : kindOf e = some (.arrive (MbarRow.loc L g (.coordReady s)))) :
    blockOf L g (Code.bump cls n e) = blockOf L g n + 1 := by
  have hb : ∀ t : Fin 4, Code.bump cls n e (.arrive (MbarRow.loc L g (.coordReady t))) =
      n (.arrive (MbarRow.loc L g (.coordReady t))) + if t = s then 1 else 0 := by
    intro t
    by_cases hts : t = s
    · subst hts
      rw [bump_self hin hk]; simp
    · have hne : kindOf e ≠ some (.arrive (MbarRow.loc L g (.coordReady t))) := by
        rw [hk]; intro h
        simp only [Option.some.injEq, Cnt.arrive.injEq] at h
        exact hts (MbarFam.coordReady.inj (loc_inj h)).symm
      rw [bump_eq hne]; simp [hts]
  unfold blockOf
  rw [hb 0, hb 1, hb 2, hb 3]
  fin_cases s <;> simp <;> omega

/-- A step on a quiet event (no arrival) adds the shuffles of the site change. -/
theorem ixN_quiet {d d' : D} {n : Cnt → Nat} {e : Event}
    (hq : ∀ l, kindOf e ≠ some (.arrive l))
    (hs : soff d'.site = soff d.site + if Execution.isShfl e then 1 else 0) :
    ixN L g d' (Code.bump cls n e) = ixN L g d n + if Execution.isShfl e then 1 else 0 := by
  unfold ixN
  rw [blockOf_ixQuiet n hq]
  omega

/-- **A step adds a shuffle exactly at a shuffle** (the sites `sA1`, `sA2`, `sB1`, `sB2`). -/
theorem ixN_step (hp : Pre P L m) {d d' : D} {n : Cnt → Nat} {e : Event}
    (hb : Body P L g d n) (hev : Ev P L g d e) (hnu : ∀ f, e.kind ≠ .ub f)
    (hs : succ P L g d e = some (some d')) :
    ixN L g d' (Code.bump cls n e) = ixN L g d n + if Execution.isShfl e then 1 else 0 := by
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨hpc, hk⟩ := hev
  have hx : site ≠ .exit := by rintro rfl; simp [succ] at hs
  have hin : inRole e = true := by
    have := site_inRole site hx
    simp only [inRole, hpc, decide_eq_true_eq]; exact this
  obtain ⟨i, -, hsl, -, -, -⟩ := hb
  dsimp only at hsl
  obtain ⟨pc, kd⟩ := e
  dsimp only at hk hnu hs hin
  cases site with
  | exit => exact absurd rfl hx
  | lenA | lenB =>
    rcases hk with ⟨a, bs, rfl⟩ | ⟨f, rfl⟩
    · simp only [succ, lenNext] at hs
      obtain ⟨x, rfl⟩ := ncNext_some hs
      refine ixN_quiet (fun l => by simp [kindOf]) ?_
      first
        | rw [soff_of_incW (incW_ixAfterA P _)]
        | rw [soff_of_incW (incW_ixLens _)]
      simp [Execution.isShfl]
    · exact absurd rfl (hnu f)
  | pre | pf | xpre | xpf =>
    all_goals
      rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
      swap
      · exact absurd hk (hnu f)
      dsimp only at hk
      subst hk
      simp only [succ] at hs
      have e1 := fun c' => soff_of_incW (incW_afterPre P L g c')
      have e2 := fun c' => soff_of_incW (incW_afterXpre L g c')
      rcases pair_cases hs with h | ⟨y0, y1, h⟩ <;>
        refine ixN_quiet (fun l => by simp [kindOf]) ?_ <;>
        simp [Execution.isShfl, e1, e2, h]
  | wA | wB =>
    all_goals
      rcases hk with ⟨ok, rfl⟩ | ⟨f, rfl⟩
      swap
      · exact absurd rfl (hnu f)
      simp only [succ, poll, Option.some.injEq] at hs
      subst hs
      refine ixN_quiet (fun l => by cases ok <;> simp [kindOf]) ?_
      cases ok <;> simp [Execution.isShfl]
  | sA1 | sA2 | sB1 | sB2 =>
    all_goals
      rcases hk with ⟨a, b, c', r, ok, rfl⟩ | ⟨f, rfl⟩
      swap
      · exact absurd rfl (hnu f)
      simp only [succ] at hs
      obtain ⟨r', rfl⟩ := shflNext_some hs
      refine ixN_quiet (fun l => by simp [kindOf]) ?_
      simp [Execution.isShfl]
  | bA | bB =>
    all_goals
      rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
      swap
      · exact absurd rfl (hnu f)
      simp only [succ, Option.some.injEq] at hs
      subst hs
      refine ixN_quiet (fun l => by simp [kindOf]) ?_
      simp [Execution.isShfl]
  | stA =>
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    swap
    · exact absurd rfl (hnu f)
    simp only [succ, Option.some.injEq] at hs
    subst hs
    refine ixN_quiet (fun l => by simp [kindOf]) ?_
    have e1 : soff (afterSt L g .bA .arrA) = 2 := by
      rcases afterSt_cases (L := L) (g := g) .bA .arrA with e | e <;> rw [e] <;> rfl
    rcases stNext_cases (⟨.stA, el, ac, c⟩ : D) (ofC (afterSt L g .bA .arrA, c)) with h | h <;>
      simp [Execution.isShfl, h, e1]
  | stB =>
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    swap
    · exact absurd rfl (hnu f)
    simp only [succ, Option.some.injEq] at hs
    subst hs
    refine ixN_quiet (fun l => by simp [kindOf]) ?_
    have e1 : soff (afterSt L g .bB .arrB) = 2 := by
      rcases afterSt_cases (L := L) (g := g) .bB .arrB with e | e <;> rw [e] <;> rfl
    rcases stNext_cases (⟨.stB, el, ac, c⟩ : D) (ofC (afterSt L g .bB .arrB, c)) with h | h <;>
      simp [Execution.isShfl, h, e1]
  | bar =>
    simp only [EvK] at hk
    subst hk
    simp only [succ, Option.some.injEq] at hs
    subst hs
    refine ixN_quiet (fun l => by simp [kindOf]) ?_
    simp [Execution.isShfl]
  | arrA | arrB =>
    all_goals
      simp only [EvK] at hk
      subst hk
      simp only [succ, Option.some.injEq] at hs
      subst hs
      have hr : kindOf ⟨pc, .arrive (smLoc L g (readyW L c) 0) 0 1 true .cta⟩ =
          some (.arrive (MbarRow.loc L g (.coordReady (MbarRow.slot4 i)))) := by
        simp only [kindOf, ready_loc hp, hsl]
      unfold ixN
      rw [blockOf_ready n hin hr]
    first
      | (have e := soff_of_incW (incW_mainEnd c); simp [Execution.isShfl, e]; omega)
      | (have e := soff_of_incW (incW_xEnd c); simp [Execution.isShfl, e]; omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
