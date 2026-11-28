-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Succ
public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.RegionTable
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The data facts a site carries

A site whose event and following code write none of its data facts, and whose successors keep
only facts it has, is checked by `carryOk` (a table over the code). `carry_step` is the data step
of every such site, whatever the kind of its event. The sites that compute a fact (`compute`: the
loads of the block table and the two column elections of a block) are in `Compute.lean`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.EventFrame Control

/-- The sites that compute a data fact of their successor. -/
def compute : Site → Bool
  | .lb _ _ => true
  | .pel _ 0 | .pel _ 1 => true
  | _ => false

/-- The sites whose successors may be query sites, and the query sites that compute a fact. -/
def qside : Site → Bool
  | .bar2 | .pel _ 3 | .ptc _ 3 | .ldq _ | .stq _ 3 => true
  | _ => false

def carrySite (s : Site) : Bool := !compute s && !qside s && s != .exit

/-- The position that writes the register of a fact (none for the launch constants). -/
def Tag.pc : Tag → Nat
  | .oy => 198 | .ox => 200
  | .row b h => [[199, 221], [242, 263], [284, 305]].getD b [] |>.getD h 0
  | .col b h => [[210, 216], [252, 258], [294, 300]].getD b [] |>.getD h 0
  | .zero => 386 | .qh k => 387 + 2 * k.val | .qw i k => 522 + 6 * i.val + k.val
  | _ => 0

def allTags : List Tag :=
  [.scale, .stride, .rows, .cols, .oy, .ox] ++ (List.finRange 3).flatMap fun b =>
    (List.finRange 2).flatMap fun h => [.row b h, .col b h]
  ++ [.zero] ++ (List.finRange 64).map .qh ++
    (List.finRange 8).flatMap fun i => (List.finRange 4).map (.qw i)

/-- The code of the prologue, from its first position. -/
abbrev slice := (kernel.code.drop 27).take 548

/-- **Each data register is written once** in the prologue, by the position of its fact. -/
theorem writers_tag : scanL (instrOk 574) slice 27 = true ∧
    allTags.all (fun τ => (writersL τ.reg slice 27).all (· == τ.pc)) = true := by
  decide +kernel

/-- The check of one carry site. -/
def carryOk (s : Site) : Bool :=
  (succs s).all (fun s' => (tags s').all (· ∈ tags s)) && Nat.blt s.pc 574 &&
    (tags s).all (fun τ => Nat.blt τ.pc s.pc) &&
    (match kernel.code[s.pc]? with
      | some ins => (tags s).all fun τ => !(eventWrites ins.op).contains τ.reg
      | none => false)

theorem carry_all : ∀ s, carrySite s = true → carryOk s = true := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem old_noq : ∀ s, (∀ k, Tag.qh k ∉ oldTags s) ∧ ∀ i k, Tag.qw i k ∉ oldTags s := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem record_keep {d : D} {e : Event} (h : ∀ b h', d.c.site ≠ .lb b h')
    (h' : ∀ j, d.c.site ≠ .ldq j) : record d e = d.v := by
  unfold record
  split
  · rename_i heq _
    exact absurd heq (h _ _)
  · rename_i heq _
    exact absurd heq (h' _)
  · rfl

theorem col_psh : ∀ b b' h, Tag.col b h ∉ tags (.psh b') := by decide +kernel

theorem succ_split {Q : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ Q L g d e = some (some d')) :
    ∃ c, Control.next Q L g d.c e = some (some c) ∧ d' = ⟨c, record d e⟩ := by
  unfold succ at h
  cases hn : Control.next Q L g d.c e with
  | none => rw [hn] at h; cases h
  | some o => cases o <;> simp_all

/-- **The facts of a carry site's successor are among its own.** -/
theorem carry_sub {Q : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hs : carrySite d.c.site = true) (h : succ Q L g d e = some (some d')) :
    ∀ x ∈ dF Q L g d', x ∈ dF Q L g d := by
  obtain ⟨c, hn, rfl⟩ := succ_split h
  have hc := carry_all _ hs
  simp only [carrySite, Bool.and_eq_true, Bool.not_eq_true'] at hs
  have hl : ∀ b h', d.c.site ≠ .lb b h' := fun b h' e => by simp_all [compute]
  have hq : ∀ j, d.c.site ≠ .ldq j := fun j e => by simp_all [compute, qside]
  have hsub : ∀ τ ∈ tags c.site, τ ∈ tags d.c.site ∧
      (¬ Bare d.c.site → (∀ b, d.c.site ≠ .psh b) → c.broadcast = d.c.broadcast) := by
    by_cases hb : Bare d.c.site
    · intro τ hτ
      have := bare_next Q L g hb hn
      simp only [Bare] at hb this
      rw [this] at hτ
      rw [hb]
      exact ⟨hτ, fun h' => absurd hb h'⟩
    · obtain ⟨hm, hbc⟩ := next_succ Q L g hb hn
      simp only [carryOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      exact fun τ hτ => ⟨hc.1.1.1 _ hm τ hτ, fun _ => hbc⟩
  intro x hx
  simp only [dF, List.mem_map] at hx ⊢
  obtain ⟨τ, hτ, rfl⟩ := hx
  obtain ⟨hτ', hbc⟩ := hsub τ hτ
  refine ⟨τ, hτ', ?_⟩
  rw [record_keep hl hq]
  cases τ with
  | col b' h' =>
    have hnb : ¬ Bare d.c.site := fun hb => by simp only [Bare] at hb; rw [hb] at hτ'; simp at hτ'
    have : ∀ b, d.c.site ≠ .psh b := fun b hp => col_psh b' b h' (hp ▸ hτ')
    simp [Tag.val, hbc hnb this]
  | qh _ | qw _ _ =>
    obtain ⟨i, j, hst⟩ : ∃ i j, d.c.site = .stq i j := by
      have hm : _ ∈ qTags d.c.site := (List.mem_append.mp hτ').resolve_left (by
        have := old_noq d.c.site; intro h; first | exact this.1 _ h | exact this.2 _ _ h)
      revert hm hs; cases d.c.site <;> simp [qside, qTags]
    simp only [Control.next, hst, Option.some.injEq] at hn
    have eq : ∀ t grp, queryOn t grp c = queryOn t grp d.c := fun t grp => by rw [← hn]; rfl
    simp [Tag.val, qv, eq]
  | _ => rfl

theorem tags_pc : ∀ s, (tags s).all (fun τ => Nat.blt τ.pc s.pc) = true := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem mem_allTags (τ : Tag) : τ ∈ allTags := by
  cases τ <;> simp [allTags]

theorem seg_range {pc : Nat} (h1 : 27 ≤ pc) (h2 : pc ≤ 574) :
    Assumption.SegFreePc Assumptions.all pc := by
  have h : ∀ q ∈ List.range' 27 548, Assumptions.emuSites.contains q = false := by decide +kernel
  exact segFree (h pc (List.mem_range'_1.mpr ⟨by omega, by omega⟩))

/-- **No instruction from `lo` on writes a fact defined before `lo`.** -/
theorem region_tags {T : List Tag} {lo : Nat} (h0 : 27 ≤ lo) (h : ∀ τ ∈ T, τ.pc < lo) :
    regionB kernel lo 574 (T.map Tag.reg) = true := by
  refine regionB_of_scan (lo0 := 27) h0 writers_tag.1 fun r hr' pc hpc => ?_
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hr'
  have h1 := List.all_eq_true.mp writers_tag.2 τ (mem_allTags τ)
  have h2 := beq_iff_eq.mp (List.all_eq_true.mp h1 pc hpc)
  have := h τ hτ
  omega

/-- **The data step of a carry site**, whatever the kind of its event. -/
theorem carry_step {Q : Params} {L : Launch} {g : Nat} {w : Value} (d : D)
    (hs : carrySite d.c.site = true) : Code.DataStep (code Q L g w) (dF Q L g) d := by
  have hc := carry_all _ hs
  have hr := d.c.site.pc_range
  simp only [carryOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨-, hlt⟩, hdef⟩, hev⟩ := hc
  cases hcode : kernel.code[d.c.site.pc]? with
  | none => rw [hcode] at hev; cases hev
  | some ins =>
    rw [hcode] at hev
    have hmap : (dF Q L g d).map Prod.fst = (tags d.c.site).map Tag.reg := by simp [dF]
    have hB : regionB kernel d.c.site.pc 574 ((dF Q L g d).map Prod.fst) = true := by
      rw [hmap]
      exact region_tags (by omega) fun τ hτ => Nat.blt_eq.mp (List.all_eq_true.mp hdef τ hτ)
    have hev' : ((dF Q L g d).map Prod.fst).all (fun r => !(eventWrites ins.op).contains r) =
        true := by
      rw [hmap]
      simpa using hev
    have hS : ∀ pc, d.c.site.pc ≤ pc → pc ≤ 574 → Assumption.SegFreePc Assumptions.all pc :=
      fun pc h1 h2 => seg_range (by omega) h2
    intro t e u d' ins' hat hi' hc' hf hn
    exact Code.DataStep.carry (C' := code Q L g w) (dF := dF Q L g) (d := d) (ins := ins)
      (hi := 574)
      Lib.rulesFrame hcode (fun R hR => ((holds_append _ _ _).mp hR).2) hB
      hS (Nat.succ_le_of_lt (Nat.blt_eq.mp hlt)) hev' (fun _ _ h => carry_sub hs (by exact h))
      ins' hat hi' hc' hf hn

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
