-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.BarGroup
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # Every named barrier has its participant group

From the barrier rows (`bar_cls`, `bar_cnt`): a barrier event of the code names barrier 0, 9, 10,
11 or 12, its group is `barWarps id` (`Common/Export/BarGroup.lean`) with the thread count
`barCnt id` (`NamedBar.Shape`), and every arrival on it is a lane of a participant warp passing
that count (`NamedBar.Sources`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A barrier event names barrier 0, 9, 10, 11 or 12, and a warp-pair barrier is its warp's. -/
private theorem bar_ids (hR : BarRows P L X) {g k id pc : Nat} {cnt : Option Nat}
    {md : BarMode} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩) :
    id = 0 ∨ (id = 9 ∧ warp L g < 4) ∨ ((id = 10 ∨ id = 11) ∧ warp L g < 4 ∧
      warp L g % 2 = id - 10) ∨ id = 12 := by
  rcases bar_cls (bar_use hR hg he rfl) with ⟨-, h⟩ | ⟨⟨hw, -⟩, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ |
    ⟨-, -, h⟩
  all_goals simp only [BarRow.Cta, BarRow.Sync, Kind.bar.injEq] at h
  all_goals obtain ⟨rfl, -, -⟩ := h
  all_goals omega

/-- The warp of a lane is its CTA-local warp index. -/
private theorem warp_mod (hp : Pre P L m) (g : Nat) : warp L g = g % L.block / 32 := by
  simp only [warp, tidOf_x_eq hp, hp.block]

/-- **Every named barrier has its group** `barWarps id`, with its sources. -/
theorem bar_groupW (hp : Pre P L m) (hR : BarRows P L X) {g i pc id : Nat} {cnt : Option Nat}
    {md : BarMode} (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .bar id cnt md⟩) :
    NamedBar.Shape L cnt (barWarps id) id ∧ NamedBar.Sources L X cnt (barWarps id) id := by
  have hb : L.block = 384 := hp.block
  have hc := bar_cnt hR hg he
  subst hc
  refine ⟨?_, fun e pc' cnt' ha hl => ?_⟩
  · have hS : ∀ j, (j = 0 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12) →
        NamedBar.Shape L (barCnt j) (barWarps j) j := by
      intro j hj
      refine ⟨?_, ?_, fun w hw => ?_, by omega⟩
      · rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
      · rw [hb]
        rcases hj with rfl | rfl | rfl | rfl | rfl
        · rw [show (barWarps 0).card = 12 by decide]; rfl
        · rw [show (barWarps 9).card = 4 by decide]; rfl
        · rw [show (barWarps 10).card = 2 by decide]; rfl
        · rw [show (barWarps 11).card = 2 by decide]; rfl
        · rw [show (barWarps 12).card = 12 by decide]; rfl
      · rw [hb]
        exact Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    exact hS id (by rcases bar_ids hR hg he with h | ⟨h, -⟩ | ⟨h, -⟩ | h <;> omega)
  · obtain ⟨md', he'⟩ := ha
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, bar_cnt hR hl he'⟩
    · rw [Finset.mem_range, hb]
      have : e.1 % 384 < 384 := Nat.mod_lt _ (by omega)
      omega
    · have hw := warp_mod hp e.1
      have hlt : e.1 % L.block / 32 < 12 := by
        rw [hb]
        have : e.1 % 384 < 384 := Nat.mod_lt _ (by omega)
        omega
      rw [← hw] at hlt ⊢
      unfold barIn
      rcases bar_ids hR hl he' with h | ⟨h, h4⟩ | ⟨h, h4, h2⟩ | h
      all_goals split_ifs <;> first | omega | (simp only [decide_eq_true_eq]; omega)

/-- **Every named barrier has its participant group** (some set of participant warps). -/
theorem bar_group (hp : Pre P L m) (hR : BarRows P L X) {g i pc id : Nat} {cnt : Option Nat}
    {md : BarMode} (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .bar id cnt md⟩) :
    ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id ∧
      ∀ w ∈ q, barIn id w = true :=
  ⟨barWarps id, (bar_groupW hp hR hg he).1, (bar_groupW hp hR hg he).2,
    fun _ hw => (Finset.mem_filter.mp hw).2⟩
