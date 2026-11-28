-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Carry

@[expose] public section

/-! # Where the row of a block-table word comes from

A site holds the row fact of half `h` of block `b` only after the load of that word: the
successors of a site keep the row facts of the site, or the site is that load, which records the
word it read (`pay_succ`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow Control

theorem row_succs : ∀ s, ∀ s' ∈ succs s, ∀ b h,
    Tag.row b h ∈ tags s' → Tag.row b h ∈ tags s ∨ s = .lb b h := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem lb_no_row : ∀ b h b' h', Tag.row b h ∉ tags (Site.lb b' h') := by decide +kernel

/-- **The row fact of a successor** is the site's own (the word unchanged), or the site is the
load of the word, and a read event records it. -/
theorem pay_succ {Q : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ Q L g d e = some (some d')) {b : Fin 3} {h' : Fin 2}
    (hr : Tag.row b h' ∈ tags d'.c.site) :
    (Tag.row b h' ∈ tags d.c.site ∧ d'.v.pay b h' = d.v.pay b h') ∨
      (d.c.site = .lb b h' ∧ ∀ a bs, e.kind = .rd a bs → d'.v.pay b h' = loadVal bs) := by
  obtain ⟨c, hn, rfl⟩ := succ_split h
  by_cases hb : Bare d.c.site
  · have := bare_next Q L g hb hn
    simp only [Bare] at this
    rw [this] at hr
    simp at hr
  · obtain ⟨hm, -⟩ := next_succ Q L g hb hn
    rcases row_succs _ _ hm b h' hr with hs | hs
    · left
      refine ⟨hs, ?_⟩
      show (record d e).pay b h' = _
      rw [record_keep (fun b' h'' e => lb_no_row b h' b' h'' (e ▸ hs)) (fun j e => by
        rw [e] at hs; simp [tags, oldTags, pos, early, qTags, qhs] at hs)]
    · right
      refine ⟨hs, fun a bs hk => ?_⟩
      unfold record
      rw [hs, hk]
      simp

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
