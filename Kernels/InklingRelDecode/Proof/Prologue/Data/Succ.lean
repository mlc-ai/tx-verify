-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Machine
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Where a site goes next

`succs s` lists the sites a control step from the data site `s` can reach; the sites without data
facts (`Bare`: the query and the store sites) stay among themselves (`bare_next`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow Control

/-- A site without data facts. -/
def Bare (s : Site) : Prop := tags s = [.scale]

instance : DecidablePred Bare := fun s => inferInstanceAs (Decidable (tags s = [.scale]))

def qSites : List Site := [.ldq 0, .ldq 16, .ldq 32, .ldq 48, .stq 0 0]

/-- The sites after the copy of `(b, j)`. -/
def afterC (b : Fin 3) : Fin 4 → List Site
  | 0 => [.pb b 2] | 1 => [.lb b 1] | 2 => [.pb b 4]
  | 3 => (if h : b.val + 1 < 3 then [.pb ⟨b.val + 1, h⟩ 0] else []) ++ qSites

def succs : Site → List Site
  | .sMax => [.ld 0] | .ld 0 => [.ld 1] | .ld 1 => [.ld 2] | .ld 2 => [.el 0]
  | .el i => [.init i, afterInit i] | .init i => [afterInit i]
  | .fnc0 => [.bar2] | .bar2 => .pb 0 0 :: qSites
  | .pb b 0 => [.arr b, .lb b 0] | .pb b 1 => [.psh b] | .pb b 2 => [.pel b 1]
  | .pb b 3 => [.pel b 2] | .pb b 4 => [.pel b 3] | .arr b => [.lb b 0]
  | .lb b 0 => [.pb b 1] | .lb b 1 => [.pb b 3] | .psh b => [.pel b 0]
  | .pel b j => .ptc b j :: afterC b j | .ptc b j => afterC b j
  | .ldq j => (if h : j.val + 1 < 64 then [.ldq ⟨_, h⟩] else []) ++ qSites
  | .stq i j => [Control.afterStore i j]
  | _ => []

private theorem query_mem (d : Control.D) (tid n : Nat) : querySite tid d n ∈ qSites := by
  unfold querySite; split_ifs <;> simp [qSites]

private theorem copy_mem (d : Control.D) (tid n : Nat) (b : Fin 3) (j : Fin 4) :
    afterCopy d tid n b j ∈ afterC b j := by
  fin_cases j <;> simp only [afterCopy, afterC] <;> try simp
  split_ifs <;> simp [query_mem, *]

private theorem copy_pel (d : Control.D) (tid n : Nat) (b : Fin 3) (j : Fin 4) :
    afterCopy d tid n b j ∈ succs (.pel b j) := List.mem_cons_of_mem _ (copy_mem d tid n b j)

private theorem copy_ptc (d : Control.D) (tid n : Nat) (b : Fin 3) (j : Fin 4) :
    afterCopy d tid n b j ∈ succs (.ptc b j) := copy_mem d tid n b j

set_option hygiene false in
local macro "go_site" : tactic => `(tactic| (
  simp only [Control.next, hs] at h
  obtain rfl := Option.some.inj (Option.some.inj h)
  refine ⟨?_, fun _ => rfl⟩
  (try split_ifs) <;> first | exact copy_pel .. | exact copy_ptc .. |
    simp [succs, afterC, qSites, afterInit]))

set_option hygiene false in
local macro "kind_site" : tactic => `(tactic| (
  simp only [Control.next, hs] at h
  split at h
  · obtain rfl := Option.some.inj (Option.some.inj h)
    refine ⟨?_, fun _ => rfl⟩
    (try split_ifs) <;> first | exact copy_pel .. | exact copy_ptc .. |
      simp [succs, afterC, qSites, afterInit]
  · cases h))

/-- **The successor of a data site** is one of `succs`; only the shuffle changes the broadcast. -/
theorem next_succ (Q : Params) (L : Launch) (g : Nat) {d c : Control.D} {e : Event}
    (hb : ¬ Bare d.site) (h : Control.next Q L g d e = some (some c)) :
    c.site ∈ succs d.site ∧ ((∀ b, d.site ≠ .psh b) → c.broadcast = d.broadcast) := by
  rw [Bare] at hb
  cases hs : d.site <;> rw [hs] at hb <;>
    try (exfalso; apply hb; simp [tags, pos, early, oldTags, qTags]; done)
  case sMax => go_site
  case ld k => fin_cases k <;> kind_site
  case el i => kind_site
  case init i => go_site
  case fnc0 => go_site
  case bar2 =>
    simp only [Control.next, hs] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    refine ⟨?_, fun _ => rfl⟩
    split_ifs <;> simp [succs, query_mem]
  case pb b j => fin_cases j <;> go_site
  case arr b => go_site
  case lb b h' => fin_cases h' <;> go_site
  case psh b =>
    simp only [Control.next, hs] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨by simp [succs], fun hn => absurd rfl (hn b)⟩
  case pel b j => kind_site
  case ptc b j => go_site
  case ldq j =>
    simp only [Control.next, hs] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    refine ⟨?_, fun _ => rfl⟩
    unfold afterQuery
    split_ifs
    · exact List.mem_append_right _ (query_mem ..)
    · simp [succs, *]
    · simp [succs, qSites]
  case stq i j =>
    simp only [Control.next, hs] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨by simp [succs], fun _ => rfl⟩

theorem query_tags : ∀ i j, Tag.qw i 3 ∈ tags (.stq i j) := by decide +kernel

set_option hygiene false in
local macro "bare_site" : tactic => `(tactic| (
  simp only [Control.next, hs] at h
  obtain rfl := Option.some.inj (Option.some.inj h)
  simp [Bare, tags, pos, early, oldTags, qTags]))

/-- **The sites without data facts stay among themselves** (the query sites have data facts). -/
theorem bare_next (Q : Params) (L : Launch) (g : Nat) {d c : Control.D} {e : Event}
    (hb : Bare d.site) (h : Control.next Q L g d e = some (some c)) : Bare c.site := by
  have hb' := hb
  rw [Bare] at hb'
  cases hs : d.site <;> rw [hs] at hb' <;>
    try (exfalso; revert hb'; simp [tags, pos, early, oldTags, qTags]; done)
  case stq i j => have := query_tags i j; rw [hb'] at this; simp at this
  case st9 j => fin_cases j <;> bare_site
  case exit => simp [Control.next, hs] at h
  all_goals bare_site

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
