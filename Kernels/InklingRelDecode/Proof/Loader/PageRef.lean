-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

/-- The block-table words of the current iteration that the loop has already loaded. -/
def Site.pages : Site → Nat
  | .warpBar p | .elect p | .copy p _ => if p.val < 2 then 1 else 2
  | .page upper => upper.toNat
  | _ => 0

/-- Every word the loop has loaded satisfies `P`, read with the loop counter of its iteration
(`P δ counter word`: the word of the block table for the slab `2 (splits j + x) + δ`). -/
def PageRef (P : Nat → Value → Value → Prop) (d : D) : Prop :=
  (1 ≤ d.site.pages → P 0 d.counter d.page0) ∧ (2 ≤ d.site.pages → P 1 d.counter d.page1)

/-- A block-table load returns a word satisfying `P` at the loop counter. -/
def PageResponse (P : Nat → Value → Value → Prop) (d : D) (e : Event) : Prop :=
  match d.site, e.kind with
  | .page u, .rd _ bs => ∀ v, rebuild 3 bs = .ok v → P u.toNat d.counter v
  | _, _ => True

theorem pageRef_init (P : Nat → Value → Value → Prop) : PageRef P {} := ⟨nofun, nofun⟩

private theorem finish_pages (d : D) (p : Fin 4) :
    (finishPair d p).page0 = d.page0 ∧ (finishPair d p).page1 = d.page1 ∧
      (finishPair d p).site.pages ≤ (Site.elect p).pages ∧
      ((finishPair d p).counter = d.counter ∨ (finishPair d p).site.pages = 0) := by
  fin_cases p <;> simp [finishPair, Site.pages]
  split_ifs <;> simp

private theorem next_pages {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) (hs : ∀ u, d.site ≠ .page u) :
    d'.page0 = d.page0 ∧ d'.page1 = d.page1 ∧ d'.site.pages ≤ d.site.pages ∧
      (d'.counter = d.counter ∨ d'.site.pages = 0) := by
  obtain ⟨s,i,n,a,b⟩ := d
  cases s with
  | page u => exact absurd rfl (hs u)
  | first | second =>
    obtain ⟨_, _, v, _, _, rfl⟩ := read_next hn
    simp [Site.pages]
  | elect p =>
    simp only [next] at hn
    split at hn
    · split at hn
      · cases hn; simp [Site.pages]
      · cases hn; exact finish_pages _ p
    · cases hn
  | copy p u =>
    cases u
    · simp only [next] at hn; cases hn; simp [Site.pages]
    · simp only [next] at hn; cases hn; exact finish_pages _ p
  | poll =>
    simp only [next] at hn
    split at hn
    · split at hn <;> cases hn <;> simp [Site.pages]
    · cases hn
  | dispatch => cases hn
  | _ =>
    simp only [next] at hn
    first | (split at hn <;> cases hn <;> simp [Site.pages]) | (cases hn; simp [Site.pages])

theorem pageRef_next {P : Nat → Value → Value → Prop} {L : Launch} {g : Nat} {d d' : D}
    {e : Event} (hr : PageRef P d) (hresp : PageResponse P d e)
    (hn : next L g d e = some (some d')) : PageRef P d' := by
  by_cases hp : ∃ u, d.site = .page u
  · obtain ⟨u, hu⟩ := hp
    obtain ⟨s,i,n,a,b⟩ := d
    change s = _ at hu
    subst hu
    cases u
    · obtain ⟨_, bs, v, he, hv, rfl⟩ := read_next hn
      have pv : P 0 i v := by
        have h := hresp
        simp only [PageResponse, he] at h
        exact h v hv
      exact ⟨fun _ => pv, nofun⟩
    · obtain ⟨_, bs, v, he, hv, rfl⟩ := read_next hn
      have pv : P 1 i v := by
        have h := hresp
        simp only [PageResponse, he] at h
        exact h v hv
      exact ⟨fun _ => hr.1 (by simp [Site.pages]), fun _ => pv⟩
  · push Not at hp
    obtain ⟨e0, e1, le, hc⟩ := next_pages hn hp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hr.1 (h.trans le)
      rcases hc with hc | hc
      · rw [e0, hc]; exact this
      · omega
    · have := hr.2 (h.trans le)
      rcases hc with hc | hc
      · rw [e1, hc]; exact this
      · omega

end PTX.Kernels.InklingRelDecode.Proof.Loader
