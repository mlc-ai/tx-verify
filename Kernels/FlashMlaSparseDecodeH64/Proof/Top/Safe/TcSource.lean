-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # An event in the tcgen05 order below another is no undefined behaviour

`tcStep_nonUb`: the source of a step of the tcgen05 order (`TcMma.TcStep`) is no undefined
behaviour. A source is before a later event of its lane (program order, a barrier arrival, a
barrier wait, an MMA's commit) or is an event of a kind that is none (an arrival, a store, a fence).
So the facts of the events below an event hold for each of them, whatever the kind of the event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {L : Launch} {m : Mem0} {X : Execution}

private theorem nu_succ (hX : Consistent L kernel Assumptions.all m X) {x j i : Nat} {e : Event}
    (he : X.get (x, j) = some e) (hi : j < i) (hl : i < (X.tr x).length) :
    ∀ f, e.kind ≠ .ub f := noUb_kind_of_lt hX he hi hl

private theorem nu_kind {a : EvId} {e : Event} {k : Kind} {pc : Nat}
    (he : X.get a = some e) (h : X.get a = some ⟨pc, k⟩) (hk : ∀ f, k ≠ .ub f) :
    ∀ f, e.kind ≠ .ub f := by
  rw [he] at h
  obtain rfl := Option.some.inj h
  exact hk

private theorem len_of {x j : Nat} {ev : Event} (h : X.get (x, j) = some ev) :
    j < (X.tr x).length := (List.getElem?_eq_some_iff.mp h).1

/-- The source of a step of the program order, a synchronization or a fence order. -/
private theorem step_nonUb (hX : Consistent L kernel Assumptions.all m X) {a b : EvId} {e : Event}
    (h : po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b)
    (he : X.get a = some e) : ∀ f, e.kind ≠ .ub f := by
  obtain ⟨x, j⟩ := a
  rcases h with ⟨rfl, hj, hb, -⟩ | ⟨-, key, i, j', ⟨-, ⟨c, pc, mode, hg⟩, -⟩, -, hi, -⟩ |
    ⟨x', w, mm, rs, as, ⟨tx, c, pc, hg⟩, -, -, -, -, -, hx, hjx⟩ |
    ⟨-, i, j', -, hl, hi, -⟩ |
    ⟨i, j', ⟨-, mask, inst, ⟨pc, hg⟩, -⟩, hi, -⟩ | ⟨a', b', bs, cs, hw, -⟩ | hF
  · exact nu_succ hX he hj hb
  · exact nu_succ hX he hi (len_of hg)
  · obtain ⟨x1, x2⟩ := x'
    subst hx
    rcases Nat.lt_or_ge j x2 with h | h
    · exact nu_succ hX he h (len_of hg)
    · obtain rfl : j = x2 := by simp only at hjx; omega
      exact nu_kind he hg (fun _ h => by cases h)
  · exact nu_succ hX he hi hl
  · exact nu_succ hX he hi (len_of hg)
  · rcases hw with ⟨pc, hg⟩ | ⟨old, pc, hg⟩
    · exact nu_kind he hg (fun _ h => by cases h)
    · exact nu_kind he hg (fun _ h => by cases h)
  · rcases hF with ⟨w, r, a', b', bs, cs, se, sf, hw, -, -, hrel, -, -⟩ | ⟨⟨s, s', hs, -, -⟩, -⟩
    · rcases hrel with ⟨rfl, -⟩ | ⟨sem, ⟨pc, hg⟩, -, -, -⟩
      · rcases hw with ⟨pc, hg⟩ | ⟨old, pc, hg⟩
        · exact nu_kind he hg (fun _ h => by cases h)
        · exact nu_kind he hg (fun _ h => by cases h)
      · exact nu_kind he hg (fun _ h => by cases h)
    · obtain ⟨pc, hg⟩ := hs
      exact nu_kind he hg (fun _ h => by cases h)

/-- **The source of a step of the tcgen05 order is no undefined behaviour.** -/
theorem tcStep_nonUb (hX : Consistent L kernel Assumptions.all m X) {a b : EvId}
    (h : TcMma.TcStep L X a b) {e : Event} (he : X.get a = some e) : ∀ f, e.kind ≠ .ub f := by
  rcases h with hb | ⟨mm, tx, c, rel, rs, acq, ws, ⟨pc, hg⟩, -⟩ |
    ⟨acq, ws, ⟨n, mm, ⟨commit, s, rank, -, ⟨hc1, hc2, -, s', ⟨pc, hg⟩⟩, -⟩, -⟩, -⟩
  · induction hb using Relation.TransGen.head_induction_on with
    | single hs => exact step_nonUb hX hs he
    | head hs _ _ => exact step_nonUb hX hs he
  · exact nu_kind he hg (fun _ h => by cases h)
  · obtain ⟨x, j⟩ := a
    obtain ⟨cx, cj⟩ := commit
    simp only at hc1 hc2 hg
    subst hc1
    exact nu_succ hX he hc2 (len_of hg)

/-- **An event below another in the tcgen05 order is no undefined behaviour.** -/
theorem tcTrans_nonUb (hX : Consistent L kernel Assumptions.all m X) {a b : EvId}
    (h : Relation.TransGen (TcMma.TcStep L X) a b) {e : Event} (he : X.get a = some e) :
    ∀ f, e.kind ≠ .ub f := by
  induction h using Relation.TransGen.head_induction_on with
  | single hs => exact tcStep_nonUb hX hs he
  | head hs _ _ => exact tcStep_nonUb hX hs he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
