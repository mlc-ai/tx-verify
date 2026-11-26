-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.StagingHandoff
public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Step.BulkWaitReady
public import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # Publication and release of a staged buffer, by counts

A proof tool, generic over the kernel: the two hand-overs of `StagingHandoff`
(`Staging.Publish`, `Staging.Release`) stated with the counts a thread layer keeps, so that a
kernel applies them without finding the fence, the arrival and the wait itself. (The first two
arguments are written inline in FlashAttn4Fwd's `Protocol/OutputStaging.lean`.)

A thread accesses shared memory through the generic proxy, the copy engine (TMA) through the
asynchronous proxy. A thread access is ordered before a later asynchronous access of the same
byte only through a `fence.proxy.async` on a base-causality path from the access to the issue;
the source reads of an asynchronous store are ordered before a later thread access only
through a `.read` bulk-group wait that covers the store.

* `publish_of_unit`: **access → fence → release arrival → acquire poll → issue.** Given the unit
  hand-off of an mbarrier `m` (`MbarRing.UnitHandoff`), an access of a producer thread with at
  most `j` earlier arrivals on `m`, a proxy fence of that thread between the access and its
  next arrival on `m`, and an asynchronous operation a consumer thread issues after more than
  `j + δ` successful polls of `m`: the access is visible to the operation at every shared byte
  of the CTA that the operation covers.
* `release_of_unit`: **store → `.read` group wait → release arrival → acquire poll → access.**
  The source reads of a tensor store issued with at most `j` earlier arrivals on `m`, covered
  by a `.read` bulk-group wait of the issuing thread before its next arrival on `m`, are
  visible to an access of a consumer thread after more than `j + δ` successful polls of `m`.
* `publish_of_handoff`, `release_of_handoff`: the same through any hand-off order
  (`Frame.Handoff`: a CTA or named barrier by `Frame.Handoff.of_bar`, a composition): the fence
  (resp. the wait) has a producer use below the consumer use of the issue (resp. the access). -/

namespace PTX.Staging
open PTX.Flow AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Publication through an mbarrier unit hand-off.** -/
theorem publish_of_unit {m : Loc} {prod cons : Nat → Prop} {δ : Nat}
    (hH : MbarRing.UnitHandoff L X m prod cons δ) {g i h k j : Nat} {a : Acc} {w : Bool}
    {p : Part} {l : Loc} (hg : prod g) (hh : cons h) (hsame : SameCta L g h)
    (hacc : X.Access (g, i) a w) (hj : arrivals m ((X.tr g).take i) ≤ j)
    (hfence : ∀ e pce tx cnt rel sc, i < e →
      X.get (g, e) = some ⟨pce, .arrive m tx cnt rel sc⟩ →
      ∃ f pcf, i < f ∧ f < e ∧
        X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hk : k < (X.tr h).length) (hpolls : j + δ + 1 ≤ okPolls m ((X.tr h).take k))
    (hl : l.space = .shared) (hlc : l.cta = g / L.block) (hcov : AsyncCovers X (h, k) p l) :
    modelCausality L X l (.thread (g, i)) (.async (h, k) p) := by
  obtain ⟨w0, pcw, par, acq, sc, hw0, hwget, hwq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := m) (h := h) (f := k) (c := j + δ) hpolls
  obtain ⟨x, hx, hs⟩ := hH h w0 pcw par acq sc j hh hwget hwq g hg
  obtain ⟨ev, hev, harr⟩ := hs.arrives
  -- the arrival observed by the poll comes after the access
  have hgx : i < x := by
    have hle := MbarRing.arrival_index_ge (e := i) hev harr hx hj
    rcases Nat.lt_or_eq_of_le hle with h' | h'
    · exact h'
    · rcases hacc with ⟨bs, ⟨pcg, hgg⟩, -⟩ | ⟨bs, ⟨pcg, hgg⟩, -⟩ | ⟨o, n, pcg, hgg⟩ <;>
      · rw [← h'] at hev
        rw [hev] at hgg
        cases hgg
        simp [arrivesOn, sourceArrive] at harr
  obtain ⟨rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ := id hs
  obtain ⟨f, pcf, hgf, hfx, hfget⟩ := hfence x pcx tx cnt true rs hgx hxget
  have hpub : Staging.Publish L X (g, i) (g, f) (g, x) (h, w0) (h, k) m :=
    { isFence := ⟨pcf, hfget⟩
      fence_lt := hsame.1
      before := .single (.inl (po_of_not_access rfl hgf (len_of_get hfget)
        (by rw [hfget]; rfl)))
      release := hs
      arrive := ⟨rfl, hfx.le⟩
      issue := ⟨rfl, hw0, hk⟩
      cluster := ⟨hsame.1, hsame.2.1, by rw [hsame.2.2]⟩ }
  exact hpub.modelCausality hl hlc hcov

/-- **Release through an mbarrier unit hand-off.** -/
theorem release_of_unit (hX : Consistent L K A mem0 X) {m : Loc} {prod cons : Nat → Prop}
    {δ : Nat} (hH : MbarRing.UnitHandoff L X m prod cons δ) {h k g i j pc addr : Nat}
    {sp : TensorStore.Spec} {x y z : Nat} {l : Loc} (hh : prod h) (hg : cons g)
    (hi : X.get (h, k) = some ⟨pc, .tensorStore addr sp⟩)
    (hj : arrivals m ((X.tr h).take k) ≤ j)
    (hwaits : ∀ e pce tx cnt rel sc, k < e →
      X.get (h, e) = some ⟨pce, .arrive m tx cnt rel sc⟩ →
      ∃ w, k < w ∧ w < e ∧ BulkWaitsFor X .read (h, k) (h, w))
    (hlen : i < (X.tr g).length) (hpolls : j + δ + 1 ≤ okPolls m ((X.tr g).take i))
    (hcov : AsyncCovers X (h, k) (.read (.store x y z)) l) :
    modelCausality L X l (.async (h, k) (.read (.store x y z))) (.thread (g, i)) := by
  obtain ⟨w0, pcw, par, acq, sc, hw0, hwget, hwq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := m) (h := g) (f := i) (c := j + δ) hpolls
  obtain ⟨e, he, hs⟩ := hH g w0 pcw par acq sc j hg hwget hwq h hh
  obtain ⟨ev, hev, harr⟩ := hs.arrives
  -- the arrival observed by the poll comes after the store
  have hke : k < e := by
    have hle := MbarRing.arrival_index_ge (e := k) hev harr he hj
    rcases Nat.lt_or_eq_of_le hle with h' | h'
    · exact h'
    · rw [← h', hi] at hev
      cases hev
      simp [arrivesOn, sourceArrive] at harr
  obtain ⟨rs, ⟨tx, cnt, pce, heget⟩, -⟩ := id hs
  obtain ⟨w, hkw, hwe, hwait⟩ := hwaits e pce tx cnt true rs hke heget
  have hwj : arrivals m ((X.tr h).take w) ≤ j := by
    have := (List.take_sublist_take_left (l := X.tr h) hwe.le).countP_le (p := arrivesOn m)
    unfold arrivals at he ⊢
    omega
  have hrel : Staging.Release L X (h, k) (h, w) (g, i) :=
    { done := Step.BulkWait.stages_of_returned hX hwait
        (by have := len_of_get heget; simp only at this ⊢; omega)
      wait := hwait
      before := hH.baseCausality_of_counts (h := g) (g := h) (e := w) (f := i) (q := j) hg hh
        hwj hpolls hlen }
  exact hrel.modelCausality hcov

/-- **Publication through a hand-off order.** -/
theorem publish_of_handoff {pair : Nat → Nat → Prop} {up uq : EvId → Nat}
    (H : Frame.Handoff L X pair up uq) {g i f h k pcf : Nat} {p : Part} {l : Loc}
    (hif : i < f)
    (hfget : X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hpair : pair g h) (hsame : SameCta L g h) (hk : k < (X.tr h).length)
    (hlt : up (g, f) < uq (h, k))
    (hl : l.space = .shared) (hlc : l.cta = g / L.block) (hcov : AsyncCovers X (h, k) p l) :
    modelCausality L X l (.thread (g, i)) (.async (h, k) p) :=
  ⟨hcov, .inl ⟨(g, f), _, _, ⟨pcf, hfget⟩, hsame.1, ⟨hl, hlc⟩,
    ⟨hsame.1, hsame.2.1, by rw [hsame.2.2]⟩,
    .single (.inl (po_of_not_access rfl hif (len_of_get hfget) (by rw [hfget]; rfl))),
    H g h f k hpair hk hlt⟩⟩

/-- **Release through a hand-off order.** -/
theorem release_of_handoff (hX : Consistent L K A mem0 X) {pair : Nat → Nat → Prop}
    {up uq : EvId → Nat} (H : Frame.Handoff L X pair up uq) {h k w g i : Nat} {x y z : Nat}
    {l : Loc} (hwait : BulkWaitsFor X .read (h, k) (h, w)) (hw : w + 1 < (X.tr h).length)
    (hpair : pair h g) (hlen : i < (X.tr g).length) (hlt : up (h, w) < uq (g, i))
    (hcov : AsyncCovers X (h, k) (.read (.store x y z)) l) :
    modelCausality L X l (.async (h, k) (.read (.store x y z))) (.thread (g, i)) :=
  (Staging.Release.mk (Step.BulkWait.stages_of_returned hX hwait hw) hwait
    (H h g w i hpair hlen hlt)).modelCausality hcov

end PTX.Staging
