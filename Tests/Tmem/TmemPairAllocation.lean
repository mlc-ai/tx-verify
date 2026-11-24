-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemLifetime
public import Lemmas.Tmem.TmemPairHistory

namespace PTX.Tests.TmemPairAllocation
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def w (cta : Nat) : WarpRequest :=
  ⟨cta, 0, fun _ => 0, 0, some ⟨.shared, cta, 0⟩, .alloc 32⟩
private def r0 : Requests := ⟨w 0, .two, .alloc 32 0⟩
private def r1 : Requests := ⟨w 1, .two, .alloc 32 128⟩
private def events (v : WarpRequest) (base : Nat) : List Event :=
  [⟨v.pc, .tc (.resource .two v.dst v.request)⟩, ⟨1, .tc (.ld base [.bits 32 0] .s32x32b)⟩]
private def X : Execution := {
  tr := fun g => if g < 32 then events (w 0) 0 else
    if g < 64 then events (w 1) 128 else [],
  rf := fun _ _ => none,
  tmemHistory := fun cta => if cta = 0 then [r0] else if cta = 1 then [r1] else [],
  tmemPairing := [(w 0, w 1)] }

private theorem valid0 : (w 0).Valid L X .two := by
  have hev : ∀ lane : Fin 32, X.get (WarpRequest.event L (w 0) lane) =
      some ⟨(w 0).pc, .tc (.resource .two (w 0).dst (w 0).request)⟩ := by
    intro lane
    simp [WarpRequest.event, w, L, X, Execution.get, events, lane.isLt]
  exact ⟨by decide, by decide, hev, 0,
    fun lane => ⟨⟨_, hev lane, rfl⟩, by simp [WarpRequest.event, w, L]⟩⟩

private theorem valid1 : (w 1).Valid L X .two := by
  have hev : ∀ lane : Fin 32, X.get (WarpRequest.event L (w 1) lane) =
      some ⟨(w 1).pc, .tc (.resource .two (w 1).dst (w 1).request)⟩ := by
    intro lane
    have h1 : ¬ 32 + lane.val < 32 := by omega
    have h2 : 32 + lane.val < 64 := by omega
    simp [WarpRequest.event, w, L, X, Execution.get, events, h1, h2]
  exact ⟨by decide, by decide, hev, 0,
    fun lane => ⟨⟨_, hev lane, rfl⟩, by simp [WarpRequest.event, w, L]⟩⟩

-- Each CTA's allocator performed its own half, at its own address; the halves are paired.
example : r0.Valid L X := ⟨by decide, rfl, valid0⟩
example : r1.Valid L X := ⟨by decide, rfl, valid1⟩
example : PairValid L X (w 0, w 1) := by
  refine ⟨by decide, valid0, valid1, ?_, by decide, by decide, rfl⟩
  unfold SameCtaGroup CtaInCluster Launch.ctaGroupRanks CtaGroup.size
  decide

private theorem left_covers : Covers L X r0 0 (0, 1) 0 := by
  refine ⟨32, 0, rfl, rfl, by decide, by decide, ?_⟩
  exact .inl (.single (.inl ⟨rfl, by decide, by decide⟩))

example : r0 ∈ X.tmemHistory 0 ∧ Covers L X r0 0 (0, 1) 0 :=
  ⟨by simp [X], left_covers⟩

example : r1 ∈ X.tmemHistory 1 ∧ Covers L X r1 1 (32, 1) 128 := by
  refine ⟨by simp [X], 32, 128, rfl, rfl, by decide, by decide, ?_⟩
  exact .inl (.single (.inl ⟨rfl, by decide, by decide⟩))

-- Pairing does not copy CTA zero's column range into CTA one's TMEM.
example : ¬ Covers L X r0 1 (32, 1) 0 := by
  rintro ⟨n, base, he, hc, _, _, _⟩
  change 1 = 0 at hc
  omega

example : ¬ Covers L X r1 1 (32, 1) 0 := by
  rintro ⟨n, base, he, _, hlo, _, _⟩
  have hb : base = 128 := by cases he; rfl
  subst base
  omega

-- A cell immediately outside the allocated range is not covered.
example : ¬ Covers L X r0 0 (0, 1) 32 := by
  rintro ⟨n, base, he, _, _, hhi, _⟩
  have hn : n = 32 := by cases he; rfl
  have hb : base = 0 := by cases he; rfl
  omega

-- Even with a fresh allocation, a source ordered before the old release is invalid.
example (Y : Execution) (x e d : EvId) (cell : TcMma.Cell)
    (cta : Nat) (r : Requests) (ha : ∀ n, ¬ Relation.TransGen (TcMma.TcStep L Y) n n)
    (hr : r ∈ Y.tmemHistory cta) (hc : Covers L Y r cell.cta e cell.column)
    (hd : ReleaseOf L Y r d)
    (hxd : baseCausality L Y x d) (hde : baseCausality L Y d e) (hl : ∃ a vals sh, Y.TLd e a vals
        sh) :
    ¬ TcMma.SourceLive L Y x e cell := by
  intro hs
  exact hs.no_release_between ha hr hc hd hxd hde (.inl hl)

/-! EXT-PAIR-ALLOC-ORDER: thread 0 (CTA 0) accesses CTA 1's column 128 after its own half of the
paired allocation. CTA 1's allocation event, which nothing orders before the access, does not
cover the cell by itself (`Allocated` fails). The paired peer request's event (thread 0's own
allocation) happens before the access, so CTA 1's record covers it through the pairing, with no
assumption: accepted. An event that no event of the peer request happens before is covered by
neither route: rejected. -/

/-- No step of `hb` in `X` enters thread 0 from another thread, nor any thread at its first
event. -/
private theorem no_fence : ∀ (e : EvId) sem s, ¬ X.ThreadFence e sem s := by
  rintro ⟨x1, x2⟩ sem s ⟨pc, hg⟩
  simp only [Execution.get] at hg
  have hmem := List.mem_of_getElem? hg
  have hkind : ∀ ev ∈ X.tr x1, ev.kind = Kind.fence sem s → False := by
    intro ev hev hk
    by_cases h1 : x1 < 32
    · rw [show X.tr x1 = events (w 0) 0 from by simp [X, h1]] at hev
      simp [events] at hev
      rcases hev with rfl | rfl <;> simp at hk
    · by_cases h2 : x1 < 64
      · rw [show X.tr x1 = events (w 1) 128 from by simp [X, h1, h2]] at hev
        simp [events] at hev
        rcases hev with rfl | rfl <;> simp at hk
      · rw [show X.tr x1 = [] from by simp [X, h1, h2]] at hev
        simp at hev
  exact hkind _ hmem rfl

private theorem step_into {x : EvId} {y : EvId} (hy : y.1 < 32)
    (h : po X x y ∨ CtaBarSync L X x y ∨ MSync L X x y ∨ ClusterSync L X x y ∨
      WarpBarSync L X x y ∨ synchronizesWith L X x y ∨ FenceSync L X x y) :
    x.1 = y.1 ∧ x.2 < y.2 := by
  obtain ⟨y1, y2⟩ := y
  dsimp only at hy
  have ev : ∀ j, j < y2 → y2 < (X.tr y1).length → j = 0 := by
    intro j hj hl
    have : (X.tr y1).length = 2 := by simp [X, hy, events]
    omega
  rcases h with ⟨h1, h2, -⟩ | ⟨-, k, i, j, -, ⟨-, ⟨c, pc, hb⟩, -⟩, -, hj, hl⟩ |
    ⟨x', w, m, rs, as, -, ⟨⟨pc, par, hw⟩, -⟩, -, hw1, hw2, hl, -⟩ |
    ⟨-, i, j, ⟨ph, ⟨i', s, t, cta, warp, lanes, g, hc, -⟩, -⟩, -⟩ |
    ⟨i, j, ⟨-, mask, inst, -, pc, hb⟩, -, hj, hl⟩ |
    ⟨a', b', bs, cs, -, -, -, -, -, -, hs, -, -, hrf⟩ | hfs
  · exact ⟨h1, h2⟩
  · obtain rfl := ev j hj hl
    simp [Execution.IsBarrier, Execution.get, X, hy, events] at hb
  · obtain ⟨w1, w2⟩ := w
    dsimp only at hw1 hw2
    subst hw1
    obtain rfl := ev w2 hw2 hl
    simp [Execution.get, X, hy, events] at hw
  · simp [X] at hc
  · obtain rfl := ev j hj hl
    simp [Execution.get, X, hy, events] at hb
  · have := hrf 0 hs
    simp [X] at this
  · exact absurd hfs (not_fenceSync_of_noFence no_fence x (y1, y2))

/-- Nothing in `X` happens before thread 0's first event. -/
private theorem baseCausality_first {z : EvId} : ¬ baseCausality L X z (0, 0) := by
  intro hz
  cases hz with
  | single h => have := step_into (by decide) h; omega
  | tail _ h => have := step_into (by decide) h; omega

/-- Nothing in `X` happens before thread 0's access at index 1 but thread 0's earlier event. -/
private theorem baseCausality_into {x : EvId} (h : baseCausality L X x (0, 1)) : x = (0, 0) := by
  cases h with
  | single h =>
    obtain ⟨h1, h2⟩ := step_into (by decide) h
    obtain ⟨x1, x2⟩ := x
    simp only at h1 h2
    subst h1
    rw [show x2 = 0 by omega]
  | tail h' h =>
    rename_i z
    obtain ⟨h1, h2⟩ := step_into (by decide) h
    obtain ⟨z1, z2⟩ := z
    simp only at h1 h2
    subst h1
    rw [show z2 = 0 by omega] at h'
    exact absurd h' baseCausality_first

private def peerCell : TcMma.Cell := ⟨1, 0, 128⟩

-- Own route: CTA 1's allocation event is not published to thread 0's access.
example : ¬ (∃ cta r, r ∈ X.tmemHistory cta ∧ ∃ n base, r.action = .alloc n base ∧
    1 = r.own.cta ∧ base ≤ peerCell.column ∧ peerCell.column < base + n ∧
    baseCausality L X (r.own.event L 0) (0, 1)) := by
  rintro ⟨cta, r, hr, n, base, ha, ho, -, -, hb⟩
  have hx := baseCausality_into hb
  have hc : r.own.cta = 1 := ho.symm
  have : (r.own.event L 0).1 = 0 := by rw [hx]
  simp [WarpRequest.event, L, hc] at this

-- Paired route: the peer request's lane-0 event (thread 0's own allocation) covers CTA 1's cell.
private theorem paired : Covers L X r1 peerCell.cta (0, 1) peerCell.column := by
  refine ⟨32, 128, rfl, rfl, by decide, by decide, .inr ⟨(w 0, w 1), by simp [X], w 0,
    .inr ⟨rfl, rfl⟩, 0, ?_⟩⟩
  exact .single (.inl ⟨rfl, by decide, by decide⟩)

-- CTA 1's record covers the access, so the release check of `AccessSafe` applies to it.
example : Covers L X r1 peerCell.cta (0, 1) peerCell.column := paired

-- The access is allocated (the allocated-before-access conjunct of `AccessSafe`, and the source
-- conjunct of `TcMma.ReadSource`).
example : r1 ∈ X.tmemHistory 1 ∧ Covers L X r1 peerCell.cta (0, 1) peerCell.column :=
  ⟨by simp [X], paired⟩

-- Not ordered after the peer request: thread 0's allocation event, which no event of the peer
-- request (nor CTA 1's own allocation event) happens before, is covered by neither route.
example : ¬ (∃ cta r, r ∈ X.tmemHistory cta ∧
    Covers L X r peerCell.cta (0, 0) peerCell.column) := by
  rintro ⟨cta, r, hr, n, base, -, -, -, -, hb | ⟨q, hq, p, -, lane, hb⟩⟩
  · exact baseCausality_first hb
  · exact baseCausality_first hb

end
end PTX.Tests.TmemPairAllocation
