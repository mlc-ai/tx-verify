-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Protocol.Order
public import Lemmas.Protocol.RegionOrder
public import Lemmas.Execution.NoAsync

@[expose] public section

/-! # The accesses and their conflicts

Every access of a thread is a word of global or of its CTA's shared memory (`Shape`): a global
read is an input or a weight, a global write is an output of the thread's own rows, a shared
access below the reduction words is in the thread's own staging slots, and the reduction words
are written by the warps' lanes `0` and thread `0` and read by warp `0`'s lanes and all threads.
So two overlapping accesses, one a write, are of one thread, or are a write and a read of a
reduction word in one CTA, ordered by the barriers between them (`overlap_cases`). Conflicting
accesses are therefore ordered (`conflicts_ordered`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The footprint of an access of thread `g` at state `d`, writing if `w`. -/
structure Shape (P : Params) (g : Nat) (d : D) (a : Acc) (w : Bool) : Prop where
  size : a.size = 4
  align : a.loc.addr % 4 = 0
  space : a.loc.space = .global ∨ a.loc.space = .shared
  global : a.loc.space = .global → a.loc.cta = 0 ∧
    (w = true → P.O ≤ a.loc.addr ∧ a.loc.addr < P.O + 8192 * P.Bt ∧
      (a.loc.addr - P.O) / 8192 % 152 = g / 256 ∧ (a.loc.addr - P.O) % 4096 / 16 = g % 256) ∧
    (w = false → (P.I ≤ a.loc.addr ∧ a.loc.addr < P.I + 8192 * P.Bt) ∨
      (P.W ≤ a.loc.addr ∧ a.loc.addr < P.W + 8192))
  shared : a.loc.space = .shared → a.loc.cta = g / 256 ∧ P.S ≤ a.loc.addr ∧
    a.loc.addr < P.S + 16416 ∧
    (a.loc.addr < P.S + 16384 → (a.loc.addr - P.S) % 8192 / 32 = g % 256) ∧
    (P.S + 16384 ≤ a.loc.addr →
      (d.site = .stws ∧ w = true ∧ a.loc.addr = P.S + 16384 + 4 * (g % 256 / 32) ∧
        g % 256 % 32 = 0) ∨
      (d.site = .stts ∧ w = true ∧ a.loc.addr = P.S + 16384 ∧ g % 256 = 0) ∨
      (d.site = .ldws ∧ w = false ∧ a.loc.addr = P.S + 16384 + 4 * (g % 256 % 32) ∧ g % 256 < 8) ∨
      (d.site = .ldts ∧ w = false ∧ a.loc.addr = P.S + 16384))

theorem row_lt {g : Nat} {d : D} (hi : Inv P g d) (hr : d.site.inRow = true) :
    g / 256 + 152 * d.i < P.Bt := hi.row hr

/-- Close a case of `Shape`: unfold the footprint and decide the address arithmetic. -/
macro "shape_close" hs:ident : tactic => `(tactic| (
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp only [$hs:ident, vacc, off, row, reduceCtorEq, false_implies, true_implies, forall_const,
      Bool.false_eq_true, Bool.true_eq_false, true_and, and_true, false_and, and_false, or_false,
      false_or, true_or, or_true, and_self, imp_self, implies_true] <;>
    omega))

variable (hpre : Pre P L mem0)
include hpre

/-- **The footprint of a read.** -/
theorem read_shape {g pc : Nat} {d : D} {a : Acc} {bs : List (Option Byte)} (hi : Inv P g d)
    (he : SiteEvent P g d ⟨pc, .rd a bs⟩) : Shape P g d a false := by
  have hS := hpre.hyp.sharedAlign
  have hI := hpre.hyp.inAlign
  have hW := hpre.hyp.wAlign
  have hsub := hi.sub.1
  have h8 := hi.ldws
  rcases rd_site he with ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ |
    ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩ <;>
    have hr := hi.row (by simp [hs, Site.inRow]) <;>
    simp only [hs, Site.vec, row, forall_const, reduceCtorEq, false_implies]
      at hsub hr h8 <;>
    shape_close hs

/-- **The footprint of a write.** -/
theorem write_shape {g pc : Nat} {d : D} {a : Acc} {bs : List Byte} (hg : g / 256 < 152)
    (hi : Inv P g d) (he : SiteEvent P g d ⟨pc, .wr a bs⟩) : Shape P g d a true := by
  have hS := hpre.hyp.sharedAlign
  have hO := hpre.hyp.outAlign
  have hsub := hi.sub.1
  have h0 := hi.stws
  have h1 := hi.stts
  rcases wr_site he with ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ |
    ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ | ⟨hs, rfl, -⟩ <;>
    have hr := hi.row (by simp [hs, Site.inRow]) <;>
    simp only [hs, Site.vec, row, forall_const, reduceCtorEq, false_implies] at hsub hr h0 h1 <;>
    shape_close hs

omit hpre in
/-- Two overlapping words are one word. -/
theorem loc_eq_of_overlap {a b : Acc} (ha : a.size = 4) (hb : b.size = 4) (ha4 : a.loc.addr % 4 = 0)
    (hb4 : b.loc.addr % 4 = 0) (hov : a.Overlap b) : a.loc = b.loc := by
  obtain ⟨l, ⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩ := hov
  rw [ha] at h4
  rw [hb] at h8
  cases hA : a.loc
  cases hB : b.loc
  rw [hA] at h1 h2 h3 h4 ha4
  rw [hB] at h5 h6 h7 h8 hb4
  simp only at *
  refine Loc.mk.injEq _ _ _ _ _ _ ▸ ⟨h1.symm.trans h5, h2.symm.trans h6, by omega⟩

/-- **Two overlapping accesses, one a write**, are of one thread, or are a write and a read of a
reduction word of one CTA, the write before the read's barrier or after it. -/
theorem overlap_cases {x y : Nat} {dx dy : D} {a b : Acc} {wx wy : Bool}
    (hx : Shape P x dx a wx) (hy : Shape P y dy b wy) (hov : a.Overlap b)
    (hw : wx = true ∨ wy = true) :
    x = y ∨ x / 256 = y / 256 ∧
      ((dx.bc0 < dy.bc0 ∨ dx.bc1 < dy.bc1) ∨ (dy.bc0 < dx.bc0 ∨ dy.bc1 < dx.bc1)) := by
  have hl := loc_eq_of_overlap hx.size hy.size hx.align hy.align hov
  have hA : b.loc.addr = a.loc.addr := by rw [hl]
  have hC : b.loc.cta = a.loc.cta := by rw [hl]
  have hIO := hpre.disjIO
  have hWO := hpre.disjWO
  rcases hx.space with hg | hs
  · have hg' : b.loc.space = .global := hl ▸ hg
    obtain ⟨-, hW, hR⟩ := hx.global hg
    obtain ⟨-, hW', hR'⟩ := hy.global hg'
    left
    cases wx <;> cases wy <;> simp only [Bool.false_eq_true, or_self, Bool.true_eq_false,
      false_implies, forall_const] at hw hW hR hW' hR' <;> omega
  · have hs' : b.loc.space = .shared := hl ▸ hs
    obtain ⟨hc, hlo, hhi, hst, hred⟩ := hx.shared hs
    obtain ⟨hc', hlo', hhi', hst', hred'⟩ := hy.shared hs'
    by_cases hlt : a.loc.addr < P.S + 16384
    · left
      have := hst hlt
      have := hst' (by omega)
      omega
    · rcases hred (by omega) with ⟨h1, rfl, h2, h3⟩ | ⟨h1, rfl, h2, h3⟩ | ⟨h1, rfl, h2, h3⟩ |
        ⟨h1, rfl, h2⟩ <;>
      rcases hred' (by omega) with ⟨h1', rfl, h2', h3'⟩ | ⟨h1', rfl, h2', h3'⟩ |
        ⟨h1', rfl, h2', h3'⟩ | ⟨h1', rfl, h2'⟩ <;>
      simp only [D.bc0, D.bc1, h1, h1', Bool.false_eq_true, or_self] at hw ⊢ <;>
      omega

omit hpre in
theorem noTma : kernel.NoTma := by unfold Kernel.NoTma; decide +kernel

omit hpre in
theorem cta_of_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : g / 256 < 152 := by
  have := hpre.hyp.grid
  have := hpre.hyp.block
  simp only [Launch.threads] at hg
  simp_all
  omega

variable (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hX ht

/-- **The facts of an access**: its event, the state it fires from and its footprint. -/
theorem access_facts {e : EvId} {a : Acc} {w : Bool} (ha : X.Access e a w) :
    e.1 < L.threads ∧ ∃ d ev, X.get e = some ev ∧ At P L X e.1 e.2 d ev ∧ Shape P e.1 d a w ∧
      ∀ pc id c, ev ≠ ⟨pc, .bar id c⟩ := by
  obtain ⟨g, k⟩ := e
  rcases ha with ⟨bs, ⟨pc, hr⟩, rfl⟩ | ⟨bs, ⟨pc, hw⟩, rfl⟩ | ⟨o, n, pc, hm⟩
  · obtain ⟨hg, d, hA⟩ := event_facts hpre hX ht hr (by intro _ _ h; cases h)
    exact ⟨hg, d, _, hr, hA, read_shape hpre hA.inv hA.event, by intro _ _ _ h; cases h⟩
  · obtain ⟨hg, d, hA⟩ := event_facts hpre hX ht hw (by intro _ _ h; cases h)
    exact ⟨hg, d, _, hw, hA, write_shape hpre (cta_of_lt hpre hg) hA.inv hA.event,
      by intro _ _ _ h; cases h⟩
  · obtain ⟨-, d, hA⟩ := event_facts hpre hX ht hm (by intro _ _ h; cases h)
    exact (rmw_site hA.event).elim

/-- **No event is an atomic read-modify-write.** -/
theorem no_rmw {e : EvId} {pc : Nat} {a : Acc} {o : List (Option Byte)} {n : Option (List Byte)} :
    X.get e ≠ some ⟨pc, .rmw a o n⟩ := by
  intro h
  obtain ⟨-, d, hA⟩ := event_facts hpre hX ht h (by intro _ _ h; cases h)
  exact rmw_site hA.event

/-- A thread's write to memory is a write event. -/
theorem writes_of_memWrites {i : EvId} {a : Acc} {bs : List Byte}
    (h : X.Writes i a bs ∨ ∃ old, X.Rmw i a old (some bs)) : X.Writes i a bs :=
  h.elim id fun ⟨_, _, hp⟩ => absurd hp (no_rmw hpre hX ht)

omit hpre hX ht in
/-- Overlapping accesses of one thread are ordered by the program. -/
theorem po_baseCausality {g i j : Nat} {a b : Acc} {wa wb : Bool} (ha : X.Access (g, i) a wa)
    (hb' : X.Access (g, j) b wb) (hlt : i < j) (hov : a.Overlap b) : baseCausality L X (g, i) (g,
        j) :=
  .single (.inl (po_of_overlap ha hb' rfl hlt hov))

/-- **Overlapping accesses, one a write, are ordered.** -/
theorem access_ordered {e f : EvId} {a b : Acc} {we wf : Bool} (he : X.Access e a we)
    (hf : X.Access f b wf) (hne : e ≠ f) (hov : a.Overlap b) (hw : we = true ∨ wf = true) :
    baseCausality L X e f ∨ baseCausality L X f e := by
  obtain ⟨x, kx⟩ := e
  obtain ⟨y, ky⟩ := f
  obtain ⟨-, dx, ex, hx, hAx, hsx, hnx⟩ := access_facts hpre hX ht he
  obtain ⟨-, dy, ey, hy, hAy, hsy, hny⟩ := access_facts hpre hX ht hf
  rcases overlap_cases hpre hsx hsy hov hw with rfl | ⟨hc, h | h⟩
  · have hk : kx ≠ ky := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
    · exact .inl (po_baseCausality he hf hlt hov)
    · exact .inr (po_baseCausality hf he hlt hov.symm)
  · exact .inl (baseCausality_of_counts hpre hX ht hx hAx hy hAy hnx hc h)
  · exact .inr (baseCausality_of_counts hpre hX ht hy hAy hx hAx hny hc.symm h)

/-- **Conflicting accesses are ordered.** -/
theorem conflicts_ordered : ConflictsOrdered L X fun _ => True := by
  intro e f a b l ⟨hne, we, wf, he, hf, hw, hov⟩ _ _ _
  have hn := noTma_of_consistent noTma hX
  obtain ⟨e, rfl, he⟩ := Execution.NoTma.intent_thread hn he
  obtain ⟨f, rfl, hf⟩ := Execution.NoTma.intent_thread hn hf
  exact (access_ordered hpre hX ht he hf (fun h => hne (by rw [h])) hov hw).elim
    (fun h => .inl (.inl h)) (fun h => .inr (.inl h))

end
end PTX.Kernels.RmsNorm.Proof
