-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Address
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Tmem.TmemPairRecord

@[expose] public section

/-! # `tc_gemm`: the Tensor Memory allocator's history

Every recorded request is warp 0's allocation of 32 columns (`allocReq`) or its release of the
column it kept (`deallocReq`), of `cta_group::1`, in CTA 0 (`rec_shape`); nothing is paired
(`pairing_nil`). The allocation is performed once lane 0 has passed it (`alloc_covered`), at the
column lane 0 stores (`alloc_base`, OBJ-TMEM-ALLOC-RESULT) that leaves room for 32 columns
(`base_room`), and the release only after it. So the history is empty, the allocation, or the
allocation then the release (`history_shape`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow Tmem.Pair

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hW

omit hX hpre in
/-- An allocation event, and its first warp-collective instance. -/
theorem talloc_at {g : Nat} (hg : g / 32 = 0) (hm : 0 < m g) :
    X.get (g, 0) = some (allocE L.sharedBase) ∧ X.TcK (g, 0) 0 := by
  have hget : X.get (g, 0) = some (allocE L.sharedBase) := by
    rw [hW.get_of_lt (by omega) hm, fullAt_head _ (by unfold hd; split_ifs <;> omega)]
    unfold headE; split_ifs <;> rfl
  exact ⟨hget, ⟨⟨_, hget, rfl⟩, by simp⟩⟩

omit hX hpre in
/-- Lane 0's address store, once performed. -/
theorem tslot_at (hm : 1 < m 0) : X.get (0, 1) = some (tslotE L.sharedBase (P 0).col) := by
  rw [hW.get_of_lt (by decide) hm, fullAt_head _ (by unfold hd; simp)]
  rfl

/-- The request of warp 0's allocation. -/
def allocReq (S col : Nat) : Requests :=
  ⟨⟨0, 0, fun _ => 0, Flow.tmemAlloc_0, some (tslot S), .alloc 32⟩, .one, .alloc 32 col⟩

/-- The request of warp 0's release. -/
def deallocReq (P : Nat → Par) : Requests :=
  ⟨⟨0, 0, fun lane => ldIdx lane.val (P lane.val) + 13, Flow.tmemDealloc_0, none, .dealloc (P 0).c
    32⟩, .one,
    .dealloc (P 0).c 32⟩

omit hX in
include hpre in
/-- An actual warp request of this kernel is warp 0's allocation or its release, of
cta_group::1. -/
theorem own_shape {w : WarpRequest} {grp : CtaGroup} (hv : w.Valid L X grp) :
    grp = .one ∧ (w = (allocReq L.sharedBase 0).own ∨ w = (deallocReq P).own) := by
  have hT := threads_eq hpre
  have hB := hpre.block
  obtain ⟨hcta, -, hev, -⟩ := hv
  have hc0 : w.cta = 0 := by rw [hpre.grid] at hcta; omega
  have hl : ∀ lane : Fin 32, X.get (w.warp * 32 + lane.val, w.indices lane) =
      some ⟨w.pc, .tc (.resource grp w.dst w.request)⟩ := by
    intro lane; rw [← hev lane]; simp [WarpRequest.event, hc0]
  have hshape := hW.resource (hl 0)
  have hg1 : grp = .one := by rcases hshape with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> exact h
  subst hg1
  refine ⟨rfl, ?_⟩
  obtain ⟨c0, w, i, p, dst, req⟩ := w
  simp only at hc0 hl hshape
  subst hc0
  cases req with
  | alloc n =>
    obtain ⟨d, n', -, rfl, he⟩ | ⟨_, _, -, -, he⟩ := hshape
    swap; · cases he
    cases he
    have h0 := hW.talloc (hl 0)
    obtain ⟨hg, hjm, h32, hi0, hd, hn⟩ := h0
    have hw0 : w = 0 := by simp at h32; omega
    subst hw0 hd hn
    have hi : ∀ lane : Fin 32, i lane = 0 := fun lane => (hW.talloc (hl lane)).2.2.2.1
    have hp : p = Flow.tmemAlloc_0 := by
      have := hl 0
      rw [hi0] at this
      rw [hW.get_of_lt (by decide) (by simpa [hi0] using hjm), fullAt_head _ (by decide)] at this
      simp [headE, allocE] at this
      exact this.symm
    left
    subst hp
    simp [allocReq, funext hi]
  | relinquish =>
    obtain ⟨_, _, -, -, he⟩ | ⟨_, _, -, -, he⟩ := hshape <;> cases he
  | dealloc ta n =>
    obtain ⟨_, _, -, -, he⟩ | ⟨ta', n', -, rfl, he⟩ := hshape
    · cases he
    cases he
    have h0 := hW.tdealloc (hl 0)
    obtain ⟨-, -, h32, -, hta, hn⟩ := h0
    have hw0 : w = 0 := by simp at h32; omega
    subst hw0 hn
    have hi : ∀ lane : Fin 32, i lane = ldIdx lane.val (P lane.val) + 13 := by
      intro lane; have := (hW.tdealloc (hl lane)).2.2.2.1; simpa using this
    have hp : p = Flow.tmemDealloc_0 := by
      have hx := hl 0
      have hidx := hi 0
      try simp at hidx hx
      rw [hidx] at hx
      have hj := (hW.tdealloc hx).2.1
      rw [hW.get_of_lt (by decide) hj, show ldIdx 0 (P 0) + 13 = ldIdx 0 (P 0) + 1 + 12 by omega,
        fullAt_post] at hx
      simp [postAt, deallocE] at hx
      exact hx.1.symm
    right
    subst hp
    rw [hta]
    simp [deallocReq, funext hi]

include hpre hX in
/-- A recorded request is warp 0's allocation or its release. -/
theorem rec_shape {key : Nat} {r : Requests} (hr : r ∈ X.tmemHistory key) :
    key = 0 ∧ ((∃ col, r = allocReq L.sharedBase col) ∨ r = deallocReq P) := by
  obtain ⟨hval, hkey, -⟩ := hX.tmemPair.1 key
  obtain ⟨-, hreq, hown⟩ := hval r hr
  have hcta := hown.1
  rw [hpre.grid] at hcta
  refine ⟨by rw [← hkey r hr]; omega, ?_⟩
  obtain ⟨hg, hw | hw⟩ := own_shape hpre hW hown <;> obtain ⟨own, grp, act⟩ := r <;>
    simp only at hg hw hreq <;> subst hg hw
  · obtain ⟨col, rfl⟩ := Tmem.Action.request_eq_alloc hreq
    exact .inl ⟨col, rfl⟩
  · rw [Tmem.Action.request_eq_dealloc hreq]
    exact .inr rfl

omit hW in
/-- The first record of a source-ordered history is one with no predecessor. -/
theorem history_head {l : List Requests} {r : Requests} (hr : r ∈ l)
    (hp : l.Pairwise fun a b => a.own.Ordered b.own) (hn : ∀ x ∈ l, ¬ x.own.Ordered r.own) :
    ∃ rest, l = r :: rest := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hr
  cases s with
  | nil => exact ⟨t, rfl⟩
  | cons x s =>
    have hx := (List.pairwise_cons.mp hp).1 r (by simp)
    exact (hn x (by simp) hx).elim

omit hW in
theorem allocReq_participates (S col : Nat) : Participates L (allocReq S col).own (0, 0) :=
  ⟨0, by simp [WarpRequest.event, allocReq]⟩

omit hW in
theorem allocReq_first {S col : Nat} (x : WarpRequest) : ¬ x.Before (allocReq S col).own := by
  intro h
  have := h.2.2 0
  simp [allocReq] at this

include hX in
/-- This kernel performs only cta_group::1 operations, so it pairs nothing. -/
theorem pairing_nil : X.tmemPairing = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  have he := (hX.tmemPair.2.1 q hq).1.2.1.2.2.1 0
  rcases hW.resource he with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> cases h

include hpre hX in
/-- Lane 0's allocation is recorded once lane 0 has passed it. -/
theorem alloc_covered (hm : 1 < m 0) : Covered L X (0, 0) := by
  have hT := threads_eq hpre
  have hget := (talloc_at hW (g := 0) (by decide) (by omega)).1
  have hl := hW.length 0 (by decide)
  exact hX.tmemPairBlocking.covered ⟨Flow.tmemAlloc_0, .one, some (tslot L.sharedBase), .alloc 32,
    hget, trivial⟩ (by simp; omega)

include hpre hX in
/-- Recording warp 0's release requires lane 0 to have passed its allocation. -/
theorem dealloc_rec_covered (hr : deallocReq P ∈ X.tmemHistory 0) : Covered L X (0, 0) := by
  have hT := threads_eq hpre
  obtain ⟨hval, -, -⟩ := hX.tmemPair.1 0
  obtain ⟨-, -, -, -, hev, -⟩ := hval _ hr
  have he := hev 0
  simp [WarpRequest.event, deallocReq] at he
  have hlt := len_of_get he
  have hget : X.get (0, 0) = some (allocE L.sharedBase) := by
    obtain ⟨_, hj, _⟩ := hW.tdealloc he
    exact (talloc_at hW (g := 0) (by decide) (by omega)).1
  exact hX.tmemPairBlocking.covered ⟨Flow.tmemAlloc_0, .one, some (tslot L.sharedBase), .alloc 32,
    hget, trivial⟩ (by simp at hlt ⊢; omega)

include hpre hX in
/-- Before lane 0's allocation is recorded, no request is recorded. -/
theorem history_nil (hn : ¬ Covered L X (0, 0)) (key : Nat) : X.tmemHistory key = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨rfl, ⟨col, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hr
  · exact hn ⟨_, .inl ⟨0, _, hr, rfl, rfl⟩, _, List.mem_singleton_self _,
      allocReq_participates _ _⟩
  · exact hn (dealloc_rec_covered hpre hX hW hr)

include hpre hX in
/-- A recorded allocation leaves room for its 32 columns: the allocator completed it. -/
theorem base_room {col : Nat} (hr : allocReq L.sharedBase col ∈ X.tmemHistory 0) :
    col + 32 ≤ 512 := by
  apply Nat.le_of_not_lt
  intro hc
  have hblk : Tmem.perform {} (.alloc 32 col) = .blocked := by
    simp [Tmem.perform, Tmem.validColumns, Tmem.available]
    omega
  obtain ⟨rest, hh⟩ := history_head hr (hX.object.tmemOrdered hX.tmemPair 0) fun x hx hxo => by
    obtain ⟨-, ⟨c, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hx
    · exact allocReq_first _ (hxo rfl rfl)
    · exact allocReq_first _ (hxo rfl rfl)
  apply (hX.tmemPair.1 0).2.2
  rw [hh]
  simp [runRequests, allocReq, hblk]

include hpre hX in
/-- Once lane 0 stored the address, a recorded allocation's column is the stored one
(OBJ-TMEM-ALLOC-RESULT). -/
theorem alloc_base {col : Nat} (hr : allocReq L.sharedBase col ∈ X.tmemHistory 0) (hm : 1 < m 0) :
    col = (P 0).col := by
  have hB := hpre.block
  have hget := (talloc_at hW (g := 0) (by decide) (by omega)).1
  have h := hX.tmemPairResult (0, 0) Flow.tmemAlloc_0 .one (some (tslot L.sharedBase)) 32 hget 0 _
    col hr
    (by simp [WarpRequest.event, allocReq]) rfl Flow.tmemAlloc_0 _ _ (tslot_at hW hm)
  have h0 := congrArg List.head? h
  simp only [Value.toBytes, Value.bytes, List.head?_map,
    show (List.range 4).head? = some 0 from rfl, Option.map_some, Option.some.injEq,
    Value.byteAt, Prod.mk.injEq, Value.bits.injEq, true_and, and_true] at h0
  have hc := base_room hpre hX hW hr
  have hp := hW.col 0
  have := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

include hpre hX in
/-- Lane 0's allocation is covered only by warp 0's recorded allocation request. -/
theorem covered0_alloc (hc : Covered L X (0, 0)) :
    ∃ col, allocReq L.sharedBase col ∈ X.tmemHistory 0 := by
  obtain ⟨ws, ⟨key, r, hr, -, rfl⟩ | ⟨q, hq, -⟩, w, hw, hp⟩ := hc
  · rw [List.mem_singleton.mp hw] at hp
    obtain ⟨rfl, ⟨col, rfl⟩ | rfl⟩ := rec_shape hpre hX hW hr
    · exact ⟨col, hr⟩
    · obtain ⟨lane, he⟩ := hp
      simp [WarpRequest.event, deallocReq] at he
  · rw [pairing_nil hX hW] at hq
    cases hq

include hpre hX in
/-- Lane 0's passing its allocation means warp 0's allocation is recorded, at the column lane 0
stored. -/
theorem alloc_recorded (hm : 1 < m 0) : allocReq L.sharedBase (P 0).col ∈ X.tmemHistory 0 := by
  obtain ⟨col, hr⟩ := covered0_alloc hpre hX hW (alloc_covered hpre hX hW hm)
  rw [← alloc_base hpre hX hW hr hm]
  exact hr

omit hW in
theorem not_before_alloc (x : WarpRequest) {S col : Nat} : ¬ x.Before (allocReq S col).own :=
  allocReq_first x

omit hW in
theorem dealloc_not_before {S col : Nat} {P : Nat → Par} :
    ¬ (deallocReq P).own.Before (allocReq S col).own :=
  allocReq_first _

omit hW in
theorem dealloc_irrefl {P : Nat → Par} : ¬ (deallocReq P).own.Before (deallocReq P).own :=
  WarpRequest.Before.irrefl _

include hpre hX in
/-- This kernel's history: nothing, its allocation, or its allocation then release. -/
theorem history_shape : X.tmemHistory 0 = [] ∨
    (∃ col, X.tmemHistory 0 = [allocReq L.sharedBase col]) ∨
    ∃ col, X.tmemHistory 0 = [allocReq L.sharedBase col, deallocReq P] := by
  have hord := (hX.object.tmemOrdered hX.tmemPair 0)
  have hmem : ∀ x ∈ X.tmemHistory 0, (∃ col, x = allocReq L.sharedBase col) ∨ x = deallocReq P :=
    fun x hx => (rec_shape hpre hX hW hx).2
  have hda : deallocReq P ∈ X.tmemHistory 0 →
      ∃ col, allocReq L.sharedBase col ∈ X.tmemHistory 0 := fun hd =>
    covered0_alloc hpre hX hW (dealloc_rec_covered hpre hX hW hd)
  generalize hl : X.tmemHistory 0 = l at hord hmem hda
  rcases l with _ | ⟨x, rest⟩
  · exact .inl rfl
  · right
    obtain ⟨hx, hrest⟩ := List.pairwise_cons.mp hord
    obtain ⟨col, rfl⟩ : ∃ col, x = allocReq L.sharedBase col := by
      rcases hmem x (by simp) with h | rfl
      · exact h
      · exfalso
        obtain ⟨c, ha⟩ := hda (by simp)
        rcases List.mem_cons.mp ha with h | h
        · simp [allocReq, deallocReq] at h
        · exact dealloc_not_before ((hx _ h) rfl rfl)
    rcases rest with _ | ⟨y, rest⟩
    · exact .inl ⟨col, rfl⟩
    · have hy : y = deallocReq P := by
        rcases hmem y (by simp) with ⟨c, rfl⟩ | h
        · exact (allocReq_first _ ((hx _ List.mem_cons_self) rfl rfl)).elim
        · exact h
      subst hy
      cases rest with
      | nil => exact .inr ⟨col, rfl⟩
      | cons z rest =>
        exfalso
        have hz := (List.pairwise_cons.mp hrest).1 z (by simp)
        rcases hmem z (by simp) with ⟨c, rfl⟩ | rfl
        · exact allocReq_first _ (hz rfl rfl)
        · exact dealloc_irrefl (hz rfl rfl)

include hpre hX in
/-- The history records at most one allocation. -/
theorem alloc_unique {c c' : Nat} (h : allocReq L.sharedBase c ∈ X.tmemHistory 0)
    (h' : allocReq L.sharedBase c' ∈ X.tmemHistory 0) : c = c' := by
  rcases history_shape hpre hX hW with hh | ⟨col, hh⟩ | ⟨col, hh⟩ <;> rw [hh] at h h' <;>
    simp [allocReq, deallocReq] at h h' <;> omega

include hpre hX in
/-- The allocated column leaves room for the 32 columns. -/
theorem col_ok (hm : 1 < m 0) : (P 0).col + 32 ≤ 512 := by
  have := base_room hpre hX hW (alloc_recorded hpre hX hW hm)
  exact this

end
end
end PTX.Kernels.TcGemm.Proof
