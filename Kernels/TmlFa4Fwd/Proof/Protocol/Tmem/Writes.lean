-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.OOrder

@[expose] public section

/-! # No two Tensor Memory writes of one cell are unordered

* **Two MMAs** (`mm_order`): one lane of the CTA's warp 12 issues them, with the accumulator of the
  cell's region: in program order, pipelined.
* **An MMA and a store** (`ms_order`): a QK MMA of tile `u` and a P store of tile `u'`, a PV MMA of
  tile `u` and a rescale store of credit `q`, by `TcOrders`.
* **Two stores** (`ss_order`): a cell's stores are one lane's, in program order. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- The protocols' Tensor Memory orders between MMAs and stores. -/
structure TcOrders (L : Launch) (X : Execution) : Prop where
  /-- An MMA before the commit of score tile `u` is done before every event of a softmax thread
  of the stage after its poll of tile `u` (`Score.s_doneBefore`). -/
  s_done : ∀ {h f : Nat} {i : EvId}, h < L.threads → Prologue.warpIndex L h < 8 → IsMma X i →
    i.1 / L.block = h / L.block →
    sCommits L X i.1 (Prologue.warpIndex L h / 4) i.2 + 1 ≤ sPolls L X h (Prologue.warpIndex L h /
        4) f →
    f < (X.tr h).length → DoneBefore L X i (h, f)
  /-- A softmax store of tile `u` is done before every MMA of its pair after the polls of phase
  `u` of the objects its columns are published through (`Score.store_done`). -/
  p_done : ∀ {h i a : Nat} {vals : List Value} {f : EvId}, h < L.threads → Prologue.warpIndex L h <
      8 →
    X.TSt (h, i) a vals .s32x32b → IsMma X f → f.1 / L.block = h / L.block →
    sPolls L X h (Prologue.warpIndex L h / 4) i ≤ pPolls L X f.1 (Prologue.warpIndex L h / 4) f.2 →
    ((∀ j < vals.length, InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) →
      sPolls L X h (Prologue.warpIndex L h / 4) i ≤ p2Polls L X f.1 (Prologue.warpIndex L h / 4)
          f.2) →
    StoreDoneBefore L X (h, i) f
  /-- A correction store of credit `q` is done before every MMA of its pair after the poll of
  phase `q` (`OAcc.store_done`). -/
  o_store_done : ∀ {h k a j st : Nat} {vals : List Value} {f : EvId}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → st < 2 → X.TSt (h, k) a vals
        .s32x32b → j < vals.length →
    InO st (tcDataCell32 L h a j) → IsMma X f → f.1 / L.block = h / L.block →
    pArr L X h st k + 1 ≤ pPolls L X f.1 st f.2 → StoreDoneBefore L X (h, k) f
  /-- A PV MMA of a tile before credit `q` is done before a correction store of credit `q`
  (`OAcc.done_store`). -/
  o_done_store : ∀ {h k a j st : Nat} {vals : List Value} {x : EvId}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → X.TSt (h, k) a vals .s32x32b → j <
        vals.length →
    InO st (tcDataCell32 L h a j) → IsMma X x → (∃ cell, X.MmaCell x cell ∧ InO st cell) →
    x.1 / L.block = h / L.block → pPolls L X x.1 st x.2 ≤ pArr L X h st k →
    DoneBefore L X x (h, k)

/-- The region of an MMA's result cell: one stage's scores or accumulator, of its pair. -/
theorem mma_region (ht : ScoreFacts L X) {x : EvId} {cell : Cell} (hc : X.MmaCell x cell) :
    IsMma X x ∧ x.1 < L.threads ∧ cell.cta = x.1 / L.block ∧
      ∃ st < 2, InS st cell ∨ InO st cell := by
  obtain ⟨d, s, acc, mask, row, col, hi, -⟩ := id hc
  obtain ⟨hg, -, st, hst, h | h⟩ := ht.mma_cells hi
  · obtain ⟨h1, h2⟩ := h cell hc
    exact ⟨⟨_, _, _, _, hi⟩, hg, h2, st, hst, .inl h1⟩
  · obtain ⟨h1, h2⟩ := h cell hc
    exact ⟨⟨_, _, _, _, hi⟩, hg, h2, st, hst, .inr h1⟩

/-- **Two MMAs writing one cell are one, or pipelined in program order.** -/
theorem mm_order (ht : ScoreFacts L X) {x y : EvId} {cell : Cell} (hx : X.MmaCell x cell)
    (hy : X.MmaCell y cell) : x = y ∨ Before L X x y ∨ Before L X y x := by
  obtain ⟨dx, sx, ax, mx, -, -, hxi, -⟩ := id hx
  obtain ⟨dy, sy, ay, my, -, -, hyi, -⟩ := id hy
  obtain ⟨-, hgx, hlx, st, hst, hr⟩ := mma_region ht hx
  obtain ⟨-, hgy, hly, -⟩ := mma_region ht hy
  have hthr : x.1 = y.1 := ht.tc_one ⟨_, _, _, _, hxi⟩ (.inl ⟨_, _, _, _, hyi⟩)
    (by rw [← hlx, ← hly])
  have hreg : (InS st cell ∧ InS st cell) ∨ (InO st cell ∧ InO st cell) :=
    hr.imp (fun h => ⟨h, h⟩) (fun h => ⟨h, h⟩)
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact .inr (.inl (Before.of_mma_po hxi hyi hgx hthr hlt (ht.mma_acc hxi hyi hx hy rfl hst
      hreg)))
  · exact .inl (Prod.ext hthr heq)
  · exact .inr (.inr (Before.of_mma_po hyi hxi hgy hthr.symm hgt
      (ht.mma_acc hyi hxi hy hx rfl hst hreg)))

/-- **An MMA and a store writing one cell are ordered.** -/
theorem ms_order (ht : ScoreFacts L X) (ho : OAccFacts L X) (hT : TcOrders L X) {x y : EvId}
    {cell : Cell} (hx : X.MmaCell x cell) (hy : StoreCell L X y cell) :
    Before L X x y ∨ StoreDoneBefore L X y x := by
  obtain ⟨hxm, -, hlx, -⟩ := mma_region ht hx
  obtain ⟨a, vals, j, hs, hj, rfl⟩ := ht.storeCell hy
  obtain ⟨g, k⟩ := y
  dsimp only at hs hj hlx hx ⊢
  obtain ⟨hh, h12⟩ := ht.tc_role (.inr hs)
  have hc : x.1 / L.block = g / L.block := hlx.symm
  by_cases h8 : Prologue.warpIndex L g < 8
  · have hP' := (ht.soft_st hh h8 hs).1 j hj
    have hS' : InS (Prologue.warpIndex L g / 4) (tcDataCell32 L g a j) := by
      unfold InP at hP'
      unfold InS
      omega
    by_cases hu : sCommits L X x.1 (Prologue.warpIndex L g / 4) x.2 + 1 ≤ sPolls L X g
        (Prologue.warpIndex L g / 4) k
    · obtain ⟨pc, hsg⟩ := id hs
      exact .inl (.inl (hT.s_done hh h8 hxm hc hu
        (len_of_get hsg)))
    · have hq := ht.qk_polls (by omega) hxm hx hS'
      exact .inr (hT.p_done hh h8 hs hxm hc (by omega) (fun _ => by omega))
  · obtain ⟨st, hst, hO', -⟩ := ho.corr_st hh (by omega) h12 hs
    have hO := hO' j hj
    by_cases hu : pPolls L X x.1 st x.2 ≤ pArr L X g st k
    · exact .inl (.inl (hT.o_done_store hh (by omega) h12 hs hj hO hxm ⟨_, hx, hO⟩ hc hu))
    · exact .inr (hT.o_store_done hh (by omega) h12 hst hs hj hO hxm hc (by omega))

/-- Two lanes of warps below 12 in one warp group (softmax stage or correction) with one cell are
one lane. -/
theorem cell_thread (hpre : Pre P L mem0) {h h' a a' j j' : Nat}
    (hst : Prologue.warpIndex L h / 4 = Prologue.warpIndex L h' / 4)
    (hc : tcDataCell32 L h a j = tcDataCell32 L h' a' j') : h = h' :=
  soft_cell_thread hpre hst hc

/-- **Two stores writing one cell are one, or ordered by the store pipeline.** -/
theorem ss_order (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X) {x y : EvId}
    {cell : Cell} (hx : StoreCell L X x cell) (hy : StoreCell L X y cell) :
    x = y ∨ StoreDoneBefore L X x y ∨ StoreDoneBefore L X y x := by
  obtain ⟨a, vals, j, hs, hj, rfl⟩ := ht.storeCell hx
  obtain ⟨a', vals', j', hs', hj', hceq⟩ := ht.storeCell hy
  obtain ⟨g, k⟩ := x
  obtain ⟨g', k'⟩ := y
  dsimp only at hs hj hs' hj' hceq ⊢
  obtain ⟨hh, h12⟩ := ht.tc_role (.inr hs)
  obtain ⟨hh', h12'⟩ := ht.tc_role (.inr hs')
  have hthr : g = g' := by
    refine cell_thread hpre ?_ hceq
    by_cases h8 : Prologue.warpIndex L g < 8 <;> by_cases h8' : Prologue.warpIndex L g' < 8
    · have h1 := (ht.soft_st hh h8 hs).1 j hj
      have h2 := (ht.soft_st hh' h8' hs').1 j' hj'
      rw [← hceq] at h2
      unfold InP at h1 h2
      omega
    · have h1 := (ht.soft_st hh h8 hs).1 j hj
      obtain ⟨st, -, hO, -⟩ := ho.corr_st hh' (by omega) h12' hs'
      have h2 := hO j' hj'
      rw [← hceq] at h2
      unfold InP at h1
      unfold InO at h2
      omega
    · obtain ⟨st, -, hO, -⟩ := ho.corr_st hh (by omega) h12 hs
      have h1 := hO j hj
      have h2 := (ht.soft_st hh' h8' hs').1 j' hj'
      rw [← hceq] at h2
      unfold InP at h2
      unfold InO at h1
      omega
    · omega
  subst hthr
  rcases Nat.lt_trichotomy k k' with hlt | rfl | hgt
  · exact .inr (.inl (StoreDoneBefore.of_po hs hs' hh rfl hlt))
  · exact .inl rfl
  · exact .inr (.inr (StoreDoneBefore.of_po hs' hs hh rfl hgt))

/-- **No two Tensor Memory writes of one cell are unordered.** -/
theorem no_writes_unsafe (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hT : TcOrders L X) : ¬ WritesUnsafe L X := by
  refine fun hn => hn fun x y cell hx hy => ?_
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hx with hxm | hxs <;>
    rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hy with hym | hys
  · rcases mm_order ht hxm hym with h | h | h
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr (.inl h))
  · rcases ms_order ht ho hT hxm hys with h | h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
  · rcases ms_order ht ho hT hym hxs with h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl (.inr (.inl h)))
  · rcases ss_order hpre ht ho hxs hys with h | h | h
    · exact .inl h
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inl h)))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
