-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Lemmas.Flow.CountTake

@[expose] public section

/-! # A dequant lane's arrival on `dequantReady` follows its 32 chunk stores

A lane's block is `wraw`, `wsv`, the four rows (a scale load, then per row the eight raw loads and
the eight chunk stores, interleaved), the proxy fence `fpx`, the arrival `arrD` on `dequantReady`
and the arrival `arrF` on `rawFree`. The number of stores a site has passed in its block is
`doneN`; a state with `n` stores passed follows the stores `0 .. n - 1` of the block, in the
order `8 r + s`, in the lane's trace (`chunk_walk`, the walk of `deq_pred` backwards as in
`Dequant/Export/QPoll.lean`), and no arrival on any object lies between them and the state.
So (`dequant_chunks`) an arrival on `dequantReady s` is preceded by the lane's chunk store `(r, q)`
into `dequant s`, with no arrival on `dequantReady s` between: the store's count of arrivals before
it is the arrival's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The chunk stores a site has passed in its block. -/
private def doneN : Dequant.Site → Nat
  | .scale r => 8 * r.val
  | .raw r s => 8 * r.val + (s.val - 1)
  | .store r s => 8 * r.val + s.val
  | .fpx => 32
  | .arrD => 32
  | _ => 0

/-- A site is a store site (1) or not (0). -/
private def isSt : Dequant.Site → Nat
  | .store _ _ => 1
  | _ => 0

private theorem rawNext_done :
    ∀ (r : Fin 4) (s : Fin 8), doneN (Dequant.Control.rawNext r s) = doneN (.raw r s) := by
  decide

private theorem storeNext_done :
    ∀ (r : Fin 4) (s : Fin 8), doneN (Dequant.Control.storeNext r s) = doneN (.store r s) + 1 := by
  decide

/-- The stores passed after a step, the slot kept, and the step not an arrival of the block. -/
private theorem succ_done {d' d : Dequant.Control.D} {f : Event}
    (h : Dequant.Control.succ P L g d' f = some (some d)) (hpos : 0 < doneN d.site) :
    d'.site ≠ .arrD ∧ d'.site ≠ .arrF ∧ d.sb = d'.sb ∧
      doneN d.site = doneN d'.site + isSt d'.site := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d'
  cases site
  case arrD =>
    simp only [Dequant.Control.succ, Option.some.injEq] at h
    subst h
    simp [doneN] at hpos
  all_goals
    simp only [Dequant.Control.succ, Dequant.Control.poll, Dequant.Control.dataRd,
      Dequant.Control.afterSmr, Dequant.Control.afterA, Dequant.Control.loopEntry,
      Dequant.Control.advance, Dequant.Control.scaleNext, Code.ncNext] at h
    repeat' split at h
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst h
    all_goals
      try simp only [rawNext_done, storeNext_done] at hpos ⊢
      simp [doneN, isSt] at hpos ⊢

/-- Outside the arrivals' sites, an event is in no arrival class. -/
private theorem no_arrive {d : Dequant.Control.D} {f : Event} (hk : Dequant.EvK L g d f)
    (h1 : d.site ≠ .arrD) (h2 : d.site ≠ .arrF) (l : Loc) :
    Dequant.cls (.arrive l) f = false := by
  obtain ⟨pc, kd⟩ := f
  have hna : ∀ m tx n rel sc, kd ≠ .arrive m tx n rel sc := by
    intro m tx n rel sc hkd
    subst hkd
    obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
    cases site <;>
      simp_all [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv]
  cases kd with
  | arrive m tx n rel sc => exact absurd rfl (hna m tx n rel sc)
  | wait m par ok acq sc => cases ok <;> simp [Dequant.cls, Dequant.kindOf]
  | _ => simp [Dequant.cls, Dequant.kindOf]

/-- The chunk store at a store site: a 16-byte write of the chunk in the slot's tile. -/
private theorem store_ev (hp : Pre P L m) {r : Fin 4} {s : Fin 8} {d : Dequant.Control.D}
    {f : Event} (hs : d.site = .store r s) (hk : Dequant.EvK L g d f)
    (hub : ∀ fl, f.kind ≠ .ub fl) :
    ∃ ac bs, f.kind = .wr ac bs ∧ MemRow.WsAcc L (g / L.block)
      ((Region.dequant (Dequant.slotF d.sb)).lo + MemRow.dqChunk (g % 128) r s) 16 ac := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  simp only at hs
  subst hs
  simp only [Dequant.EvK, Dequant.StoreEv] at hk
  rcases hk with ⟨a, bs, hk, hl, hz⟩ | ⟨fl, hk⟩
  · rw [PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.store_loc hp] at hl
    exact ⟨a, bs, hk, hl, hz⟩
  · exact (hub fl hk).elim

/-- **The walk**: a state at index `i ≤ k` of a lane with an event at `k`, with `n` stores passed
in its block, follows the block's stores `(r, q)`, `8 r + q < n`, in the slot's tile, with no
arrival between them and the state. -/
private theorem chunk_walk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ∀ i, i ≤ k → ∀ (d : Dequant.Control.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d⟩, n)) →
      ∀ (r : Fin 4) (q : Fin 8), 8 * r.val + q.val < doneN d.site →
      ∃ j < i, ∃ pcw ac bs, X.get (g, j) = some ⟨pcw, .wr ac bs⟩ ∧
        2606 ≤ pcw ∧ pcw < 3611 ∧ MemRow.WsAcc L (g / L.block)
          ((Region.dequant (Dequant.slotF d.sb)).lo + MemRow.dqChunk (g % 128) r q) 16 ac ∧
        ∀ l, ((X.tr g).take j).countP (Dequant.cls (.arrive l)) =
          ((X.tr g).take i).countP (Dequant.cls (.arrive l)) := by
  intro i
  induction i with
  | zero =>
    intro _ d n hs
    obtain ⟨i', hi'⟩ := deq_pred_index hs
    omega
  | succ i ih =>
    intro hik d n hs r q hlt
    have hpos : 0 < doneN d.site := by omega
    obtain ⟨f, hf, hub⟩ := deq_earlier_ev hX he (by omega : i < k)
    have hsite : d.site ≠ .smr := by
      intro h
      rw [h] at hpos
      simp [doneN] at hpos
    obtain ⟨d', n', hs', hsucc⟩ := deq_pred hFw hg hf hs hsite
    obtain ⟨hD, hF, hsb, hdone⟩ := succ_done hsucc hpos
    obtain ⟨hpc, hk⟩ := deq_ev hp hX hFw hf hub hs'
    have hcnt : ∀ l, ((X.tr g).take (i + 1)).countP (Dequant.cls (.arrive l)) =
        ((X.tr g).take i).countP (Dequant.cls (.arrive l)) :=
      fun l => countP_take_succ_false hf (no_arrive hk hD hF l)
    by_cases hold : 8 * r.val + q.val < doneN d'.site
    · obtain ⟨j, hj, pcw, ac, bs, hget, h1, h2, hw, hc⟩ := ih (by omega) d' n' hs' r q hold
      exact ⟨j, by omega, pcw, ac, bs, hget, h1, h2, by rw [hsb]; exact hw,
        fun l => (hc l).trans (hcnt l).symm⟩
    · obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d'
      simp only at hold hdone hsb hk hpc hD hF
      generalize doneN d.site = N at hpos hlt hdone
      cases site <;> simp only [isSt, doneN] at hdone hold <;> try omega
      rename_i r' s'
      have hr : r = r' := Fin.ext (by have := r'.isLt; have := q.isLt; have := s'.isLt; omega)
      have hq : q = s' := Fin.ext (by have := r'.isLt; have := q.isLt; have := s'.isLt; omega)
      subst hr hq
      obtain ⟨a, bs, hkind, hw⟩ := store_ev hp (g := g) rfl hk hub
      obtain ⟨pcf, kf⟩ := f
      simp only at hkind hpc
      subst hkind
      refine ⟨i, by omega, pcf, a, bs, hf, ?_, ?_, by rw [hsb]; exact hw, fun l => (hcnt l).symm⟩
      · rw [hpc]
        simp only [Dequant.Site.pc, Dequant.rowBase]
        split_ifs <;> omega
      · rw [hpc]
        have := r.isLt
        have := q.isLt
        simp only [Dequant.Site.pc, Dequant.rowBase]
        split_ifs <;> omega

/-- **A dequant lane's arrival on `dequantReady s` follows each of its 32 chunk stores**: the
store `(r, q)` of the block into the tile `dequant s` of the lane's CTA, with the arrivals on
`dequantReady s` before the store as many as before the arrival. -/
theorem dequant_chunks (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {ia pc c : Nat} {s : Fin 2} {sc : MbarScope}
    (hw : 8 ≤ warp L g ∧ warp L g < 12)
    (he : X.get (g, ia) = some ⟨pc, .arrive (mbarLoc L c (.dequantReady s)) 0 1 true sc⟩)
    (r : Fin 4) (q : Fin 8) :
    ∃ j < ia, ∃ pcw ac bs, X.get (g, j) = some ⟨pcw, .wr ac bs⟩ ∧ DequantAt L g pcw ∧
      MemRow.WsAcc L (g / L.block) ((Region.dequant s).lo + MemRow.dqChunk (g % 128) r q) 16 ac ∧
      arrivals (mbarLoc L c (.dequantReady s)) ((X.tr g).take j) =
        arrivals (mbarLoc L c (.dequantReady s)) ((X.tr g).take ia) := by
  have hg := Frame.lt_of_get hX he
  have hin := wg2_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩)))
  simp only [Dequant.inRole, decide_eq_true_eq] at hin
  have hub : ∀ fl, Kind.arrive (mbarLoc L c (.dequantReady s)) 0 1 true sc ≠ .ub fl :=
    fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc
    ⟨hin.1, Nat.lt_succ_of_le hin.2⟩
  obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
  cases site
  case arrD =>
    simp only [Dequant.EvK, Kind.arrive.injEq] at hk
    have h1 := hk.1.trans (Dequant.ready_loc hp sb)
    simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h1
    have hs := MbarFam.dequantReady.inj (MbarFam.off_inj h1.2)
    obtain ⟨j, hj, pcw, a, bs, hget, hl, hh, hw', hc⟩ :=
      chunk_walk hp hX hFw hg he ia le_rfl _ _ hσ r q (by simp [doneN]; omega)
    refine ⟨j, hj, pcw, a, bs, hget, ⟨hw.1, hw.2, hl, hh⟩, ?_, ?_⟩
    · simp only at hw'
      rw [hs]
      exact hw'
    · rw [wg2_arrivals hp hX hFw hw, wg2_arrivals hp hX hFw hw]
      exact hc _
  case arrF =>
    exfalso
    simp only [Dequant.EvK, Kind.arrive.injEq] at hk
    have h1 := hk.1.trans (Dequant.free_loc hp sb)
    simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff] at h1
    cases MbarFam.off_inj h1.2.2
  all_goals
    exfalso
    simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv] at hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
