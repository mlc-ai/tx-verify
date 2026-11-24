-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.MbarReach
public import Kernels.InklingRelDecode.Proof.Protocol.SrCells

@[expose] public section

/-!
# The orders between the MMA lane and a softmax `tcgen05.st`

The handshakes of `SOHandoff` and `SOOdone`, applied to a `tcgen05.st` of the softmax region and
an MMA of the CTA's MMA lane `cm`. A store's **gate** (`StGate`) is its place in its iteration:

* a successful acquire poll `j` of a barrier `m` by the storing thread `t` before the store, with
  `u` earlier successful polls of `m` (`m = s_ready b` for the `P` store, with `u` the use of the
  buffer; `m = o_done` for the rescale store of iteration `i`, with `u = i - 1`);
* once thread 0 has arrived on `p_ready b` more than `q` times, the store's `tcgen05.wait::st`
  after it, which is base-causally before an event `e` of thread 0 of the default partition
  (the `bar.sync 0, 128` that every softmax thread passes between its wait and thread 0's
  arrival: **a premise of the named barrier**, see `BarChain` below) with at most `q` earlier
  arrivals on `p_ready b`.

From a gate and `Mbar.Ctx` (the reuse paths, the record sources):

* `mma_before_s_store`: an MMA of the lane with at most `u` commits to `s_ready b` before it is
  done before the store (`SOHandoff.s_doneBefore`);
* `mma_before_o_store`: the same for `o_done` (`SO.o_doneBefore`);
* `store_before_mma`: the store is `StoreDoneBefore` every event of the lane that follows more
  than `q` successful polls of `p_ready b` (`SOHandoff.p_store_before_read`).

`BarChain` derives a `tcgen05` event's causality to another thread's later event from the named
barrier: a pair of `bar.sync 0, 128` events of one barrier-0 ordinal, of the first thread after the
event and of the second thread before the later event, with `Bar128Causal`, the base-causality
form of `Mbar.Bar128Witness` (what the named-barrier generation proof of barrier 0 owes).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {c cm p0 : Nat} {Soft Mma : Nat → Prop}

/-- **The gate of a softmax `tcgen05.st`.** Thread `t` of the softmax threads polls `m` with `u`
earlier successful polls (an acquire poll at CTA scope) before the store at `sk`, and its
`tcgen05.wait::st` after the store is base-causally before an event `e` of thread 0 with at most
`q` earlier arrivals on `p_ready b`. -/
structure StGate (L : Launch) (X : Execution) (c p0 : Nat) (Soft : Nat → Prop) (t sk : Nat)
    (m : Loc) (u b q : Nat) : Prop where
  soft : Soft t
  poll : ∃ j pc p sc, j < sk ∧ X.get (t, j) = some ⟨pc, .wait m p true true sc⟩ ∧
    okPolls m ((X.tr t).take j) = u
  /-- Once thread 0 has made more than `q` arrivals on `p_ready b`, the store's `wait::st` exists
  and is base-causally before an event of thread 0 with at most `q` earlier arrivals. The guard
  makes the clause true on a prefix that stops between the store and thread 0's arrival
  (the development notes, "Kk"). -/
  rendezvous : q + 1 ≤ arrivals (pReady L c b) (X.tr p0) →
    ∃ wk pcw e, sk < wk ∧ X.get (t, wk) = some ⟨pcw, .tc .waitSt⟩ ∧
      baseCausality L X (t, wk) (p0, e) ∧ arrivals (pReady L c b) ((X.tr p0).take e) ≤ q

variable (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma)
include H

/-- A softmax thread is a launched thread of the default partition of CTA `c`. -/
theorem soft_info {t : Nat} (ht : Soft t) : t < L.threads ∧ t / L.block = c ∧ t % L.block < 128 :=
  H.route.soft_thread ht

/-- **An MMA of the lane before the `P` store.** An MMA `x` of the lane, `x.1 / block = c`, with at
most `u` commits to `s_ready b` before it, is done before the `P` store whose gate polled
`s_ready b` with `u` earlier polls. -/
theorem mma_before_s_store {t sk b u q : Nat} {x : EvId} {a : Nat} {vals : List Value}
    {sh : TcShape} (hb : b < 2) (hcm : cm < L.threads) (hcmc : cm / L.block = c)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hg : StGate L X c p0 Soft t sk (sReady L c b) u b q) (hst : X.TSt (t, sk) a vals sh)
    (hx : IsMma X x) (hxc : x.1 / L.block = c)
    (hu : ((X.tr cm).take x.2).countP (commitsTo (sReady L c b)) ≤ u) :
    DoneBefore L X x (t, sk) := by
  obtain ⟨ht, htc, -⟩ := soft_info H hg.soft
  obtain ⟨j, pc, p, sc, hj, hw, hq⟩ := hg.poll
  obtain ⟨pcs, hs⟩ := hst
  exact SO.s_doneBefore H.cons H.facts hone hb ⟨hcm, ht, by rw [hcmc, htc]⟩
    (Mbar.sReach H hb hg.soft) hw hq hx hxc hu hj (len_of_get hs)

/-- **An MMA of the lane before the rescale store.** An MMA `x` of the lane with at most `u`
commits to `o_done` before it is done before the rescale store whose gate polled `o_done` with
`u` earlier polls. -/
theorem mma_before_o_store {t sk b u q : Nat} {x : EvId} {a : Nat} {vals : List Value}
    {sh : TcShape} (hcm : cm < L.threads) (hcmc : cm / L.block = c)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hg : StGate L X c p0 Soft t sk (oDone L c) u b q) (hst : X.TSt (t, sk) a vals sh)
    (hx : IsMma X x) (hxc : x.1 / L.block = c)
    (hu : ((X.tr cm).take x.2).countP (commitsTo (oDone L c)) ≤ u) :
    DoneBefore L X x (t, sk) := by
  obtain ⟨ht, htc, -⟩ := soft_info H hg.soft
  obtain ⟨j, pc, p, sc, hj, hw, hq⟩ := hg.poll
  obtain ⟨pcs, hs⟩ := hst
  exact SO.o_doneBefore H.cons H.facts H.opar hone ⟨hcm, ht, by rw [hcmc, htc]⟩
    (Mbar.oReach H hg.soft) hw hq hx hxc hu hj (len_of_get hs)

/-- **The store before an MMA-lane event.** A `tcgen05.st` with a gate for `p_ready b` and `q` is
`StoreDoneBefore` the event `f` of the lane that follows more than `q` successful polls of
`p_ready b`. `hpAcq`: the lane's polls of `p_ready` are acquire polls (their event shape). -/
theorem store_before_mma {t sk b u q f : Nat} {m : Loc} {a : Nat} {vals : List Value}
    {sh : TcShape} (hb : b < 2) (hcm : cm < L.threads) (hcmc : cm / L.block = c)
    (hpAcq : ∀ {j pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (cm, j) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩ → acq = true)
    (hg : StGate L X c p0 Soft t sk m u b q) (hst : X.TSt (t, sk) a vals sh)
    (hf : q + 1 ≤ okPolls (pReady L c b) ((X.tr cm).take f)) (hfl : f < (X.tr cm).length) :
    StoreDoneBefore L X (t, sk) (cm, f) := by
  have hp0 := soft_info H H.route.p0_soft
  have hU := SO.p_handoff H.cons H.facts hb (cons := fun h => h = cm)
    (fun h hh => by subst hh; exact Mbar.pReach H hb H.route.cm_mma)
    (fun hh hw' => by subst hh; exact hpAcq hw')
    (fun h hh => by subst hh; exact ⟨hp0.1, hcm, by rw [hp0.2.1, hcmc]⟩)
  have harr : q + 1 ≤ arrivals (pReady L c b) (X.tr p0) := by
    obtain ⟨j, pcj, p, acq, sc, -, hwj, hq⟩ := MbarRing.UnitHandoff.exists_poll hf
    obtain ⟨i, hi, hs⟩ := hU cm j pcj p acq sc q rfl hwj (by simpa using hq) p0 ⟨0, rfl⟩
    obtain ⟨ev, hev, ha⟩ := hs.arrives
    have h1 : arrivals (pReady L c b) ((X.tr p0).take (i + 1)) = q + 1 := by
      have hg : (X.tr p0)[i]? = some ev := hev
      simp only [arrivals] at hi ⊢
      rw [List.take_add_one, hg, Option.toList_some, List.countP_append, hi]
      simp [ha]
    have h2 := (List.take_sublist (i + 1) (X.tr p0)).countP_le (p := arrivesOn (pReady L c b))
    simp only [arrivals] at h1 ⊢
    omega
  obtain ⟨wk, pcw, e, hsk, hw, hbar, he⟩ := hg.rendezvous harr
  exact SO.p_store_before_read hU hst hw hsk hbar he rfl hf hfl

/-- **An MMA of the lane before every event after a softmax thread's poll of `s_ready`**, for the
events `e` the poll is base-causally before (`SOHandoff.s_doneBefore` with the target left free,
as `f_doneBefore_at` is for `o_final`): every MMA with at most `u` commits to `s_ready b` before
it, where the poll has `u` earlier successful polls. -/
theorem s_doneBefore_to {b h j pc p u : Nat} {sc : MbarScope} {x e : EvId} (hb : b < 2)
    (hcta : SameCta L cm h)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hR : MbarRing.Notify.Reach L K A X (sReady L c b) cm (sReady L c b) 0 h)
    (he : X.get (h, j) = some ⟨pc, .wait (sReady L c b) p true true sc⟩)
    (hq : okPolls (sReady L c b) ((X.tr h).take j) = u) (hx : IsMma X x)
    (hxc : x.1 / L.block = c)
    (hu : ((X.tr cm).take x.2).countP (commitsTo (sReady L c b)) ≤ u)
    (hbc : baseCausality L X (h, j) e) : DoneBefore L X x e := by
  obtain ⟨i, pcx, sp, rank, hget, hmbar, htgt, hcnt, hrank, hobs⟩ :=
    SO.s_observes H.cons H.facts hb hR he hq
  have hthr : x.1 = cm := hone hx hxc
  have hlt : x.2 < i := by
    obtain ⟨_, _, _, _, _, hxp⟩ := hx.get
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := countP_take_succ (p := commitsTo (sReady L c b)) hget
        (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (sReady L c b)) (X.tr cm)
        (show i + 1 ≤ x.2 by omega)
      omega
    · have hxi : (cm, i) = x := Prod.ext hthr.symm heq
      rw [← hxi] at hxp
      rw [hxp] at hget
      cases hget
  refine .inl ⟨(h, j), sc, ⟨.async (cm, i) (.tcNotify rank), sReady L c b,
    ⟨(cm, i), sp, rank, rfl, ⟨hthr.symm ▸ rfl, hlt, .inl hx, sp, pcx, hget⟩, ⟨pcx, hget⟩, htgt,
      hrank⟩, hobs⟩, ?_, hbc⟩
  rw [hthr]
  exact MbarRing.Unit.Gate.scopesMeet hcta _ _

end
end PTX.Kernels.InklingRelDecode.Proof.Sr
