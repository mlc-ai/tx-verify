-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOHyp
public import Lemmas.Protocol.UnitGate
public import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-!
# The handoffs of the S/P/O handshake

From the objects of `SOHyp` and the reuse premises (the dependency paths that make each barrier's
next phase wait for the consumers' polls of the previous one; **named premises, not proved here**,
see the design note in `SO.lean`):

* **SFull** (`s_observes`): a thread's poll of `s_ready b` with `u` earlier successful polls
  observes the notification of `cm`'s commit with `u` earlier commits to it. With the MMA warp's
  counts (`SOMmaExec.mma_qkcommit_exec`) that commit is the QK commit of block `2 u + b`.
* **S-write before S-read** (`s_doneBefore`): every MMA `cm` issued before that commit (the QK
  MMAs of block `2 u + b`, and all earlier ones) is done before every event of the polling thread
  after its poll (`DoneBefore`): in particular before its `tcgen05.ld` of the S tile.
* **PReady** (`p_handoff`, `p_before_pv`): an MMA lane's poll of `p_ready b` with `q` earlier
  successful polls synchronizes with thread 0's arrival with `q` earlier arrivals; what thread 0
  did up to that arrival happens before the lane's events after the poll (`UnitHandoff`).
  With the named-barrier premise that every thread's `tcgen05.wait::st` after its P store comes
  before thread 0's arrival, **P-write before P-read** (`p_store_before_read`): each P store is
  `WaitBefore .waitSt` the lane's later events: the PV MMA that reads it.
* **OFinal** (`f_doneBefore`): the epilogue's poll of `o_final` observes `cm`'s only commit, so
  every MMA is done before the epilogue's later events: **PV accumulate before the O read and the
  dealloc's TMEM users**.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow AsyncCopy TcMma
open PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section

variable {L : Launch} {X : Execution} {c cm p0 : Nat} {K : Kernel} {A : List Assumption}
  {mem0 : Mem0}

/-- An MMA issue. -/
def IsMma (X : Execution) (i : EvId) : Prop := ∃ d s acc mask, X.MmaIssue i d s acc mask

/-- An MMA's event. -/
theorem IsMma.get {i : EvId} (h : IsMma X i) :
    ∃ pc d s acc mask, X.get i = some ⟨pc, .tc (.mma d s acc mask)⟩ := by
  obtain ⟨d, s, acc, mask, pc, hp⟩ := h
  exact ⟨pc, d, s, acc, mask, hp⟩

/-- Program order from an event that is no memory access is causality. -/
theorem baseCausality_src {e f : EvId} {ev : Event} (he : X.get e = some ev)
    (hacc : ev.acc = none) (hs : e.1 = f.1) (hlt : e.2 < f.2) (hf : f.2 < (X.tr f.1).length) :
    baseCausality L X e f :=
  .single (.inl (po_of_source_not_access hs hlt hf (by rw [he]; exact hacc)))

/-! ### `s_ready`: S written by the MMA, read by the default partition -/

/-- **SFull**: a poll of `s_ready b` with `u` earlier successful polls observes the notification
of `cm`'s commit with `u` earlier commits to the barrier, given the reuse premise of the polling
thread (`Notify.Reach`: the commit of use `t` follows the thread's polls for the uses before
`t`). -/
theorem s_observes (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) {b : Nat} (hb : b < 2)
    {h j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (hR : MbarRing.Notify.Reach L K A X (sReady L c b) cm (sReady L c b) 0 h)
    (he : X.get (h, j) = some ⟨pc, .wait (sReady L c b) p true acq sc⟩)
    (hq : okPolls (sReady L c b) ((X.tr h).take j) = u) :
    ∃ i pc' sp rank, X.get (cm, i) = some ⟨pc', .tc (.commit sp)⟩ ∧ sp.mbar = sReady L c b ∧
      TcCommit.target sp rank = some (sReady L c b) ∧
      ((X.tr cm).take i).countP (commitsTo (sReady L c b)) = u ∧
      rank ∈ X.tcNotified (cm, i) ∧
      WaitObserves X (.async (cm, i) (.tcNotify rank)) (h, j) (sReady L c b) acq sc :=
  (sObj hX F hb).observes hX hR he (by omega)

/-- **S-write before S-read.** Every MMA of `cm` issued before the commit that the poll observes
(`x` has at most `u` earlier commits to `s_ready b`) is done before every event of the polling
thread after its poll: the commit tracks all earlier MMAs of its thread, and the poll (an acquire
at CTA scope of a thread of the CTA) observes it. -/
theorem s_doneBefore (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm) {b : Nat} (hb : b < 2)
    {h j pc p u f : Nat} {sc : MbarScope} (hcta : SameCta L cm h)
    (hR : MbarRing.Notify.Reach L K A X (sReady L c b) cm (sReady L c b) 0 h)
    (he : X.get (h, j) = some ⟨pc, .wait (sReady L c b) p true true sc⟩)
    (hq : okPolls (sReady L c b) ((X.tr h).take j) = u) {x : EvId} (hx : IsMma X x)
    (hxc : x.1 / L.block = c)
    (hu : ((X.tr cm).take x.2).countP (commitsTo (sReady L c b)) ≤ u) (hjf : j < f)
    (hf : f < (X.tr h).length) : DoneBefore L X x (h, f) := by
  obtain ⟨i, pcx, sp, rank, hget, hmbar, htgt, hcnt, hrank, hobs⟩ := s_observes hX F hb hR he hq
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
      hrank⟩, hobs⟩, ?_, baseCausality_src he rfl rfl hjf hf⟩
  rw [hthr]
  exact MbarRing.Unit.Gate.scopesMeet hcta _ _

/-! ### `p_ready`: P written by the default partition, read by the MMA -/

/-- **PReady**: an MMA lane's poll of `p_ready b` with `q` earlier successful polls synchronizes
with thread 0's arrival with `q` earlier arrivals, given the reuse premise of each polling lane
(`Unit.Reach`: thread 0's arrival of use `t` follows the lane's polls for the uses before `t`) and
that the lanes are threads of the CTA. -/
theorem p_handoff (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) {b : Nat} (hb : b < 2)
    {cons : Nat → Prop}
    (hR : ∀ h, cons h → MbarRing.Unit.Reach L K A X (pReady L c b) 1 (fun _ => p0) 0 h)
    (hacq : ∀ {h j pc p : Nat} {acq : Bool} {sc : MbarScope}, cons h →
      X.get (h, j) = some ⟨pc, .wait (pReady L c b) p true acq sc⟩ → acq = true)
    (hcta : ∀ h, cons h → SameCta L p0 h) :
    MbarRing.UnitHandoff L X (pReady L c b) (fun g => ∃ _ : Fin 1, g = p0) cons 0 :=
  (pObj hX F hb).handoff hX hR hacq
    (fun hh _ _ => MbarRing.Unit.Gate.scopesMeet (hcta _ hh) _ _)

/-- **Thread 0's events up to its arrival happen before the MMA lane's events after its poll.**
Event `e` of thread 0 has at most `q` arrivals on `p_ready b` before it, and the lane `h` has more
than `q` successful polls of it before `f`. -/
theorem p_before_pv {b : Nat} {cons : Nat → Prop}
    (hU : MbarRing.UnitHandoff L X (pReady L c b) (fun g => ∃ _ : Fin 1, g = p0) cons 0)
    {h e f q : Nat} (hh : cons h)
    (he : arrivals (pReady L c b) ((X.tr p0).take e) ≤ q)
    (hf : q + 1 ≤ okPolls (pReady L c b) ((X.tr h).take f)) (hfl : f < (X.tr h).length) :
    baseCausality L X (p0, e) (h, f) :=
  hU.baseCausality_of_counts hh ⟨0, rfl⟩ he (by omega) hfl

/-- **P-write before P-read.** A `tcgen05.st` of thread `t` of the P tile is done before the MMA
lane's event `f` (the PV MMA that reads it from Tensor Memory, `StoreDoneBefore`) when `t`'s
`tcgen05.wait::st` after the store comes before thread 0's arrival (the named-barrier premise:
`bar.sync 0, 128` between every thread's wait and thread 0's arrival) and the lane has more than
`q` polls of `p_ready` before `f`. -/
theorem p_store_before_read {b : Nat} {cons : Nat → Prop}
    (hU : MbarRing.UnitHandoff L X (pReady L c b) (fun g => ∃ _ : Fin 1, g = p0) cons 0)
    {t sk wk e h f q pcw a : Nat} {vals : List Value} {sh : TcShape}
    (hst : X.TSt (t, sk) a vals sh) (hw : X.get (t, wk) = some ⟨pcw, .tc .waitSt⟩) (hsk : sk < wk)
    (hbar : baseCausality L X (t, wk) (p0, e))
    (he : arrivals (pReady L c b) ((X.tr p0).take e) ≤ q) (hh : cons h)
    (hf : q + 1 ≤ okPolls (pReady L c b) ((X.tr h).take f)) (hfl : f < (X.tr h).length) :
    StoreDoneBefore L X (t, sk) (h, f) :=
  ⟨⟨a, vals, sh, hst⟩, .inl ⟨(t, wk), ⟨pcw, hw⟩, rfl, hsk,
    .inl (hbar.trans (p_before_pv hU hh he hf hfl))⟩⟩

/-! ### `o_final`: the last PV accumulate, read by the epilogue -/

/-- **The reuse premise of `o_final` holds**: `cm` commits to it once (the first commit has no
earlier one), so no counted unit has an earlier use for a poll to precede. -/
theorem fReach (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0) (h : Nat)
    (hone : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (oFinal L c)) = 0) :
    MbarRing.Notify.Reach L K A X (oFinal L c) cm (oFinal L c) 0 h := by
  intro x hx j hj
  obtain ⟨-, pc, sp, hget, hm, -, hc⟩ := (fObj hX F).S_rec hx
  have := hone hget hm
  omega

variable (hX : Consistent L K A mem0 X) (F : Facts L X c cm p0)
    (hone : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm)
    (hcommit : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (oFinal L c)) = 0)
    (hbefore : ∀ {x : EvId}, IsMma X x → x.1 / L.block = c → ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = oFinal L c → x.2 < i)
include hX F hone hcommit hbefore

/-- **Every MMA is done before every event that follows the epilogue's poll of `o_final`**, for any
event `e` the poll happens before in causality (`hbc`): an epilogue thread's poll of `o_final`
observes `cm`'s only commit to it, and every MMA is issued before that commit (`hbefore`: the commit
follows the loop). -/
theorem f_doneBefore_at {h j pc p : Nat} {sc : MbarScope} (hcta : SameCta L cm h)
    (he : X.get (h, j) = some ⟨pc, .wait (oFinal L c) p true true sc⟩) {x e : EvId} (hx : IsMma X x)
    (hxc : x.1 / L.block = c) (hbc : baseCausality L X (h, j) e) :
    DoneBefore L X x e := by
  have hq : okPolls (oFinal L c) ((X.tr h).take j) + 0 = okPolls (oFinal L c) ((X.tr h).take j) :=
    rfl
  obtain ⟨i, pcx, sp, rank, hget, hmbar, htgt, hcnt, hrank, hobs⟩ :=
    (fObj hX F).observes hX (fReach hX F h hcommit) he hq
  have hthr : x.1 = cm := hone hx hxc
  have hlt : x.2 < i := hbefore hx hxc hget hmbar
  refine .inl ⟨(h, j), sc, ⟨.async (cm, i) (.tcNotify rank), oFinal L c,
    ⟨(cm, i), sp, rank, rfl, ⟨hthr.symm ▸ rfl, hlt, .inl hx, sp, pcx, hget⟩, ⟨pcx, hget⟩, htgt,
      hrank⟩, hobs⟩, ?_, hbc⟩
  rw [hthr]
  exact MbarRing.Unit.Gate.scopesMeet hcta _ _

/-- **PV accumulate before the O read.** Every MMA is done before every event of the epilogue
thread after its poll of `o_final`: before its `tcgen05.ld` of the `O` tile. -/
theorem f_doneBefore {h j pc p f : Nat} {sc : MbarScope} (hcta : SameCta L cm h)
    (he : X.get (h, j) = some ⟨pc, .wait (oFinal L c) p true true sc⟩) {x : EvId} (hx : IsMma X x)
    (hxc : x.1 / L.block = c) (hjf : j < f) (hf : f < (X.tr h).length) :
    DoneBefore L X x (h, f) :=
  f_doneBefore_at hX F hone hcommit hbefore hcta he hx hxc (baseCausality_src he rfl rfl hjf hf)

end
end PTX.Kernels.InklingRelDecode.Proof.SO
