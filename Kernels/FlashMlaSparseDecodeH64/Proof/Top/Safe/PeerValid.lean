-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.LoWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TcSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerPair
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxPeer
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen

@[expose] public section

/-! # A peer read keeps warpgroup 0's trace valid

The read at pc `477 + 5 k0` is element 0 or 1 of the lane's slot (`w0_pld_el`). Element 0 leaves
the block's pair `k0` unchanged. Element 1 finishes it, and the pair is the partner's low words
at its peer store (`peer_pair_at`), which read as numbers (`lo_at_pst_at`) from the partner's
prefix before the store and the words of the events before the read in the tcgen05 order. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The bar events before an access run are the same**: no event of `[a, b)` is a barrier. -/
theorem countP_bar_run {X : Execution} {g n a b : Nat} (hab : a ≤ b) (hb : b ≤ (X.tr g).length)
    (hacc : ∀ q, a ≤ q → q < b → ((X.get (g, q)).bind Event.acc).isSome) :
    ((X.tr g).take a).countP (Execution.isBarId n) =
      ((X.tr g).take b).countP (Execution.isBarId n) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    obtain ⟨ev, hev⟩ : ∃ ev, X.get (g, b) = some ev :=
      ⟨_, (List.getElem?_eq_getElem (by omega : b < (X.tr g).length) : (X.tr g)[b]? = _)⟩
    rw [ih (by omega) (fun q h1 h2 => hacc q h1 (by omega)), trace_take_succ hev,
      List.countP_append]
    have := hacc b hab (by omega)
    rw [hev] at this
    obtain ⟨pc, kd⟩ := ev
    cases kd <;> simp_all [Event.acc, Execution.isBarId]

/-- **The partner's low words at its peer stores below a read** (valid rows): not empty, finite. -/
theorem w0_peer_lo (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {g kb k0 : Nat}
    (hg : g < L.threads) (hw : warp L g < 4) (hk0 : k0 < 8)
    (hbelow : W0Below P L X (w0Partner L g) g kb)
    (hcl : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, kb) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w) :
    ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 403 + 10 * k0 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, kb) →
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo ≠ [] ∧ ∀ c < 32, ∃ x : ℝ,
      (w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c (.pred false) =
        .float .f32 x := fun j f hf hfp htc => by
  obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
  obtain ⟨hne, -, hfl, -⟩ := lo_at_pst_at hp hIn hX hFw hwh
    (Wg0.W0Valid.take_le (hbelow j f hf htc).1 (Nat.le_succ j))
    (fun w e' hw' htc' => hcl w e' hw' (htc'.trans htc)) hk0 hf (tcTrans_nonUb hX htc hf) hfp
  exact ⟨hne, hfl⟩

/-- **The words of a peer read** (valid rows): the two halves of the 64-bit word read as finite
numbers. -/
theorem w0_pay_peer (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {g k k0 : Nat}
    {a : Acc} {bs : List (Option Byte)} (hw : warp L g < 4) (hk0 : k0 < 8)
    (he : X.get (g, k) = some ⟨477 + 5 * k0, .rd a bs⟩)
    (hbelow : W0Below P L X (w0Partner L g) g k)
    (hcl : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w) :
    ∃ v, rebuild 3 bs = .ok v ∧ W0Fin (splitValue 64 v).1 ∧ W0Fin (splitValue 64 v).2 := by
  obtain ⟨r, hr, -, hcnt⟩ := peer_cnt hp hX hFw hw hk0 he
  have hne := w0_peer_lo hp hIn hX hFw (Frame.lt_of_get hX he) hw hk0 hbelow hcl
  obtain ⟨j, f, el, hf, hfp, -, htc, hel, -, hval⟩ := peer_read_value hp hX hFw
    (hIn.bar hp X hX hFw) hw hk0 he hcnt (List.getElem?_eq_some_iff.mp he).1 hcnt hr hbelow
    (fun j f hf hfp htc => (hne j f hf hfp htc).1) (fun j f hf hfp htc => (hne j f hf hfp htc).2)
  obtain ⟨x0, h0⟩ := (hne j f hf hfp htc).2 (4 * k0 + 2 * el) (by omega)
  obtain ⟨x1, h1⟩ := (hne j f hf hfp htc).2 (4 * k0 + 2 * el + 1) (by omega)
  rw [h0, h1] at hval
  simp only [w0RdVal, Option.some.injEq] at hval
  cases hrb : rebuild 3 bs with
  | error f => simp [hrb, Except.toOption] at hval
  | ok v =>
    simp only [hrb, Except.toOption, Option.getD_some] at hval
    subst hval
    exact ⟨_, rfl, ⟨x0, by simp [valFloat]; rfl⟩, ⟨x1, by simp [valFloat]; rfl⟩⟩

/-- **A peer read keeps the trace valid**: `hbelow` is the partner's valid prefixes before the
base event `(g, kb)` of the read's vector access in the tcgen05 order, `hcl` the words of the
Tensor Memory below it; between the read and the base only memory accesses occur. -/
theorem w0Valid_snoc_peer (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {g k kb : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hw : warp L g < 4) {k0 : Nat}
    (hk0 : k0 < 8) (hpc : e.pc = 477 + 5 * k0) (hkbl : kb < (X.tr g).length)
    (hbtw : ∀ q, min k kb ≤ q → q ≤ max k kb → ((X.get (g, q)).bind Event.acc).isSome)
    (hbelow : W0Below P L X (w0Partner L g) g kb)
    (hcl : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, kb) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  have he0 := he
  rw [trace_take_succ he]
  obtain ⟨a, bs, el, hk, hel, hws, hpar⟩ := w0_peer_el hp hX hFw hw h hk0 he hub hpc
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hk
  have hr : (w0RdVal ⟨pc, .rd a bs⟩).isSome := by simp [w0RdVal]
  have hc : (⟨pc, .rd a bs⟩ : Event).pc ≠ w0ArrSPc ∧ (⟨pc, .rd a bs⟩ : Event).pc ≠ w0ArrLPc := by
    show pc ≠ w0ArrSPc ∧ pc ≠ w0ArrLPc
    simp only [w0ArrSPc, w0ArrLPc]; omega
  obtain ⟨hb, -, -⟩ := w0_boundSeen hp hX hFw hw he (fun f hf => by cases hf)
    (by simp only; omega) h
  have hfs : (w0Fin ((X.tr g).take k)).2 = (w0Scan ((X.tr g).take k)).2 := w0Fin_snd _
  refine w0Core_peer hp.scalePos hk0 hpc hb ?_ h
  rw [hfs]
  have hel' : el = 0 ∨ el = 1 := by omega
  rcases hel' with rfl | rfl
  · exact Or.inl (w0Peer_snoc_first hpc hr hpar)
  · refine Or.inr ?_
    have he1 : X.get (g, k) = some ⟨477 + 5 * k0, .rd a bs⟩ := by rw [← hpc]; exact he0
    have hg := Frame.lt_of_get hX he0
    obtain ⟨-, hwh, -, -⟩ := w0Partner_facts hp hw hg
    obtain ⟨r, -, hr1, hcnt⟩ := peer_cnt hp hX hFw hw hk0 he1
    have hkb : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he0).1
    have hsp := trace_take_succ he0
    have hcl' : w0Closed ((X.tr g).take (k + 1)) = w0Closed ((X.tr g).take k) := by
      rw [hsp]
      simp only [w0Closed, List.countP_append, List.countP_cons, List.countP_nil]
      have : ¬ pc = w0ArrSPc := hc.1
      simp [this]
    have hsc : (w0Scan ((X.tr g).take (k + 1))).2 =
        (w0Scan ((X.tr g).take k)).2 ++ [⟨pc, .rd a bs⟩] := by
      rw [hsp, w0Scan_snoc_quiet hc]
    have hn2 : 2 ≤ ((w0Scan ((X.tr g).take (k + 1))).2.filter fun e =>
        e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length := by
      rw [hsc, List.filter_append]
      simp only [List.length_append]
      have h2 : ([(⟨pc, .rd a bs⟩ : Event)].filter fun e =>
          e.pc = 477 + 5 * k0 && (w0RdVal e).isSome).length = 1 := by
        simp [hpc, w0RdVal]
      rw [h2]
      omega
    have hnb : ((X.tr g).take kb).countP (Execution.isBarId (10 + warp L g % 2)) =
        w0Closed ((X.tr g).take (k + 1)) + 1 := by
      have hbase : ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) =
          w0Closed ((X.tr g).take (k + 1)) + 1 := by rw [hcnt, hcl', hr1]
      rw [← hbase]
      rcases le_total k kb with hle | hle
      · exact (countP_bar_run hle hkbl.le (fun q h1 h2 => hbtw q (by omega) (by omega))).symm
      · exact countP_bar_run hle hkb.le (fun q h1 h2 => hbtw q (by omega) (by omega))
    have hne := w0_peer_lo hp hIn hX hFw hg hw hk0 hbelow hcl
    obtain ⟨j, f, hf, hfp, htc, -, hpeer⟩ := peer_pair_at hp hX hFw (hIn.bar hp X hX hFw) hw
      h hk0 le_rfl hkbl hn2 (LaneUbFree.succ (noUbBefore_of_get hX he0) he0 hub) hnb hbelow
      (fun j f hf hfp htc => (hne j f hf hfp htc).1)
      (fun j f hf hfp htc => (hne j f hf hfp htc).2)
    have hfin : (w0Fin ((X.tr g).take (k + 1))).2 = (w0Scan ((X.tr g).take k)).2 ++
        [⟨pc, .rd a bs⟩] := by rw [w0Fin_snd, hsc]
    rw [hfin] at hpeer
    rw [hpeer]
    obtain ⟨-, hfl⟩ := hne j f hf hfp htc
    have hfin' : ∀ c < 32, W0Fin ((w0Words (w0Fin ((X.tr (w0Partner L g)).take j)).2).lo.getD c
        (.pred false)) := fun c hc => by
      obtain ⟨x, hx⟩ := hfl c hc
      rw [hx]
      exact ⟨x, by simp [valFloat]; rfl⟩
    exact ⟨hfin' _ (by omega), hfin' _ (by omega), hfin' _ (by omega), hfin' _ (by omega)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
