-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.ResultFloat
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeCarry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.RunClass
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAProof
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.PvWordAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.OpcValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PeerValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.PmValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.ScoreValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TcSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.VoteValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PrevPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SamePc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCut
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidPeer
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidRestart
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.VmKind
import Lemmas.Order.OrderBaseCausality
import Lemmas.Tcgen05.ValuesByTcOrder

@[expose] public section

/-! # The step of warpgroup 0's valid trace

`Safe.w0Hq`: the claim `W0Q` at an event, from the claims and the facts of the Tensor Memory words
at the events below it in the tcgen05 order. The claim is the validity of the lane's prefix
through every element of the vector access at the event (`W0Run`) and, at a read of the exchange
word (pc 572), that the word read differs from the default. The elements of a vector access are
at one pc, a peer read's or a quiet one (`w0_vec_pair`), so only the run of a single event has a
clause at any other pc. -/

/-! # The words of the Tensor Memory and warpgroup 0's valid traces, by one induction

`Safe.tmJoint`: a claim `Q` about the events of warpgroup 0 (its lane's valid prefix) is proved
together with the facts of the Tensor Memory words (`TmClaim`, `RfClaim`) by induction on the
tcgen05 order (`Frame.values_by_tcStep`). The operand elements of a PV MMA and a rescale store's
words need the validity of warpgroup 0's prefixes only for the writes and the loads before them,
which are before the event in that order (`pv_a_tc`, `po`); so no fact consumes the validity of a
whole trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The empty trace is valid.** -/
theorem w0Valid_nil (sc : ℝ) : W0Valid sc [] := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
    simp only [List.length_nil, nonpos_iff_eq_zero] at hj <;> subst hj <;>
    simp [W0Now, W0Early, W0EpiOk, w0Fin, w0Scan, w0SkWord, w0EpiPe, w0EpiO, w0SkRaw, w0Last,
      w0NegInf]

/-- **The joint induction**: a claim `Q` of the events with the facts of the words. The claim at
an event follows from the claims and facts at the events before it in the tcgen05 order
(`hQ`); `hQv` says a claim at `(g, k)` is the validity of the lane's prefix through the event. -/
theorem Safe.tmJoint (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (Q : EvId → Prop)
    (hQv : ∀ g k, Q (g, k) → warp L g < 4 → NonUbAt X (g, k) →
      W0Valid P.scale ((X.tr g).take (k + 1)))
    (hQ : ∀ w e, X.get w = some e →
      (∀ j e', X.get j = some e' → Relation.TransGen (TcMma.TcStep L X) j w →
        Q j ∧ TmRace.TmClaim L X j ∧ TmRace.RfClaim L X j) → Q w) :
    ∀ w e, X.get w = some e → Q w ∧ TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w := by
  have hT : TmemRows P L X := tmem_rows hp hX hFw
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hPS : TmRace.PvStoreOrder L X := Safe.pvStore hp hIn hX hFw
  have hG : SyncGuarded L kernel X := Safe.guarded hp hIn hX hFw
  have ht : Tmem.One.Tmem1Facts L X 0 := Safe.tmemOne hp hIn hX hFw
  have hb := Safe.tmBase hp hIn hX hFw
  have hMb : MbarRows P L X := hIn.mbar hp X hX hFw
  have hI : InitRows L X := hIn.initRows hp X hX hFw
  have hB : Bar0Rows L X := hIn.bar0 hp X hX hFw
  have hN : DequantInputs L X := hIn.dequant hp X hX hFw
  have hBr : BarRows P L X := hIn.bar hp X hX hFw
  have hSi : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask :=
    fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi
  refine Frame.values_by_tcStep hX hG _ fun w e hwe ih => ?_
  have hQw := hQ w e hwe ih
  have hbelow : ∀ h k2 ev, X.get (h, k2) = some ev →
      Relation.TransGen (TcMma.TcStep L X) (h, k2) w → warp L h < 4 →
      W0Valid P.scale ((X.tr h).take k2) := fun h k2 ev hev htc hw =>
    Wg0.W0Valid.take_le (hQv h k2 (ih _ _ hev htc).1 hw
      fun _ he => tcTrans_nonUb hX htc he) (Nat.le_succ k2)
  have hEw : MmaElemAt X w := TmRace.mma_elem_at hp hX hFw hMb hI hB hN hb.hv hSi hT hO ht
    hb.hmd w fun d s acc mask ops row col cell hi hd hops hc hd256 =>
      TmRace.pv_a_elem_at hp hX hFw hMb hI hB hBr hSi hT hbelow d s acc mask ops row col cell
        hi hd hops hc hd256
  obtain ⟨g, k⟩ := w
  have hSw : RescaleStepAt L X (g, k) := by
    intro cell old hsv
    refine w0_rescale_step_at hp hX hFw (fun hw => ?_) cell old hsv
    rcases k with _ | k'
    · simpa using w0Valid_nil P.scale
    · obtain ⟨a, vals, sh, jj, ⟨pc, he⟩, -, -⟩ := id hsv
      have hlen : k' + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      have hev : X.get (g, k') = some (X.tr g)[k'] :=
        List.getElem?_eq_getElem (show k' < (X.tr g).length by omega)
      have hpo : po X (g, k') (g, k' + 1) :=
        po_of_not_access rfl (Nat.lt_succ_self _) hlen (by rw [he]; rfl)
      exact hQv g k' (ih _ _ hev (.single (.inl (.single (.inl hpo))))).1 hw
        fun _ he' => noUb_kind_of_lt hX he' (Nat.lt_succ_self _) hlen
  refine ⟨hQw, TmRace.tm_step hp hX hFw hT hO hPS hG ht hb.hmd hMb hI hB hN hBr
    (fun j e' hj htg => (ih j e' hj htg).2.1) hEw hSw,
    TmRace.result_float_step hp hX hT hO hG hEw (fun s e' hs hdep cell old hst =>
      (ih s e' hs hdep).2.1.2 cell old hst) fun s e' hs hdep => (ih s e' hs hdep).2.2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At a read of the exchange word the word read is not the default. -/
def W0Flag (L : Launch) (X : Execution) (w : EvId) : Prop :=
  warp L w.1 < 4 → ∀ a bs, X.get w = some ⟨572, .rd a bs⟩ →
    (w0Words (w0Fin ((X.tr w.1).take (w.2 + 1))).2).pm ≠ .pred false

/-- **The claim of the trace's induction.** -/
def W0Q (P : Params) (L : Launch) (X : Execution) (w : EvId) : Prop :=
  W0Run P L X w ∧ W0Flag L X w

/-- An event that is neither quiet nor a peer read is in program order after the event before. -/
theorem po_of_class {g j : Nat} {f1 f : Event} (hp : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L g < 4) (h1 : X.get (g, j) = some f1) (hf : X.get (g, j + 1) = some f)
    (hnq : ¬ W0Quiet f) (hnp : ¬ ∃ k0, k0 < 8 ∧ f.pc = 477 + 5 * k0) :
    po X (g, j) (g, j + 1) := by
  have hl : j + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨rfl, Nat.lt_succ_self _, hl, fun hs => ?_⟩
  rcases Wg0.Control.w0_vec_pair hp hX hFw (noUbBefore_of_get hX hf) hw h1 hf hs with
      ⟨k0, hk0, hk, hpc⟩ | ⟨-, hq⟩
  · exact hnp ⟨k0, hk0, by omega⟩
  · exact hnq hq

/-- The index of an event with an access is below the trace's length. -/
theorem lt_length_of_acc {g m : Nat} (h : ((X.get (g, m)).bind Event.acc).isSome) :
    m < (X.tr g).length := by
  by_contra hc
  have : X.get (g, m) = none := by
    show (X.tr g)[m]? = none
    exact List.getElem?_eq_none (by omega)
  simp [this] at h

/-- **The step of the trace's induction at an event of warpgroup 0**, from the claims below it. -/
theorem Safe.w0Hq (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ∀ w e, X.get w = some e →
      (∀ j e', X.get j = some e' → Relation.TransGen (TcMma.TcStep L X) j w →
        W0Q P L X j ∧ TmRace.TmClaim L X j ∧ TmRace.RfClaim L X j) → W0Q P L X w := by
  rintro ⟨g, k⟩ e hwe ih
  by_cases hw : warp L g < 4
  swap
  · exact ⟨fun h => absurd h hw, fun h => absurd h hw⟩
  have hg : g < L.threads := Frame.lt_of_get hX hwe
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hwe).1
  have hbc : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w :=
    fun w e' hw' ht => ⟨(ih w e' hw' ht).2.1, (ih w e' hw' ht).2.2⟩
  have hUnder : W0Under P L X g k := fun y j f hf hwy ht => ((ih (y, j) f hf ht).1.1).valid hwy
    fun _ he => tcTrans_nonUb hX ht he
  have hbel : ∀ h k2 ev, X.get (h, k2) = some ev →
      Relation.TransGen (TcMma.TcStep L X) (h, k2) (g, k) → warp L h < 4 →
      W0Valid P.scale ((X.tr h).take k2) := fun h k2 ev hev htc hwh =>
    Wg0.W0Valid.take_le (hUnder h k2 ev hev hwh htc) (Nat.le_succ k2)
  have hEb := Safe.mmaElemBelow hp hIn hX hFw (b := (g, k)) hbel
  have hWB : W0Below P L X (w0Partner L g) g k := fun j e' hj ht => ⟨
    hUnder _ j e' hj (w0Partner_facts hp hw hg).2.1 ht, tcTrans_nonUb hX ht hj⟩
  have hsuc : ∀ j, j + 1 < (X.tr g).length → NonUbAt X (g, j) := fun j hj _ he' =>
    noUb_kind_of_lt hX he' (Nat.lt_succ_self j) hj
  have hal0 : LaneUbFree X g k := noUbBefore_of_get hX hwe
  have hat : ∀ f : Event, 103 ≤ f.pc → f.pc < 1842 → Wg0At L g f.pc := fun f h1 h2 => ⟨hw, h1, h2⟩
  have hMb := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hB := hIn.bar0 hp X hX hFw
  have hN := hIn.coord hp X hX hFw
  -- the prefix before the event, when the event is no element of a vector access
  have hprev : ∀ j, j + 1 = k → ∀ f1, X.get (g, j) = some f1 → ¬ W0Quiet e →
      (¬ ∃ k0, k0 < 8 ∧ e.pc = 477 + 5 * k0) → W0Valid P.scale ((X.tr g).take k) := by
    intro j hj f1 hf1 hnq hnp
    subst hj
    have hpo := po_of_class hp hX hFw hw hf1 hwe hnq hnp
    exact ((ih _ _ hf1 (.single (.inl (.single (.inl hpo))))).1.1).valid hw (hsuc _ hk)
  -- the clause of the event at `k`, when no other element of a vector access is at `k`
  have hsingle : NonUbAt X (g, k) → W0Valid P.scale ((X.tr g).take k) →
      W0Valid P.scale ((X.tr g).take (k + 1)) := by
    intro hn hv
    have hubk : ∀ f, e.kind ≠ .ub f := hn e hwe
    rcases w0Quiet_or e with hq | h103 | h156 | h200 | h1122 | h278 | h280 | h283 | h285 | h289 |
      h572 | h578 | h1157 | ⟨k0, hk0, hpc⟩ | hopc
    · rw [trace_take_succ hwe]; exact hv.snoc_quiet hp.scalePos hq
    · exact w0Valid_snoc_sink_pre hp hX hFw hal0 hwe (hat e (by omega) (by omega)) (Or.inl h103) hv
    · exact w0Valid_snoc_sink_pre hp hX hFw hal0 hwe (hat e (by omega) (by omega)) (Or.inr h156) hv
    · exact w0Valid_snoc_restart_hub hp hX hFw hwe hubk hw h200 hv
    · exact w0Valid_snoc_cut_alive hp hX hFw (LaneAlive.of_get hal0 hwe hubk) hw hwe h1122 hv
    · exact w0Valid_snoc_score hp hIn hX hFw hwe hubk hw (Or.inl h278) hbc hv
    · exact w0Valid_snoc_score hp hIn hX hFw hwe hubk hw (Or.inr (Or.inl h280)) hbc hv
    · exact w0Valid_snoc_score hp hIn hX hFw hwe hubk hw (Or.inr (Or.inr (Or.inl h283))) hbc hv
    · exact w0Valid_snoc_score hp hIn hX hFw hwe hubk hw (Or.inr (Or.inr (Or.inr h285))) hbc hv
    · obtain ⟨a, bs, hkd⟩ := wg0_vmKind hp hX hFw hwe hubk h289
      have he2 : X.get (g, k) = some ⟨289, .rd a bs⟩ := by
        obtain ⟨pc, kd⟩ := e
        simp only at h289 hkd
        subst h289 hkd
        exact hwe
      exact w0Valid_snoc_mask hp hX hFw hMb hI hB hN he2 hw hv
    · obtain ⟨a, bs, hkd, -⟩ := (wg0_peerPlace hp hX hFw hwe hubk (hat e (by omega) (by omega))
        (Or.inr (Or.inl h572))).2 (Or.inl h572)
      have he2 : X.get (g, k) = some ⟨572, .rd a bs⟩ := by
        obtain ⟨pc, kd⟩ := e
        simp only at h572 hkd
        subst h572 hkd
        exact hwe
      exact (w0Valid_snoc_pm hp hIn hX hFw he2 hw hWB hv).1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
        cases k with
        | zero => exact (Wg0.w0_not_first hp hX hFw hwe hubk ⟨by omega, by omega⟩).elim
        | succ j => exact ⟨j, rfl⟩
      have hb : w0Body e.pc = true := by rw [h578]; decide
      obtain ⟨f1, hf1, hfp⟩ := w0_prev_pc hp hX hFw hw hwe hubk hb hv
      have h572 : f1.pc = 572 := by rw [h578] at hfp; simpa [w0Prev] using hfp
      obtain ⟨a, bs, hkd, -⟩ := (wg0_peerPlace hp hX hFw hf1
        (noUb_kind_of_lt hX hf1 (Nat.lt_succ_self j) hk) (hat f1
        (by omega) (by omega))
        (Or.inr (Or.inl h572))).2 (Or.inl h572)
      have he1 : X.get (g, j) = some ⟨572, .rd a bs⟩ := by
        obtain ⟨pc, kd⟩ := f1
        simp only at h572 hkd
        subst h572 hkd
        exact hf1
      have hpo := po_of_class hp hX hFw hw hf1 hwe (fun hq => hq.vt h578)
        (fun ⟨k0, hk0, h⟩ => by omega)
      have hpm := (ih _ _ hf1 (.single (.inl (.single (.inl hpo))))).1.2 hw a bs he1
      exact w0Valid_snoc_vote hp hIn hX hFw hwe hubk hw h578 hpm hv
    · obtain ⟨a, bs, hkd, -⟩ := (wg0_peerPlace hp hX hFw hwe hubk (hat e (by omega) (by omega))
        (Or.inr (Or.inr (Or.inr h1157)))).2 (Or.inr h1157)
      have he2 : X.get (g, k) = some ⟨1157, .rd a bs⟩ := by
        obtain ⟨pc, kd⟩ := e
        simp only at h1157 hkd
        subst h1157 hkd
        exact hwe
      exact w0Valid_snoc_pe hp hIn hX hFw hw he2 hv hUnder
    · obtain ⟨a, bs, el, hkd, -⟩ := w0_peer_el hp hX hFw hw hv hk0 hwe hubk hpc
      refine w0Valid_snoc_peer hp hIn hX hFw hwe hubk hw hk0 hpc hk (fun q h1 h2 => ?_) hWB hbc hv
      have hacc : e.acc = some a := by
        obtain ⟨pc, kd⟩ := e
        simp only at hkd
        subst hkd
        rfl
      rw [show q = k by omega]
      simp [hwe, hacc]
    · exact w0Valid_snoc_opc hp hIn hX hFw hwe hubk hw hopc hbc hEb hv
  have hpre : ∀ s, s ≤ k → (s = k ∨ SameAccess X (g, s) (g, k)) →
      (∀ j, j < s → ¬ SameAccess X (g, j) (g, k)) → W0Valid P.scale ((X.tr g).take s) := by
    intro s hsk _ hmin
    rcases s with _ | s'
    · simpa using w0Valid_nil P.scale
    · have hlen' : s' < (X.tr g).length := by omega
      have hev : X.get (g, s') = some (X.tr g)[s'] := List.getElem?_eq_getElem hlen'
      have hpo : po X (g, s') (g, k) := ⟨rfl, by omega, hk, hmin s' (by omega)⟩
      exact ((ih _ _ hev (.single (.inl (.single (.inl hpo))))).1.1).valid hw (hsuc _ (by omega))
  have hstep : ∀ s m j, s ≤ k → (s = k ∨ SameAccess X (g, s) (g, k)) → k ≤ m →
      (m = k ∨ SameAccess X (g, k) (g, m)) → RunIn X g s m j → NonUbAt X (g, j) →
      W0Valid P.scale ((X.tr g).take j) → W0Valid P.scale ((X.tr g).take (j + 1)) := by
    intro s m j hsk hs hkm hm hj hnj hv
    obtain ⟨hsj, hjm, -⟩ := hj
    have hSA : s = m ∨ SameAccess X (g, s) (g, m) := by
      rcases hm with rfl | hm
      · rcases hs with rfl | hs
        · exact Or.inl rfl
        · exact Or.inr hs
      · rcases hs with rfl | hs
        · exact Or.inr hm
        · exact Or.inr (sameAccess_trans hs hm hsk hkm)
    have hmlen : m < (X.tr g).length := by
      rcases hm with rfl | hm
      · exact hk
      · exact lt_length_of_acc hm.1
    have hjlen : j < (X.tr g).length := by omega
    obtain ⟨f, hf⟩ : ∃ f, X.get (g, j) = some f := ⟨_, List.getElem?_eq_getElem hjlen⟩
    by_cases hq : W0Quiet f
    · rw [trace_take_succ hf]; exact hv.snoc_quiet hp.scalePos hq
    by_cases hsm : s = m
    · have hjk : j = k := by omega
      subst hjk
      have hfe : f = e := Option.some.inj (hf.symm.trans hwe)
      subst hfe
      exact hsingle hnj hv
    have hSA' : SameAccess X (g, s) (g, m) := hSA.resolve_left hsm
    have hcls : ∃ k0, k0 < 8 ∧ f.pc = 477 + 5 * k0 := by
      by_cases hjm' : j < m
      · obtain ⟨f', hf'⟩ : ∃ f', X.get (g, j + 1) = some f' :=
          Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind (sameAccess_acc hSA'
            (by omega) (by omega)))
        rcases Wg0.Control.w0_vec_pair hp hX hFw (noUbBefore_of_get hX hf') hw hf hf'
          (sameAccess_adj hSA' hsj hjm')
          with ⟨k0, hk0, hpc, -⟩ | ⟨hqf, -⟩
        · exact ⟨k0, hk0, hpc⟩
        · exact absurd hqf hq
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hj'len : j' < (X.tr g).length := by omega
        obtain ⟨f1, hf1⟩ : ∃ f1, X.get (g, j') = some f1 :=
          ⟨_, List.getElem?_eq_getElem hj'len⟩
        rcases Wg0.Control.w0_vec_pair hp hX hFw (noUbBefore_of_get hX hf) hw hf1 hf
          (sameAccess_adj hSA' (by omega) (by omega)) with ⟨k0, hk0, hpc, hpc'⟩ | ⟨-, hqf⟩
        · exact ⟨k0, hk0, by omega⟩
        · exact absurd hqf hq
    obtain ⟨k0, hk0, hpc⟩ := hcls
    exact w0Valid_snoc_peer hp hIn hX hFw hf (hnj f hf) hw hk0 hpc hk
      (fun q h1 h2 => sameAccess_acc hSA' (by omega) (by omega)) hWB hbc hv
  have hrun : W0Run P L X (g, k) := W0Run.of_step hX hk hpre hstep
  refine ⟨hrun, fun _ a bs hev => ?_⟩
  have hfe : e = ⟨572, .rd a bs⟩ := Option.some.inj (hwe.symm.trans hev)
  subst hfe
  have hv : W0Valid P.scale ((X.tr g).take k) := by
    rcases k with _ | j
    · simpa using w0Valid_nil P.scale
    · have hlen' : j < (X.tr g).length := by omega
      have hf1 : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hlen'
      exact hprev j rfl _ hf1 (fun hq => hq.pm rfl) (fun ⟨k0, hk0, h⟩ => by simp at h; omega)
  exact (w0Valid_snoc_pm hp hIn hX hFw hev hw hWB hv).2

/-- **Warpgroup 0's trace is valid at every event, with the facts of the Tensor Memory words.** -/
theorem Safe.w0Joint (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ∀ w e, X.get w = some e →
      W0Q P L X w ∧ TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w :=
  Safe.tmJoint hp hIn hX hFw (W0Q P L X) (fun _ _ h hw hn => h.1.valid hw hn)
    (Safe.w0Hq hp hIn hX hFw)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
