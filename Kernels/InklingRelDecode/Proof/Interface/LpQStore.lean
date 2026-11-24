-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LpQAddr
public import Kernels.InklingRelDecode.Proof.Interface.ScFence
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# The query stores of a thread, and their order before the MMA warp

* `bar1_of_exit`, `fnc1_of_bar`: a default-partition thread that exited has a first barrier-1
  event, and before it a prologue state at the fence `fnc1` (the `fence.proxy.async` after the
  query stores);
* `stq_chain`: the 32 events before that fence are the 32 query stores, at the store sites in
  order, with the fence state's data (`ProA.next_into_tail`);
* `qtile_writer`: the store of a byte of the query tile, before that fence;
* `stq_proxyBefore`: a query store of a thread is ordered before every event of a thread of its CTA
  that has made a barrier-1 event, through the fence: `ProxyBefore` (the store is before the fence
  by program order, the fence before the thread's first barrier-1 arrival, which synchronizes with
  the other thread's arrival of the same ordinal, `Bar.bar1_baseCausality`). For an MMA-warp event
  the barrier-1 event is the role's (`phase_inv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The state before a prologue state at a chain site** (a query store after the first, or the
fence `fnc1`) is the chain's previous site, with the same data, at the previous event. -/
theorem chain_pred {k : Nat} {d : ProA.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hs : d.site ∈ ProA.stqTail) :
    ∃ k0 dt0 i, k = k0 + 1 ∧ i < 32 ∧ d.site = ProA.chainSite (i + 1) ∧
      St Q L X g k0 = some (some (.d (.pro ⟨ProA.chainSite i, dt0⟩))) ∧ d.dt = dt0 := by
  rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, -, hσ0, hn⟩
  · exfalso
    have : (DComp.code L g Q).init = .dstart (DStart.D.start L g) := rfl
    rw [this] at h0
    cases h0
  · cases s0 with
    | dstart dd =>
      exfalso
      change DComp.dstartNext L g Q dd e = _ at hn
      unfold DComp.dstartNext at hn
      obtain ⟨d', -, hs'⟩ := map_map_eq_some_some hn
      split at hs'
      · cases hs'
        simp [ProA.D.start, ProA.stqTail] at hs
      · cases hs'
    | pro dp =>
      change DComp.proNext L g Q dp e = _ at hn
      unfold DComp.proNext at hn
      split at hn
      · split at hn <;> cases hn
      · obtain ⟨d3, hd3, h3⟩ := map_map_eq_some_some hn
        cases h3
        obtain ⟨site, dt0⟩ := dp
        obtain ⟨⟨i, hi, hs1, hs2⟩, hdt⟩ := ProA.next_into_tail hd3 hs
        subst hs1
        exact ⟨k0, dt0, i, rfl, hi, hs2, hσ0, hdt⟩
    | sm d0 =>
      exfalso
      change DComp.smNext L g d0 e = _ at hn
      unfold DComp.smNext at hn
      split at hn
      · unfold DComp.exitNext at hn
        split at hn <;> cases hn
      · obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
        cases ha
    | epi de =>
      exfalso
      change (Epi.next de e).map (Option.map DComp.St.epi) = _ at hn
      obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
      cases ha

/-- **The query stores before the fence.** A thread at `fnc1` at event `j` was at store site `i`
at event `j - 32 + i`, with the same data. -/
theorem stq_chain {j : Nat} {dt : ProA.Dat} (hj : j ≤ (X.tr g).length)
    (hσ : St Q L X g j = some (some (.d (.pro ⟨.fnc1, dt⟩)))) :
    32 ≤ j ∧ ∀ i < 32, St Q L X g (j - 32 + i) = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩))) := by
  have key : ∀ n, n ≤ 32 → n ≤ j ∧
      St Q L X g (j - n) = some (some (.d (.pro ⟨ProA.chainSite (32 - n), dt⟩))) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by omega, by simpa [ProA.chainSite_fnc1] using hσ⟩
    | succ n ih =>
      intro hn
      obtain ⟨hnj, hσn⟩ := ih (by omega)
      obtain ⟨k0, dt0, i, hk0, hi, hsi, hσ0, hdt⟩ := chain_pred (by omega) hσn
        (ProA.chainSite_tail (i := 31 - n) (by omega) |> fun h => by
          rw [show 31 - n + 1 = 32 - n by omega] at h; exact h)
      have hii : 32 - n = i + 1 := ProA.chainSite_inj (by omega) (by omega) hsi
      simp only at hdt
      subst hdt
      refine ⟨by omega, ?_⟩
      rw [show j - (n + 1) = k0 by omega, show 32 - (n + 1) = i by omega]
      exact hσ0
  refine ⟨(key 32 le_rfl).1, fun i hi => ?_⟩
  have h := (key (32 - i) (by omega)).2
  rw [show j - (32 - i) = j - 32 + i by have := (key 32 le_rfl).1; omega,
    show 32 - (32 - i) = i by omega, ProA.chainSite_stq hi] at h
  exact h

/-- Two barrier-1 events of a thread with no earlier barrier-1 event are one. -/
theorem bar1_first_unique {t a b pa pb : Nat} (ha : X.IsBarrier (t, a) 1 none pa)
    (hb : X.IsBarrier (t, b) 1 none pb)
    (hca : ((X.tr t).take a).countP (Execution.isBarId 1) = 0)
    (hcb : ((X.tr t).take b).countP (Execution.isBarId 1) = 0) : a = b := by
  have side : ∀ {a b pa pb : Nat}, X.IsBarrier (t, a) 1 none pa → a < b →
      ((X.tr t).take b).countP (Execution.isBarId 1) = 0 → False := by
    intro a b pa pb ha hlt hcb
    have hga : (X.tr t)[a]? = some ⟨pa, .bar 1 none .sync⟩ := ha
    have h1 : ((X.tr t).take (a + 1)).countP (Execution.isBarId 1) ≥ 1 := by
      rw [countP_take_succ _ hga, isBarId_bar]
      simp
    have h2 : ((X.tr t).take (a + 1)).countP (Execution.isBarId 1) ≤
        ((X.tr t).take b).countP (Execution.isBarId 1) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  rcases lt_trichotomy a b with h | h | h
  · exact (side (pb := pb) ha h hcb).elim
  · exact h
  · exact (side (pb := pa) hb h hca).elim

/-- **The first barrier-1 event of a default thread that exited.** -/
theorem bar1_of_exit (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hdef : g % L.block < 128)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) :
    ∃ i0 pc0, X.IsBarrier (g, i0) 1 none pc0 ∧
      ((X.tr g).take i0).countP (Execution.isBarId 1) = 0 := by
  obtain ⟨kx, pcx, hgetx, hx⟩ := Rr.exit_of_last hX hf hex
  have hkx : kx < (X.tr g).length := len_of_get hgetx
  obtain ⟨d, hσx, hdx⟩ : ∃ d : Epi.D, St Q L X g kx = some (some (.d (.epi d))) ∧
      d.site = .exit := by
    rcases hx with h | ⟨x, hσ, -⟩
    · exact h
    · exfalso
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hgetx hσ
      have : ¬ IsDefault L g := hinv.1
      exact this hdef
  obtain ⟨dd, hdd, hb⟩ := dphase_inv hpre hX hf.sound hdef kx _ hkx.le hσx
  cases hdd
  rw [d_exit_phase d hdx] at hb
  obtain ⟨i0, pc0, -, hbar, hc0⟩ := arrival1_before hpre hX (h := g) (k := kx) (r := 0)
    (by rw [hb]; omega)
  exact ⟨i0, pc0, hbar, hc0⟩

/-- **The fence `fnc1` before a default thread's first barrier-1 event.** -/
theorem fnc1_of_bar (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hg : g < L.threads) (hdef : g % L.block < 128) {i0 pc0 : Nat}
    (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) :
    ∃ (j1 : Nat) (dt : ProA.Dat), j1 < i0 ∧ i0 < (X.tr g).length ∧
      St Q L X g j1 = some (some (.d (.pro ⟨.fnc1, dt⟩))) ∧
      X.IsProxyFence (g, j1) (.async (some (.shared .cta))) none := by
  have hge : X.get (g, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hbar
  have hli : i0 < (X.tr g).length := len_of_get hge
  obtain ⟨s0, hσ0⟩ := Frame.event_state hf.sound hX hf.tracked hge (by intro pc f h; cases h)
  obtain ⟨d0, rfl, hb0⟩ := dphase_inv hpre hX hf.sound hdef i0 s0 hli.le hσ0
  have hb1 := event_b1 hpre hX hf.sound hge hσ0
  rw [isBarId_bar] at hb1
  have h0 : (dPh d0).2 = 0 := by rw [← hb0]; exact hc0
  obtain ⟨dp, rfl, hs⟩ := dB1_phase0 h0 hb1.symm
  obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_pastPro (X := X)
    (fun h' a b => ProA.next_cross_fnc1 h' a b) (by decide) (by decide) i0 _ hσ0
    (by show ProA.Site.fnc1.pc < dp.site.pc; rw [hs]; decide)
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, j1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (show j1 < (X.tr g).length by omega)⟩
  obtain ⟨pcf, hev⟩ := fnc_event hX hf.sound hT hg he1 hσ1 (Or.inr hs1)
  obtain ⟨site, dt⟩ := d1
  simp only at hs1
  subst hs1
  exact ⟨j1, dt, hj1, hli, hσ1, ⟨pcf, by rw [he1, hev]⟩⟩

/-- **A query store is ordered before every later-phase event of its CTA through the fence.** For
the store at event `k` of a default thread `g`, before its fence `fnc1` at `j1`, which is before its
first barrier-1 event at `i0`: every event `(h, n)` of a thread of the CTA that has made a barrier-1
event before it is `ProxyBefore` the store for every shared byte of the CTA. -/
theorem stq_proxyBefore (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hE : Bar1Exits L X) {k j1 i0 pc0 : Nat} (hg : g < L.threads)
    (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) (hj1 : j1 < i0) (hk : k < j1)
    (hfence : X.IsProxyFence (g, j1) (.async (some (.shared .cta))) none)
    {h n : Nat} (hh : h < L.threads) (hcta : h / L.block = g / L.block)
    (hn : n < (X.tr h).length) (hb1 : 1 ≤ b1N X h n) {l : Loc} (hls : l.space = .shared)
    (hlc : l.cta = g / L.block) : ProxyBefore L X (g, k) (h, n) l := by
  obtain ⟨jm, pcm, hjm, hfm, hcm⟩ := arrival1_before hpre hX (h := h) (k := n) (r := 0)
    (by omega)
  have hp : jm + 1 < (X.tr h).length := by omega
  obtain ⟨i, pc', hfi, hci⟩ := bar1_has hpre hX hE (g := g) (h := h) hfm hp hcta.symm
  have hi : i = i0 := bar1_first_unique hfi hbar (by rw [hci, hcm]) hc0
  subst hi
  have hgl : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp
    (show X.get (g, i) = some _ from hfi)).1
  obtain ⟨pcf, hpf⟩ := hfence
  refine ⟨(g, j1), _, _, ⟨pcf, hpf⟩, hg, ⟨hls, hlc⟩, ⟨hg, hh, by simp only; rw [hcta]⟩, ?_, ?_⟩
  · exact .single (.inl (po_of_not_access (X := X) rfl hk (by simp only; omega)
      (by rw [hpf]; rfl)))
  · exact Bar.bar1_baseCausality hpre hX ⟨hg, hh, hcta.symm⟩ hfi hfm hp
      (by rw [hci, hcm]) hj1 hjm hn

/-- **An MMA-warp event has made a barrier-1 event.** -/
theorem mma_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {h n : Nat} {dm : Mma.D}
    {P : Loader.Pro} (hn : n ≤ (X.tr h).length)
    (hσ : St Q L X h n = some (some (.w (.mma dm P)))) : 1 ≤ b1N X h n := by
  obtain ⟨-, t, -, h2, -⟩ := phase_inv hpre hX hf.sound hR n _ hn hσ
  rw [h2]
  have : 1 ≤ (tPh (.w (.mma dm P))).2 := by
    simp only [tPh]
    cases hs : dm.site <;> simp [wPh, hs]
  omega

/-- **The first barrier-1 event of a thread of a CTA one of whose MMA states has an event.** -/
theorem bar1_of_mma (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hE : Bar1Exits L X) {m : EvId}
    {dm : Mma.D} {P : Loader.Pro} (hn : m.2 < (X.tr m.1).length)
    (hm : St Q L X m.1 m.2 = some (some (.w (.mma dm P)))) {t : Nat}
    (hmc : t / L.block = m.1 / L.block) :
    ∃ i0 pc0, X.IsBarrier (t, i0) 1 none pc0 ∧
      ((X.tr t).take i0).countP (Execution.isBarId 1) = 0 := by
  have hb1 := mma_b1 hpre hX hf hR hn.le hm
  obtain ⟨jm, pcm, hjm, hfm, hcm⟩ := arrival1_before hpre hX (h := m.1) (k := m.2) (r := 0)
    (by omega)
  obtain ⟨i0, pc', hfi, hci⟩ := bar1_has hpre hX hE (g := t) (h := m.1) hfm (by omega) hmc
  exact ⟨i0, pc', hfi, by rw [hci, hcm]⟩

/-- **The writer of a byte of the query tile.** For a launched thread `g` and element `(r, d)`,
`d < 128`, of the query tile of its CTA, given the first barrier-1 event of the thread
`qThread r d` of the CTA: that thread writes bytes `z < 2` of the element with element
`qElemIdx d` of its store `qStore r d`. The write covers the byte, the byte written is byte
`2 (d % 2) + z` of the stored word `qWord dt (4 m + w)` of the data `dt` the thread has at its
fence `fnc1`, and the write is before the fence, which is before the barrier-1 event. -/
theorem qtile_writer (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hg : g < L.threads) {r d : Nat} (hd : d < 128) (hr : r < 64) {i0 pc0 : Nat}
    (hbar : X.IsBarrier (g / L.block * L.block + qThread r d, i0) 1 none pc0)
    (hc0 : ((X.tr (g / L.block * L.block + qThread r d)).take i0).countP (Execution.isBarId 1) = 0)
    : ∃ (k j1 pc : Nat) (dt : ProA.Dat) (a : Acc) (v : Value),
      X.get (g / L.block * L.block + qThread r d, k) = some ⟨pc, .wr a v.toBytes⟩ ∧
      (∀ z < 2, a.Covers ⟨.shared, g / L.block, Result.Mma.qAddr L.sharedBase r d z⟩ ∧
        wbyte a v.toBytes ⟨.shared, g / L.block, Result.Mma.qAddr L.sharedBase r d z⟩ =
          v.toBytes[2 * (d % 2) + z]?) ∧
      storeValue 32 (ProA.qWord dt (4 * qStore r d + qElemIdx d)) = .ok v ∧
      St Q L X (g / L.block * L.block + qThread r d) j1 =
        some (some (.d (.pro ⟨.fnc1, dt⟩))) ∧
      k < j1 ∧ j1 < i0 ∧
      X.IsProxyFence (g / L.block * L.block + qThread r d, j1) (.async (some (.shared .cta)))
        none ∧
      St Q L X (g / L.block * L.block + qThread r d) k =
        some (some (.d (.pro ⟨ProA.stqSite (4 * qStore r d + qElemIdx d), dt⟩))) := by
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hq := qThread_lt (r := r) (d := d)
  set t := g / L.block * L.block + qThread r d with ht
  have htl : t < L.threads := by rw [hth, hb] at hg ⊢; rw [hb] at ht; omega
  have htm : t % L.block = qThread r d := by rw [ht, hb]; omega
  have htc : t / L.block = g / L.block := by rw [ht, hb]; omega
  have hdef : t % L.block < 128 := by omega
  obtain ⟨j1, dt, hj1, hi0, hσ1, hfence⟩ := fnc1_of_bar hpre hX hf hT htl hdef hbar hc0
  obtain ⟨h32, hch⟩ := stq_chain (show j1 ≤ (X.tr t).length by omega) hσ1
  have hm := qStore_lt hr hd
  have hw := qElemIdx_lt (d := d)
  have hi : 4 * qStore r d + qElemIdx d < 32 := by omega
  have hσs := hch _ hi
  set k := j1 - 32 + (4 * qStore r d + qElemIdx d) with hk
  obtain ⟨e, he⟩ : ∃ e, X.get (t, k) = some e :=
    ⟨_, List.getElem?_eq_getElem (show k < (X.tr t).length by omega)⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf htl he hσs (by simp [ExitState])
  obtain ⟨v, hv, hev⟩ := ProA.shape_stq hm hw (fired_pro hF) rfl
  have hsb := sbRoom_of_pre hpre
  have hform := ProA.qStoreBase_form L t dt (by simp only [ProA.tidOf]; omega) hsb hm
  have htid : ProA.tidOf L t = qThread r d := htm
  rw [htid] at hform
  refine ⟨k, j1, _, dt, _, v, by rw [he, hev], fun z hz => ⟨?_, ?_⟩, hv, hσ1, by omega, hj1,
    hfence, hσs⟩
  all_goals have hqa := qAddr_form (sb := L.sharedBase) (r := r) hpre.sharedAlignment hd hz
  · refine ⟨rfl, htc.symm, ?_⟩
    simp only [EvD.wordAcc]
    rw [hqa, hform]
    omega
  · simp only [wbyte, EvD.wordAcc]
    rw [hqa, hform]
    congr 1
    omega

/-- An event with an MMA read is an event of the execution. -/
theorem mmaRead_get {m : EvId} {isB : Bool} {idx : Nat} {l : Loc} {b : Option Byte}
    (h : X.MmaRead m isB idx l b) : ∃ ev, X.get m = some ev := by
  rcases h.1 with ⟨d, s, acc, mask, ⟨pc, hm⟩, -⟩ | ⟨c, k, cta, ⟨pc, hm⟩, -⟩
  · exact ⟨_, hm⟩
  · exact ⟨_, hm⟩

/-- An MMA read covers its byte. -/
theorem mmaRead_covers {m : EvId} {isB : Bool} {idx : Nat} {l : Loc} {b : Option Byte}
    (h : X.MmaRead m isB idx l b) : AsyncCovers X m (.mmaRead isB idx) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, h.1⟩,
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩⟩

/-- **A query store is before every MMA read of its CTA's shared memory**, in the model's
causality: the read covers the byte, and the store is `ProxyBefore` the MMA's issue
(`stq_proxyBefore`, the MMA warp's barrier-1 event `mma_b1`). -/
theorem stq_before_mmaRead (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hE : Bar1Exits L X)
    {k j1 i0 pc0 : Nat} (hg : g < L.threads) (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) (hj1 : j1 < i0) (hk : k < j1)
    (hfence : X.IsProxyFence (g, j1) (.async (some (.shared .cta))) none)
    {m : EvId} {dm : Mma.D} {P : Loader.Pro} {isB : Bool} {idx : Nat} {l : Loc}
    {obs : Option Byte} (hm : St Q L X m.1 m.2 = some (some (.w (.mma dm P))))
    (hmc : m.1 / L.block = g / L.block) (hread : X.MmaRead m isB idx l obs)
    (hls : l.space = .shared) (hlc : l.cta = g / L.block) :
    modelCausality L X l (.thread (g, k)) (.async m (.mmaRead isB idx)) := by
  obtain ⟨ev, hev⟩ := mmaRead_get hread
  have hml : m.1 < L.threads := Frame.lt_of_get hX hev
  have hn : m.2 < (X.tr m.1).length := (List.getElem?_eq_some_iff.mp hev).1
  refine ⟨mmaRead_covers hread, .inl ?_⟩
  exact stq_proxyBefore hpre hX hE hg hbar hc0 hj1 hk hfence hml hmc hn
    (mma_b1 hpre hX hf hR hn.le hm) hls hlc

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
