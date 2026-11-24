-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Protocol.HsRoute
public import Kernels.InklingRelDecode.Proof.Interface.SwStO
public import Kernels.InklingRelDecode.Proof.Interface.FrTcData
public import Kernels.InklingRelDecode.Proof.Interface.RdSmBack

@[expose] public section

/-!
# The coordinates of the softmax region's `tcgen05.st` stores (`Sr.Lane.st`)

A `tcgen05.st` of a thread of CTA `c` is the `P` store at `tmemSt` or the rescale store at `stO` of
a softmax state `d` (`tcst_event`). Its coordinate is the loop counter `d.i`, and:

* the gate's poll is the thread's successful poll of `s_ready (i % 2)` with `i / 2` earlier ones
  (of `o_done` with `i - 1` earlier ones): the counts of `Rd.sm_cnt` at the store and `nth_okPoll`;
* the event, the poll counts and the address are the store's (`tcst_event`, `Rd.sm_cnt`,
  `Sm.tileAddr_eq`, `Sm.oAddr_eq`, base column 0);
* a rescale store has `1 ≤ i`: it follows the iteration's `o_done` poll at `waitO`
  (`stO_pred`, `preLdO_back`, `Rd.sm_cnt`).

The one clause that is not proved here is the gate's rendezvous (`StRdv`): once thread 0 has made
more than `i / 2` arrivals on `p_ready (i % 2)`, the store's `tcgen05.wait::st` exists and is
base-causally before an event of thread 0 with at most `i / 2` earlier arrivals.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The rendezvous of the stores of CTA `c`** (`Sr.StGate.rendezvous` with the coordinate the
loop counter of the softmax state at the store). -/
def StRdv (Q : Params) (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∀ {t sk : Nat} {d : Sm.D}, t < L.threads → t / L.block = c →
    St Q L X t sk = some (some (.d (.sm d))) → (d.site = .tmemSt ∨ d.site = .stO) →
    sk < (X.tr t).length →
    d.i / 2 + 1 ≤ arrivals (pReady L c (d.i % 2)) (X.tr (p0Of L c)) →
      ∃ wk pcw e, sk < wk ∧ X.get (t, wk) = some ⟨pcw, .tc .waitSt⟩ ∧
        baseCausality L X (t, wk) (p0Of L c, e) ∧
        arrivals (pReady L c (d.i % 2)) ((X.tr (p0Of L c)).take e) ≤ d.i / 2

/-- **The `n`-th successful poll**: a thread with more than `n` successful polls of `m` among its
first `k` events has one with exactly `n` before it. -/
theorem nth_okPoll {g : Nat} {m : Loc} :
    ∀ (k n : Nat), n < okPolls m ((X.tr g).take k) →
      ∃ j < k, ∃ pc p acq sc, X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
        okPolls m ((X.tr g).take j) = n := by
  intro k
  induction k with
  | zero => intro n h; simp [okPolls] at h
  | succ k ih =>
    intro n h
    cases he : (X.tr g)[k]? with
    | none =>
      have hl : (X.tr g).length ≤ k := by
        rw [List.getElem?_eq_none_iff] at he
        exact he
      rw [List.take_of_length_le (by omega)] at h
      rw [← List.take_of_length_le (l := X.tr g) hl] at h
      obtain ⟨j, hj, rest⟩ := ih n h
      exact ⟨j, by omega, rest⟩
    | some e =>
      rw [Rd.okPolls_take_succ _ he] at h
      by_cases hn : n < okPolls m ((X.tr g).take k)
      · obtain ⟨j, hj, rest⟩ := ih n hn
        exact ⟨j, by omega, rest⟩
      · have hok : okPoll m e = true := by
          by_contra h'
          simp [h'] at h
          omega
        rw [hok] at h
        simp only [ite_true] at h
        obtain ⟨p, acq, sc, hev⟩ := okPoll_true hok
        refine ⟨k, by omega, e.pc, p, acq, sc, ?_, by omega⟩
        rw [← hev]
        exact he

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A rescale store is in an iteration `i ≥ 1`.** -/
theorem stO_one_le {g k : Nat} {d : Sm.D} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .stO) : 1 ≤ d.i := by
  obtain ⟨k0, d0, a, vals, sh, rfl, hσ0, hs0, -, rfl⟩ := Sv.stO_pred hk hσ hs
  obtain ⟨kp, dp, ep, hkp, -, hσp, hwp, hip, -, -⟩ :=
    preLdO_back k0 (by omega) hσ0 (by simp [PreLdO, hs0])
  have hc := (Rd.sm_cnt hpre hX hf hg kp (by omega) _ hσp).2 dp rfl
  have := hc.ok hwp
  simp only at hip ⊢
  omega

/-- **The `P` store's coordinates.** -/
theorem pst_of (hb : BaseWordRead L X) {c : Nat} (hr : StRdv Q L X c) {t sk pc a : Nat}
    {vals : List Value} {sh : TcShape} (he : X.get (t, sk) = some ⟨pc, .tc (.st a vals sh)⟩)
    (htc : t / L.block = c) {d : Sm.D} (hσ : St Q L X t sk = some (some (.d (.sm d))))
    (hs : d.site = .tmemSt) (ha : a = Sm.tileAddr L t d) (hsh : sh = .s16x32bx2 32)
    (hl : vals.length = 32) :
    Sr.PSt L X c (p0Of L c) (Sr.SoftOf L c) (tmOf c) t sk d.i a vals sh := by
  have ht : t < L.threads := event_thread_lt hX he
  have hk : sk < (X.tr t).length := len_of_get he
  have hdef : t % L.block < 128 := (hf.reach ht hσ).1
  have htm : d.e.tm = 0 := smBaseZero_of hpre hX hf hb ht hσ
  have hcnt := (Rd.sm_cnt hpre hX hf ht sk hk.le _ hσ).2 d rfl
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hpol : okPolls (sReady L c (d.i % 2)) ((X.tr t).take sk) = d.i / 2 + 1 := by
    rw [← htc, hcnt.s _ hb2]
    simp only [SO.smPolled, hs, below2]
    omega
  refine ⟨⟨⟨ht, htc, hdef⟩, ?_, ?_⟩, ⟨pc, he⟩, ?_, ?_⟩
  · obtain ⟨j, hj, pcj, p, acq, sc, hej, hcj⟩ :=
      nth_okPoll (X := X) (g := t) (m := sReady L c (d.i % 2)) sk (d.i / 2) (by omega)
    have hacq := poll_acq hpre hX hf hej
    subst hacq
    exact ⟨j, pcj, p, sc, hj, hej, hcj⟩
  · intro h
    exact hr ht htc hσ (.inl hs) hk h
  · intro b hb'
    rw [← htc, hcnt.s _ hb']
    simp [SO.smPolled, hs]
  · refine ⟨hsh, hl, t % L.block / 32, ?_⟩
    rw [ha, Sm.tileAddr_eq hdef (by omega) (sm_bw' hpre hX hf ht hσ (by rw [hs]; trivial)),
      htm]
    unfold tmOf
    omega

/-- **The rescale store's coordinates.** -/
theorem ost_of (hb : BaseWordRead L X) {c : Nat} (hr : StRdv Q L X c) {t sk pc a : Nat}
    {vals : List Value} {sh : TcShape} (he : X.get (t, sk) = some ⟨pc, .tc (.st a vals sh)⟩)
    (htc : t / L.block = c) {d : Sm.D} (hσ : St Q L X t sk = some (some (.d (.sm d))))
    (hs : d.site = .stO) (ha : a = Sm.oAddr L t d) (hsh : sh = .s16x32bx2 64)
    (hl : vals.length = 64) :
    Sr.OSt L X c (p0Of L c) (Sr.SoftOf L c) (tmOf c) t sk d.i a vals sh := by
  have ht : t < L.threads := event_thread_lt hX he
  have hk : sk < (X.tr t).length := len_of_get he
  have hdef : t % L.block < 128 := (hf.reach ht hσ).1
  have htm : d.e.tm = 0 := smBaseZero_of hpre hX hf hb ht hσ
  have hcnt := (Rd.sm_cnt hpre hX hf ht sk hk.le _ hσ).2 d rfl
  have h1 : 1 ≤ d.i := stO_one_le hpre hX hf ht hk.le hσ hs
  have hpol : okPolls (oDone L c) ((X.tr t).take sk) = d.i := by
    rw [← htc, hcnt.o]
    simp [SO.smOPolled, hs]
  refine ⟨⟨⟨ht, htc, hdef⟩, ?_, ?_⟩, h1, ⟨pc, he⟩, hpol, ?_⟩
  · obtain ⟨j, hj, pcj, p, acq, sc, hej, hcj⟩ :=
      nth_okPoll (X := X) (g := t) (m := oDone L c) sk (d.i - 1) (by omega)
    have hacq := poll_acq hpre hX hf hej
    subst hacq
    exact ⟨j, pcj, p, sc, hj, hej, hcj⟩
  · intro h
    exact hr ht htc hσ (.inr hs) hk h
  · refine ⟨hsh, hl, t % L.block / 32, ?_⟩
    rw [ha, Sm.oAddr_eq hdef (by omega) (sm_bw' hpre hX hf ht hσ (by rw [hs]; trivial)), htm]
    unfold tmOf
    omega

/-- **`Sr.Lane.st`** from the rendezvous of the stores. -/
theorem lane_st (hb : BaseWordRead L X) {c : Nat} (hr : StRdv Q L X c) {t sk a : Nat}
    {vals : List Value} {sh : TcShape} (he : X.TSt (t, sk) a vals sh) (htc : t / L.block = c) :
    (∃ i, Sr.PSt L X c (p0Of L c) (Sr.SoftOf L c) (tmOf c) t sk i a vals sh) ∨
      ∃ i, Sr.OSt L X c (p0Of L c) (Sr.SoftOf L c) (tmOf c) t sk i a vals sh := by
  obtain ⟨pc, hget⟩ := he
  have ht : t < L.threads := event_thread_lt hX hget
  obtain ⟨d, hσ, ⟨hs, ha, hsh, hl⟩ | ⟨hs, ha, hsh, hl⟩⟩ := Lk.tcst_event hX hf ht hget
  · exact .inl ⟨_, pst_of hpre hX hf hb hr hget htc hσ hs ha hsh hl⟩
  · exact .inr ⟨_, ost_of hpre hX hf hb hr hget htc hσ hs ha hsh hl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
