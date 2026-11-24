-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LpQVal
public import Kernels.InklingRelDecode.Proof.Interface.FootSrc
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Result.MmaQStore
public import Kernels.InklingRelDecode.Proof2.Lib.QTile

@[expose] public section

/-!
# `QTile`: the query tile

`qTile_of : Result.Mma.QTile Q L X` for a complete consistent execution:

* the writer of byte `(r, d, z)` is the store `qtile_writer` names, and the byte it writes is
  byte `z` of the bf16 element `qElem`: the stored word packs the values loads `2 i` and `2 i + 1`
  stored (`q_at_fnc1`, their guards hold for a row of a valid token below row 60,
  `ldq_guard_of_valid`), which are the elements of the row and the columns `d - d % 2` and
  `d - d % 2 + 1` (`qVal_eq`), and `Result.Mma.qstore_value` gives the byte;
* the write is before every QK MMA read of the byte (`stq_before_mmaRead`);
* every write covering the byte is this write (`qtile_other`): a thread write of shared memory is
  one of the kernel's store sites (`source_class`), only a query store reaches the query tile, the
  address of a query store determines the thread, the store and the element (`qOff_inj`), and a
  thread is at a store site at one event only (`stq_unique`: its state there is `36 - i` events
  before the thread's first barrier-1 event, at `bar18`: `lt_bar`, `eq_bar`, `stq_bar`); a tensor
  load writes below `sharedBase + 196608`.

The writer, its uniqueness and the order take the writer thread's first barrier-1 event; here it
comes from the thread's exit (`bar1_of_exit`), elsewhere from an MMA of the CTA (`bar1_of_mma`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-! ### A thread is at a store site at one event -/

omit hpre hX hf in
/-- A state at `St` past the end of the trace is the state at the end. -/
theorem st_min {q : Nat} {s : Option TSt} (h : St Q L X g q = some s) :
    St Q L X g (min q (X.tr g).length) = some s := by
  rcases le_total q (X.tr g).length with hq | hq
  · rwa [Nat.min_eq_left hq]
  · rw [Nat.min_eq_right hq]
    exact (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := q) hq).symm.trans h

/-- **A prologue state of a default thread other than `bar18` is before its first barrier-1
event.** -/
theorem lt_bar (hdef : g % L.block < 128) {i0 pc0 : Nat} (hbar : X.IsBarrier (g, i0) 1 none pc0)
    {q : Nat} {d : ProA.D} (hσ : St Q L X g q = some (some (.d (.pro d)))) (hs : d.site ≠ .bar18)
    : q < i0 := by
  have hge : X.get (g, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hbar
  have hli : i0 < (X.tr g).length := len_of_get hge
  have hσ' := st_min hσ
  obtain ⟨dd, hdd, hb⟩ := dphase_inv hpre hX hf.sound hdef _ _ (Nat.min_le_right _ _) hσ'
  cases hdd
  have hz : (dPh (.pro d)).2 = 0 := by
    obtain ⟨site, dt⟩ := d
    cases site <;> rfl
  rw [hz] at hb
  have hle : min q (X.tr g).length ≤ i0 := by
    by_contra hlt
    have h1 : ((X.tr g).take (i0 + 1)).countP (Execution.isBarId 1) ≥ 1 := by
      rw [countP_take_succ _ hge]
      simp [isBarId_bar]
    have h2 : ((X.tr g).take (i0 + 1)).countP (Execution.isBarId 1) ≤
        b1N X g (min q (X.tr g).length) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have : min q (X.tr g).length < (X.tr g).length := by omega
    omega
  · exfalso
    rw [heq] at hσ'
    have hb1 := event_b1 hpre hX hf.sound hge hσ'
    rw [isBarId_bar] at hb1
    obtain ⟨site, dt⟩ := d
    cases site <;> first | exact hs rfl | simp [tB1, dB1, proB1] at hb1

/-- **A default thread's prologue state at `bar18` is at its first barrier-1 event.** -/
theorem eq_bar (hdef : g % L.block < 128) {i0 pc0 : Nat} (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) {q : Nat} {dt : ProA.Dat}
    (hσ : St Q L X g q = some (some (.d (.pro ⟨.bar18, dt⟩)))) : q = i0 := by
  have hge : X.get (g, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hbar
  have hli : i0 < (X.tr g).length := len_of_get hge
  have hσ' := st_min hσ
  obtain ⟨dd, hdd, hb⟩ := dphase_inv hpre hX hf.sound hdef _ _ (Nat.min_le_right _ _) hσ'
  cases hdd
  have hz : (dPh (.pro ⟨.bar18, dt⟩)).2 = 0 := rfl
  rw [hz] at hb
  have hle : min q (X.tr g).length ≤ i0 := by
    by_contra hlt
    have h1 : ((X.tr g).take (i0 + 1)).countP (Execution.isBarId 1) ≥ 1 := by
      rw [countP_take_succ _ hge]
      simp [isBarId_bar]
    have h2 : ((X.tr g).take (i0 + 1)).countP (Execution.isBarId 1) ≤
        b1N X g (min q (X.tr g).length) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exfalso
    set p := min q (X.tr g).length with hp
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[p]? = some e :=
      ⟨_, List.getElem?_eq_getElem (show p < (X.tr g).length by omega)⟩
    have hb1 := event_b1 hpre hX hf.sound (show X.get (g, p) = some e from he) hσ'
    have h1 : ((X.tr g).take (p + 1)).countP (Execution.isBarId 1) ≥ 1 := by
      rw [countP_take_succ _ he, hb1]
      simp [tB1, dB1, proB1]
    have h2 : ((X.tr g).take (p + 1)).countP (Execution.isBarId 1) ≤
        ((X.tr g).take i0).countP (Execution.isBarId 1) :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  · have : min q (X.tr g).length < (X.tr g).length := by omega
    omega

omit hpre hX hf in
/-- A prologue state with an event steps to the machine's successor. -/
theorem pro_step {k : Nat} {d d' : ProA.D} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hb : d.site ≠ .bar18)
    (hn : ∀ e, ProA.next L g d e = some (some d')) :
    St Q L X g (k + 1) = some (some (.d (.pro d'))) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  show Frame.stateAt (code L Q) X g (k + 1) = _
  rw [Frame.stateAt_succ he, show Frame.stateAt (code L Q) X g k = _ from hσ]
  show (threadCode L g Q).next (.d (.pro d)) e = _
  rw [next_d]
  show (DComp.proNext L g Q d e).map (Option.map TSt.d) = _
  unfold DComp.proNext
  simp only [hb, ↓reduceIte, hn e]
  rfl

/-- **A state at store site `i` is `36 - i` events before the first barrier-1 event.** -/
theorem stq_bar (hdef : g % L.block < 128) {i0 pc0 : Nat} (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) {k i : Nat} {dt : ProA.Dat}
    (hi : i < 32) (hσ : St Q L X g k = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩)))) :
    k + (36 - i) = i0 := by
  have hli : i0 < (X.tr g).length := len_of_get (show X.get (g, i0) = _ from hbar)
  have step : ∀ {q : Nat} {d d' : ProA.D}, St Q L X g q = some (some (.d (.pro d))) →
      d.site ≠ .bar18 → (∀ e, ProA.next L g d e = some (some d')) →
      St Q L X g (q + 1) = some (some (.d (.pro d'))) := by
    intro q d d' h hb hn
    exact pro_step (by have := lt_bar hpre hX hf hdef hbar h hb; omega) h hb hn
  have chain : ∀ n, n ≤ 32 - i →
      St Q L X g (k + n) = some (some (.d (.pro ⟨ProA.chainSite (i + n), dt⟩))) := by
    intro n
    induction n with
    | zero => intro _; simpa [ProA.chainSite_stq hi] using hσ
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have hst : ProA.chainSite (i + n) = ProA.stqSite (i + n) :=
        ProA.chainSite_stq (by omega)
      rw [hst] at h1
      have := step h1 (by
        have key : ∀ j < 32, ProA.stqSite j ≠ .bar18 := by decide
        exact key _ (by omega)) (fun e => ProA.next_stq_fwd (by omega) dt e)
      rw [show k + (n + 1) = k + n + 1 by omega, show i + (n + 1) = i + n + 1 by omega]
      exact this
  have h32 := chain (32 - i) le_rfl
  rw [show i + (32 - i) = 32 by omega, ProA.chainSite_fnc1] at h32
  have h1 := step h32 (by intro h; cases h) (ProA.next_fnc1_fwd dt)
  have h2 := step h1 (by intro h; cases h) (ProA.next_st8_fwd dt)
  have h3 := step h2 (by intro h; cases h) (ProA.next_st90_fwd dt)
  have h4 := step h3 (by intro h; cases h) (ProA.next_st91_fwd dt)
  have := eq_bar hpre hX hf hdef hbar hc0 h4
  omega

/-- **A thread is at a store site at one event**, given its first barrier-1 event. -/
theorem stq_unique (hdef : g % L.block < 128) {i0 pc0 : Nat} (hbar : X.IsBarrier (g, i0) 1 none pc0)
    (hc0 : ((X.tr g).take i0).countP (Execution.isBarId 1) = 0) {k k' i : Nat} {dt dt' : ProA.Dat}
    (hi : i < 32) (hσ : St Q L X g k = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩))))
    (hσ' : St Q L X g k' = some (some (.d (.pro ⟨ProA.stqSite i, dt'⟩)))) : k = k' := by
  have := stq_bar hpre hX hf hdef hbar hc0 hi hσ
  have := stq_bar hpre hX hf hdef hbar hc0 hi hσ'
  omega

/-! ### The other writers of a byte of the query tile -/

omit hpre hX hf in
/-- The address of a byte of the query tile is inside the tile. -/
theorem qAddr_range {sb r d z : Nat} (hsb : sb % 1024 = 0) (hd : d < 128) (hz : z < 2)
    (hr : r < 64) :
    sb + 196608 ≤ Result.Mma.qAddr sb r d z ∧ Result.Mma.qAddr sb r d z < sb + 212992 := by
  rw [qAddr_form hsb hd hz]
  have h1 := ProA.qGroup_lt _ (qStore_lt hr hd)
  have h2 := ProA.qSwz_spec _ (qThread_lt (r := r) (d := d))
  have h3 := qElemIdx_lt (d := d)
  omega

/-- **Every write covering a byte of the query tile is the store of its writer.** -/
theorem qtile_other {r d z k : Nat} (hd : d < 128) (hz : z < 2) (hr : r < 64) {dt : ProA.Dat}
    {i0 pc0 : Nat} (hbar : X.IsBarrier (g / L.block * L.block + qThread r d, i0) 1 none pc0)
    (hc0 : ((X.tr (g / L.block * L.block + qThread r d)).take i0).countP (Execution.isBarId 1) = 0)
    (hσk : St Q L X (g / L.block * L.block + qThread r d) k =
      some (some (.d (.pro ⟨ProA.stqSite (4 * qStore r d + qElemIdx d), dt⟩))))
    {other : AsyncCopy.Ref} {fp : Acc} {bytes : List Byte} (hw : X.MemWrites other fp bytes)
    (hcov : fp.Covers ⟨.shared, g / L.block, Result.Mma.qAddr L.sharedBase r d z⟩) :
    other = .thread (g / L.block * L.block + qThread r d, k) := by
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hsb := sbRoom_of_pre hpre
  unfold ProA.SbRoom at hsb
  obtain ⟨qlo, qhi⟩ := qAddr_range (r := r) hpre.sharedAlignment hd hz hr
  obtain ⟨ev, hev⟩ := write_present hX hw
  have hlt : (refEvent other).1 < L.threads := Frame.lt_of_get hX hev
  have hTT : TT Q L X (refEvent other) := hf.tracked _ _ hlt
  have hsp : fp.loc.space = .shared := hcov.1.symm
  obtain ⟨-, hcc, hlo, hhi⟩ := hcov
  simp only at hcc hlo hhi
  rcases source_class hpre hX hf.sound hw hsp hTT with
    ⟨g', k', s', rfl, hg', hσ', hTW⟩ | ⟨i, -, -, h12⟩
  · cases hTW with
    | stq hi hs hl hz' h1 h2 =>
      rename_i d' i' x
      obtain ⟨pc, hget⟩ : ∃ pc, X.get (g', k') = some ⟨pc, .wr fp bytes⟩ := by
        rcases hw with ⟨pc, hget⟩ | ⟨old, pc, hget⟩
        · exact ⟨pc, hget⟩
        · exact absurd hget (no_rmw hX)
      have hdef : g' % L.block < 128 := by
        obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hget hσ'
        exact hinv.1
      obtain ⟨u, hF⟩ := fired_cont hX hf hg' hget hσ' (by simp [ExitState])
      have hm' : i' / 4 < 8 := by omega
      have hw' : i' % 4 < 4 := by omega
      obtain ⟨v', -, hev'⟩ := ProA.shape_stq hm' hw' (fired_pro hF)
        (by rw [hs]; congr 1; omega)
      simp only [Event.mk.injEq, Kind.wr.injEq] at hev'
      obtain ⟨-, hfp, -⟩ := hev'
      rw [hfp] at hlo hhi hcc
      simp only [EvD.wordAcc] at hlo hhi hcc
      have hform := ProA.qStoreBase_form L g' d'.dt hdef hsb hm'
      rw [hform] at hlo hhi
      rw [qAddr_form hpre.sharedAlignment hd hz] at hlo hhi
      have hlt' : ProA.tidOf L g' < 128 := hdef
      have hqa := qAddr_form (sb := L.sharedBase) (r := r) hpre.sharedAlignment hd hz
      obtain ⟨ht1, hm1, hw1⟩ := qOff_inj (m := i' / 4) (t := ProA.tidOf L g') (w := i' % 4)
        (b := Result.Mma.qAddr L.sharedBase r d z - (L.sharedBase + 196608 +
          2048 * ProA.qGroup (i' / 4) + ProA.qSwz (ProA.tidOf L g') + 4 * (i' % 4)))
        (m' := qStore r d) (t' := qThread r d) (w' := qElemIdx d) (b' := 2 * (d % 2) + z)
        hm' (qStore_lt hr hd) hlt' (qThread_lt (r := r) (d := d)) hw' (qElemIdx_lt (d := d))
        (by omega) (by omega) (by omega)
      have hgg : g' = g / L.block * L.block + qThread r d := by
        have h1 := Nat.div_add_mod g' L.block
        have h2 : ProA.tidOf L g' = g' % L.block := rfl
        rw [hb] at h1 h2 hcc ⊢
        omega
      have hii : i' = 4 * qStore r d + qElemIdx d := by omega
      subst hgg hii
      obtain ⟨site, dt'⟩ := d'
      simp only at hs
      subst hs
      have := stq_unique hpre hX hf hdef hbar hc0 hi hσ' hσk
      rw [this]
    | st8 hs ha hb' =>
      rw [ha] at hlo hhi; simp only [EvD.wordAcc] at hlo hhi
      rw [Nat.mod_eq_of_lt (by omega)] at hlo; omega
    | st9_0 hs ha hb' =>
      rw [ha] at hlo hhi; simp only [EvD.wordAcc] at hlo hhi
      rw [Nat.mod_eq_of_lt (by omega)] at hlo; omega
    | st9_1 hs ha hb' =>
      rw [ha] at hlo hhi; simp only [EvD.wordAcc] at hlo hhi
      rw [Nat.mod_eq_of_lt (by omega)] at hlo; omega
    | store10 hs ha =>
      rw [ha] at hlo hhi; simp only [EvD.wordAcc] at hlo hhi; omega
    | allocWr hs ha hb' =>
      rw [ha] at hlo hhi; simp only at hlo hhi; omega
    | stTab hs ha hb' =>
      rw [ha] at hlo hhi; simp only [EvD.wordAcc] at hlo hhi
      rw [Nat.mod_eq_of_lt (by omega)] at hlo; omega
  · have hsr0 := hpre.sharedRange
    unfold sharedBytes at hsr0
    rcases h12 with h12 | h12 <;> omega

end

/-! ### The bytes and the assembly -/

/-- The element loads `2 i + b` of the writer of byte `(r, d)` reads is the tile's element, for the
`b` of the column's parity. -/
theorem qVal_eq {t r d : Nat} (hd : d < 128) (htid : ProA.tidOf L t = qThread r d)
    (hcz : ProA.cta L t .z = ProA.cta L g .z) (hcy : ProA.cta L t .y = ProA.cta L g .y) :
    qVal Q L t (2 * (4 * qStore r d + qElemIdx d) + d % 2) =
      Value.float .bf16 (Result.Mma.qElem Q L g r d) := by
  unfold qVal Result.Mma.qElem Result.Mma.reqOf Result.Mma.kvhOf
  rw [htid, hcz, hcy]
  have e1 : qThread r d / 8 % 16 + 16 * ((2 * (4 * qStore r d + qElemIdx d) + d % 2) / 16) = r := by
    unfold qThread qStore qElemIdx; omega
  have e2 : 8 * (qThread r d % 8) + 64 * ((2 * (4 * qStore r d + qElemIdx d) + d % 2) % 16 / 8) +
      (2 * (4 * qStore r d + qElemIdx d) + d % 2) % 8 = d := by
    unfold qThread qStore qElemIdx; omega
  rw [e1, e2, show group = 6 from rfl, Nat.mul_comm 6]

/-- **The query tile** (`Result.Mma.QTile`), for a complete consistent execution. -/
theorem qTile_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hc : Complete L X) : Result.Mma.QTile Q L X := by
  refine ⟨fun {g r d z} hg hrv hd hz => ?_⟩
  obtain ⟨h60, htok⟩ := hrv
  have hr : r < 64 := by omega
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  set t := g / L.block * L.block + qThread r d with ht
  have hq := qThread_lt (r := r) (d := d)
  have htl : t < L.threads := by rw [hth, hb] at hg ⊢; rw [hb] at ht; omega
  obtain ⟨i0, pc0, hbar, hc0⟩ := bar1_of_exit hpre hX hf (g := t) (by rw [ht, hb]; omega)
    (by rcases hc.1 t htl with hcan | hl
        · exact absurd hcan (no_canceled hX t htl)
        · exact hl)
  obtain ⟨k, j1, pc, dt, a, v, hget, hcz, hv, hσ1, hkj, hj1, hfence, hσk⟩ :=
    qtile_writer hpre hX hf hT hg hd hr hbar hc0
  obtain ⟨hcov, hwb⟩ := hcz z hz
  have htc : t / L.block = g / L.block := by rw [ht, hb]; omega
  have htid : ProA.tidOf L t = qThread r d := by
    show t % L.block = _; rw [ht, hb]; omega
  have hcz : ProA.cta L t .z = ProA.cta L g .z := by unfold ProA.cta; rw [htc]
  have hcy : ProA.cta L t .y = ProA.cta L g .y := by unfold ProA.cta; rw [htc]
  have hdef : t % L.block < 128 := by rw [show t % L.block = ProA.tidOf L t from rfl, htid]; omega
  -- the loaded values at the fence
  have hj1l : j1 < (X.tr t).length := by
    have := (List.getElem?_eq_some_iff.mp (show X.get (t, i0) = some _ from hbar)).1
    simp only at this
    omega
  obtain ⟨hw0, hw1, hw2⟩ := Mbar.wordsSo_all hpre hX hf j1 _ hσ1
  have hm : ProA.WordsMatch Q (ProA.cta L t .z) dt :=
    ⟨hw0 (by intro h; cases h) (by intro h; cases h), hw1 (.inl rfl), hw2 rfl⟩
  obtain ⟨-, -, hzb⟩ := ProA.cta_lt hpre htl
  have hBnd := ProA.bnd_of_pre hpre hzb hm
  have hql : dt.cu1 - dt.cu0 = Q.qLen (ProA.cta L t .z) := by
    simp [Params.qLen, hm.cu0, hm.cu1]
  have hguard : ∀ e < 2, ProA.guardVal L t dt
      (ProA.ldqSite (2 * (4 * qStore r d + qElemIdx d) + e)) = true := by
    intro e he
    have hk : 2 * (4 * qStore r d + qElemIdx d) + e < 64 := by
      have := qStore_lt hr hd; have := qElemIdx_lt (d := d); omega
    refine ProA.ldq_guard_of_valid L t dt hBnd (by rw [htid]; exact hq) hk ?_ ?_
    · rw [htid, hql, hcz]
      have : qThread r d / 8 % 16 + 16 * ((2 * (4 * qStore r d + qElemIdx d) + e) / 16) = r := by
        unfold qThread qStore qElemIdx; omega
      rw [this]; exact htok
    · rw [htid]
      have : qThread r d / 8 % 16 + 16 * ((2 * (4 * qStore r d + qElemIdx d) + e) / 16) = r := by
        unfold qThread qStore qElemIdx; omega
      rw [this]; exact h60
  have hqv : ∀ e < 2, dt.q (2 * (4 * qStore r d + qElemIdx d) + e) =
      qVal Q L t (2 * (4 * qStore r d + qElemIdx d) + e) := by
    intro e he
    exact q_at_fnc1 hpre hX hf htl hj1l.le hσ1 _ (by
      have := qStore_lt hr hd; have := qElemIdx_lt (d := d); omega) (hguard e he)
  -- the byte
  have hx := hqv 0 (by omega)
  have hy := hqv 1 (by omega)
  simp only [Nat.add_zero] at hx
  unfold qVal at hx hy
  obtain ⟨hb0, hb1⟩ := Result.Mma.qstore_value hx hy hv hz
  have hbyte : wbyte a v.toBytes ⟨.shared, g / L.block, Result.Mma.qAddr L.sharedBase r d z⟩ =
      some ((Value.float .bf16 (Result.Mma.qElem Q L g r d)).byteAt z) := by
    rw [hwb]
    have he := qVal_eq (Q := Q) (g := g) (t := t) hd htid hcz hcy
    unfold qVal at he
    rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · rw [h2, Nat.add_zero] at he
      simp only [Value.float.injEq, true_and] at he
      rw [h2, Nat.mul_zero, Nat.zero_add, hb0, he]
    · rw [h2] at he
      simp only [Value.float.injEq, true_and] at he
      rw [h2, Nat.mul_one, hb1, he]
  refine ⟨(t, k), a, v.toBytes, ⟨pc, hget⟩, hcov, hbyte, ?_⟩
  intro m dm idx obs hm hqk hmc hread
  obtain ⟨P, hσm⟩ := hm
  refine ⟨stq_before_mmaRead hpre hX hf hR hE htl hbar hc0 hj1 hkj hfence hσm
    (by rw [hmc, htc]) hread rfl (by simp only; exact htc.symm), ?_⟩
  intro other fp bytes hw hcv
  left
  rw [qtile_other hpre hX hf hd hz hr hbar hc0 hσk hw hcv]

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
