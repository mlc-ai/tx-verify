-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkSource
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Lemmas.Tcgen05.TcProgramOrder
import Lemmas.Tcgen05.TcMmaSource
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The source of a PV step's accumulator

The PV steps of a lane are in program order by their key `8 b + j` (ordinal `b`, step `j`): one
issue per key (`pv_once`). The accumulator read of the step with key `n + 1` has the step with key
`n` before it, and its source is that step, or the rescale store of the round before its block when
that store writes the cell (the step `0` of an ordinal at least `2`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- Lane `g` issued PV step `j` at its position `k`. -/
def PvAt (X : Execution) (g k : Nat) (j : Fin 8) : Prop :=
  ∃ d s acc mask, X.get (g, k) = some ⟨Lib.pvIssue j, .tc (.mma d s acc mask)⟩

/-- The key of a PV step: its ordinal and its index. -/
def pvKey (X : Execution) (g k : Nat) (j : Fin 8) : Nat :=
  8 * pollRound 2510 ((X.tr g).take k) + j.val

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV step is issued once per ordinal.** -/
theorem pv_unique (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) {g k1 k2 : Nat} {j : Fin 8}
    (h1 : PvAt X g k1 j) (h2 : PvAt X g k2 j)
    (hr : pollRound 2510 ((X.tr g).take k1) = pollRound 2510 ((X.tr g).take k2)) : k1 = k2 := by
  obtain ⟨_, _, _, _, e1⟩ := h1
  obtain ⟨_, _, _, _, e2⟩ := h2
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := Mma.Export.pv_once hp hX hf words e1 e2 rfl h
    omega
  · exact h
  · have := Mma.Export.pv_once hp hX hf words e2 e1 rfl h
    omega

/-- **The PV steps of a lane are in program order of their keys.** -/
theorem pv_key_lt (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X) {g k k' : Nat}
    {j j' : Fin 8} (h : PvAt X g k j) (h' : PvAt X g k' j')
    (lt : pvKey X g k' j' < pvKey X g k j) : k' < k := by
  by_contra not
  have mono : pollRound 2510 ((X.tr g).take k) ≤ pollRound 2510 ((X.tr g).take k') :=
    (List.take_sublist_take_left (Nat.le_of_not_lt not)).countP_le (p := okPollAt 2510)
  obtain ⟨d, s, a, mk, e⟩ := h
  have j8 := j.isLt
  have j8' := j'.isLt
  unfold pvKey at lt
  obtain ⟨-, -, prior, -⟩ := Mma.Export.pv_prior hp hX hf words hu e rfl
  have hb : pollRound 2510 ((X.tr g).take k') = pollRound 2510 ((X.tr g).take k) := by omega
  have hj : j'.val < j.val := by omega
  obtain ⟨kR, ltk, d2, s2, a2, m2, g2, q2⟩ := prior j' hj
  have := pv_unique hp hX hf words ⟨d2, s2, a2, m2, g2⟩ h' (by omega)
  omega

/-- **Of the PV steps writing a cell, none lies between two adjacent keys**: the step before a
step is the only write of the lane between its two neighbours' sources. -/
theorem pv_between (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X) {g kc kp ks : Nat}
    {jc jp js : Fin 8} (hc : PvAt X g kc jc) (hp' : PvAt X g kp jp) (hs : PvAt X g ks js)
    (key : pvKey X g kc jc + 1 = pvKey X g kp jp) (l1 : kc ≤ ks) (l2 : ks < kp) : ks = kc := by
  have a1 : ¬ pvKey X g ks js < pvKey X g kc jc := fun h =>
    absurd (pv_key_lt hp hX hf words hu hc hs h) (by omega)
  have a2 : ¬ pvKey X g kp jp < pvKey X g ks js := fun h =>
    absurd (pv_key_lt hp hX hf words hu hs hp' h) (by omega)
  have a3 : pvKey X g ks js ≠ pvKey X g kp jp := fun h => by
    unfold pvKey at h
    have jj : js = jp := Fin.ext (by have := js.isLt; have := jp.isLt; omega)
    subst jj
    have := pv_unique hp hX hf words hs hp' (by omega)
    omega
  have eq : pvKey X g ks js = pvKey X g kc jc := by omega
  unfold pvKey at eq
  have jj : js = jc := Fin.ext (by have := js.isLt; have := jc.isLt; omega)
  subst jj
  exact pv_unique hp hX hf words hs hc (by omega)

/-- The rescale store `st` of round `r` writes `cell`. -/
def RescaleAt (L : Launch) (X : Execution) (st : EvId) (r : Nat) (cell : Cell) : Prop :=
  ∃ a vals sh jj, X.get st = some ⟨2328, .tc (.st a vals sh)⟩ ∧ jj < vals.length ∧
    cell = tcDataCell L st.1 sh a jj ∧ pollRound 1257 ((X.tr st.1).take st.2) = r + 1

private theorem pv_ne_qk : ∀ j j' : Fin 8, Lib.pvIssue j ≠ Lib.qkIssue j' := by decide +kernel

/-- A PV issue writes the accumulator at column 256 with the PV descriptor. -/
theorem pv_cols (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {g k d s acc mask} {j : Fin 8}
    (he : X.get (g, k) = some ⟨Lib.pvIssue j, .tc (.mma d s acc mask)⟩) :
    d = 256 ∧ s.descriptor = Lib.pvDesc := by
  obtain ⟨_, _, _, _, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j', hpc, -⟩ := qk
    exact absurd hpc (pv_ne_qk j j')
  · obtain ⟨j', -, hd, -, hD⟩ := pv
    exact ⟨hd, hD⟩

/-- A rescale store writes the cells of its own CTA. -/
theorem rescale_cta (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {st : EvId} {r : Nat} {cell : Cell}
    (h : RescaleAt L X st r cell) : cell.cta = st.1 / L.block := by
  obtain ⟨a, vals, sh, jj, hy, hj, hc, -⟩ := h
  obtain ⟨-, -, k1 | k2⟩ := st_write_cell hp hX hf base (x := st) (cell := cell)
    ⟨a, vals, sh, jj, ⟨2328, hy⟩, hj, hc⟩
  · obtain ⟨a1, v1, ba, w, j1, g1, -⟩ := k1
    rw [hy] at g1
    simp at g1
  · obtain ⟨a2, v2, w, j2, g2, ha, hj2, hc2⟩ := k2
    have := (o_cols (L := L) (g := st.1) (w := w) hj2).2.2
    rw [← ha] at this
    rw [hc2]
    exact this

/-- **The source of a PV step's accumulator read**: a step `j > 0` has the step `j - 1` of its
ordinal; step `0` of an ordinal `b ≥ 2` has the last step of ordinal `b - 1` (when no rescale store
of round `b - 1` writes the cell) or that rescale store. -/
theorem pv_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hG : SyncGuarded L kernel X)
    (tie : RescaleLd X) {g kp : Nat} {cell : Cell} {src : EvId} {d s mask} {j : Fin 8}
    (he : X.get (g, kp) = some ⟨Lib.pvIssue j, .tc (.mma d s true mask)⟩)
    (hrd : X.MmaReadCell (g, kp) cell) (hs : ReadSource L X .acc src (g, kp) cell) :
    (0 < j.val → ∃ kR j', j'.val + 1 = j.val ∧ src = (g, kR) ∧ PvAt X g kR j' ∧
      pollRound 2510 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take kp)) ∧
    (j.val = 0 → 2 ≤ pollRound 2510 ((X.tr g).take kp) ∧
      ((∃ kR, src = (g, kR) ∧ PvAt X g kR 7 ∧
        pollRound 2510 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take kp) - 1 ∧
        ∀ st, ¬ RescaleAt L X st (pollRound 2510 ((X.tr g).take kp) - 1) cell) ∨
      RescaleAt L X src (pollRound 2510 ((X.tr g).take kp) - 1) cell)) := by
  have words : RoleBytes L X := fun h => Shared.role_bytes hp hX h
  obtain ⟨b, hd256, pb, hb1, -, -, warp, hacc⟩ := Mma.Export.pv_block hp hX hf base he ⟨j, rfl⟩
  obtain ⟨-, -, prior, last⟩ := Mma.Export.pv_prior hp hX hf words hu he rfl
  have cyc : ∀ {x y : EvId}, Relation.TransGen (TcStep L X) x y →
      Relation.TransGen (TcStep L X) y x → False := fun h1 h2 =>
    tcStep_acyclic hX hG _ (h1.trans h2)
  rw [pb]
  -- the candidate: the step just before this one in key order
  obtain ⟨jc, kc, hcAt, hkc, key, hbc, hj7⟩ : ∃ (jc : Fin 8) (kc : Nat), PvAt X g kc jc ∧ kc < kp ∧
      pvKey X g kc jc + 1 = pvKey X g kp j ∧
      pollRound 2510 ((X.tr g).take kc) = (if 0 < j.val then b else b - 1) ∧
      (j.val = 0 → jc = 7) := by
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · have b2 : 2 ≤ b := by
        rcases hacc j rfl rfl with h | h <;> omega
      obtain ⟨kR, lt, d2, s2, a2, m2, g2, q2⟩ := last (by rw [pb]; exact b2)
      refine ⟨7, kR, ⟨d2, s2, a2, m2, g2⟩, lt, ?_, (by simp [h0, pb] at q2 ⊢; omega),
        fun _ => rfl⟩
      unfold pvKey
      rw [q2, pb]
      omega
    · let jc : Fin 8 := ⟨j.val - 1, by have := j.isLt; omega⟩
      obtain ⟨kR, lt, d2, s2, a2, m2, g2, q2⟩ := prior jc (by simp [jc]; omega)
      refine ⟨jc, kR, ⟨d2, s2, a2, m2, g2⟩, lt, ?_, (by simp [hpos, pb] at q2 ⊢; omega),
        fun h => by omega⟩
      unfold pvKey
      rw [q2, pb]
      simp [jc]
      omega
  obtain ⟨dc, sc, ac, mc, hgc⟩ := hcAt
  obtain ⟨hdc, hDc⟩ := pv_cols hp hX hf base hgc
  obtain ⟨-, hDp⟩ := pv_cols hp hX hf base he
  obtain ⟨hwc, hwbc⟩ := step_candidate hp hX hf base hrd he hgc hkc (hdc.trans hd256.symm)
    (hDc.trans hDp.symm)
  obtain ⟨hne, hw, hwb, hmaster, -⟩ := readSource_acc.mp hs
  have hmp : X.MmaCell (g, kp) cell := mma_read_write hp hX hf base hrd
  have hmc : X.MmaCell (g, kc) cell := mma_of_write hgc hwc
  have hcm : (g, kc) = src ∨ WriteBefore L X (g, kc) src := by
    rcases hmaster (g, kc) hwc with h | h | h | h
    · exact .inl h
    · simp only [Prod.mk.injEq, true_and] at h
      omega
    · exact .inr h
    · exact absurd (hwbc.tcStep) (fun hc => cyc hc (WriteBefore.tcStep (.inl h)))
  obtain ⟨pcc, dcc, scc, accc, maskc, hec, ctc, hl1, hh1, -, -, -⟩ :=
    mma_write_cell hp hX hf base hmc
  have e := Option.some.inj (hgc.symm.trans hec)
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e
  obtain ⟨-, rfl, -, -, -⟩ := e
  have col256 : 256 ≤ cell.column := by omega
  have ctp : cell.cta = g / L.block := by
    obtain ⟨-, -, -, -, -, -, ct, -⟩ := mma_write_cell hp hX hf base hmp
    exact ct
  obtain ⟨gs, ks⟩ := src
  have main : (gs, ks) = (g, kc) ∨ ∃ r, RescaleAt L X (gs, ks) r cell ∧ r < b ∧
      pollRound 2510 ((X.tr g).take kc) ≤ r := by
    rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hsm | hst
    · left
      obtain ⟨hthr, -⟩ := mma_wb hp hX hf base hsm hmp
      have lt2 := mma_wb_lt hp hX hf base hG hsm hmp hwb
      simp only at hthr lt2
      subst hthr
      have lt1 : kc ≤ ks := by
        rcases hcm with h | h
        · simp only [Prod.mk.injEq, true_and] at h
          omega
        · exact Nat.le_of_lt (mma_wb_lt hp hX hf base hG hmc hsm h)
      obtain ⟨pcs, ds, ss, as, ms, hes, -, hl2, hh2, -, -, kind⟩ :=
        mma_write_cell hp hX hf base hsm
      obtain ⟨js, hpcs⟩ : ∃ js : Fin 8, pcs = Lib.pvIssue js := by
        rcases kind with ⟨j2, -, hd2, -⟩ | ⟨j2, h2, -⟩
        · omega
        · exact ⟨j2, h2⟩
      subst hpcs
      have := pv_between hp hX hf words hu ⟨dc, sc, ac, mc, hgc⟩ ⟨d, s, true, mask, he⟩
        ⟨ds, ss, as, ms, hes⟩ key lt1 lt2
      rw [this]
    · right
      obtain ⟨a, vals, sh, jj, ⟨pcs, hy⟩, hlen, hc⟩ := hst
      obtain ⟨-, -, k1 | k2⟩ := st_write_cell hp hX hf base (x := (gs, ks)) (cell := cell)
        ⟨a, vals, sh, jj, ⟨pcs, hy⟩, hlen, hc⟩
      · exfalso
        obtain ⟨a1, v1, ba, w, j1, g1, ha1, hb1, hj1, hc1⟩ := k1
        obtain ⟨-, c2, -⟩ := p_cols (L := L) (g := gs) (w := w) hb1 hj1
        rw [← ha1, ← hc1] at c2
        omega
      · obtain ⟨a2, v2, w, j2, g2, ha2, hj2, hc2⟩ := k2
        have e := Option.some.inj (hy.symm.trans g2)
        simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at e
        obtain ⟨rfl, -, -, -⟩ := e
        have tc : isTcColl ⟨2328, .tc (.st a vals sh)⟩ = true := rfl
        obtain ⟨r, w', s1, -, -, -⟩ := Proof.Export.st_round hp hX hf base hy tc (.inr rfl)
        have hres : RescaleAt L X (gs, ks) r cell := ⟨a, vals, sh, jj, hy, hlen, hc, s1⟩
        have cw : gs / L.block = g / L.block := (rescale_cta hp hX hf base hres).symm.trans ctp
        have hlt : r < b := by
          by_contra hge
          have wbp := pv_store_small hp hX hf safe hG base rows init tie hy s1 he cw pb
            (by omega)
          exact cyc wbp.tcStep hwb.tcStep
        refine ⟨r, hres, hlt, ?_⟩
        by_contra hgt
        have sd := store_pv_before hp hX hf safe base rows init hy s1 hgc cw rfl (by omega)
        rcases hcm with h | h
        · rw [← h, hgc] at hy
          simp at hy
        · exact cyc sd.tcStep h.tcStep
  have b2 : j.val = 0 → 2 ≤ b := fun h0 => by
    rcases hacc j rfl rfl with h | h <;> omega
  rcases main with h | ⟨r, hres, hlt, hle⟩
  · rw [h] at hmaster
    refine ⟨fun hpos => ?_, fun h0 => ?_⟩
    · simp only [hpos, ite_true] at hbc
      refine ⟨kc, jc, ?_, h, ⟨dc, sc, ac, mc, hgc⟩, hbc⟩
      unfold pvKey at key
      omega
    · have np : ¬ 0 < j.val := by omega
      simp only [np, ite_false] at hbc
      refine ⟨b2 h0, Or.inl ⟨kc, h, ?_, hbc, ?_⟩⟩
      · have := hj7 h0
        subst this
        exact ⟨dc, sc, ac, mc, hgc⟩
      · rintro ⟨gt, kt⟩ ⟨sa, sv, ssh, sj, sy, sjl, scell, srd⟩
        have cwt : gt / L.block = g / L.block :=
          (rescale_cta hp hX hf base ⟨sa, sv, ssh, sj, sy, sjl, scell, srd⟩).symm.trans ctp
        have hwr : TmemWrite L X (gt, kt) cell := .inr (.inl ⟨sa, sv, ssh, sj, ⟨2328, sy⟩, sjl,
          scell⟩)
        have sd := store_pv_before hp hX hf safe base rows init sy srd he cwt pb
          (show b - 1 < b by omega)
        have wb := pv_store_small hp hX hf safe hG base rows init tie sy srd hgc cwt rfl
          (by omega)
        rcases hmaster _ hwr with h1 | h1 | h1 | h1
        · rw [h1, hgc] at sy
          simp at sy
        · rw [h1, he] at sy
          simp at sy
        · exact cyc wb.tcStep h1.tcStep
        · exact cyc (WriteBefore.tcStep (.inl h1)) sd.tcStep
  · refine ⟨fun hpos => ?_, fun h0 => ?_⟩
    · exfalso
      simp only [hpos, ite_true] at hbc
      omega
    · have np : ¬ 0 < j.val := by omega
      simp only [np, ite_false] at hbc
      refine ⟨b2 h0, Or.inr ?_⟩
      have : r = b - 1 := by omega
      rw [← this]
      exact hres

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
