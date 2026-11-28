-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvVals
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdSource
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdCand
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # The word an accumulator load returns, from its source

An accumulator load (the round's or the epilogue's) takes its word from the last PV step of an
ordinal the caller names (`ld_src_pv7`: no other writer of the cell is the source), and the word is
the `ResReal` of that step (`ld_pv_real`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The MMA writers of the cell of an accumulator load are PV steps. -/
theorem pv_of_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {i : EvId} {cell : Cell}
    (hm : X.MmaCell i cell) (col : 256 ≤ cell.column) : PvIssue X i := by
  obtain ⟨pc, d, s, acc, mask, he, -, lo, hi, -, -, kind⟩ := mma_write_cell hp hX hf base hm
  rcases kind with ⟨j, -, hd, -⟩ | ⟨j, hpc, -⟩
  · omega
  · exact ⟨pc, d, s, acc, mask, he, j, hpc⟩

/-- **The source of an accumulator load is the last PV step the caller names.** `bound`: a PV step
written before the load is of an ordinal at most the step's; `late`: a rescale store of the load's
thread is before the step or after the load. -/
theorem ld_src_pv7 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {t k0 pc a vals sh j}
    (hpc : pc = 2260 ∨ pc = 2607) (he : X.get (t, k0) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) {g kR d7 s7 a7 m7}
    (gw : X.get (g, kR) = some ⟨Lib.pvIssue 7, .tc (.mma d7 s7 a7 m7)⟩)
    (cy : g / L.block = t / L.block) (wbw : WriteBefore L X (g, kR) (t, k0))
    (bound : ∀ {k2 j2 d2 s2 a2 m2},
      X.get (g, k2) = some ⟨Lib.pvIssue j2, .tc (.mma d2 s2 a2 m2)⟩ →
      WriteBefore L X (g, k2) (t, k0) →
      pollRound 2510 ((X.tr g).take k2) ≤ pollRound 2510 ((X.tr g).take kR))
    (late : ∀ {k2 a2 v2}, X.get (t, k2) = some ⟨2328, .tc (.st a2 v2 (.s16x32bx2 64))⟩ →
      StoreDoneBefore L X (t, k2) (g, kR) ∨ ReadBefore L X .ld (t, k0) (t, k2))
    {src : EvId} (hrs : ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j)) :
    src = (g, kR) := by
  obtain ⟨kk, -, rfl, rfl, hj64, lt, cellEq⟩ := ld_o_cell hp hX hf base he hpc hj
  have wcell : X.MmaCell (g, kR) (tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j) := by
    rw [cellEq]
    exact pv_cell_write hp hX hf base gw cy hj64
  have col : 256 ≤ (tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j).column := by
    rw [cellEq]
    dsimp only
    omega
  have cyc : ∀ {x y : EvId}, Relation.TransGen (TcStep L X) x y →
      Relation.TransGen (TcStep L X) y x → False := fun h1 h2 =>
    tcStep_acyclic hX hG _ (h1.trans h2)
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨g2, k2⟩ := src
  obtain ⟨hne, hw, hwb, hmaster, -⟩ := readSource_ld.mp hrs
  have nld : ∀ {e : EvId} {pc d s acc mask},
      X.get e = some ⟨pc, .tc (.mma d s acc mask)⟩ → e ≠ (t, k0) :=
    fun {e} {pc d s acc mask} h hh => by
    rw [hh, he] at h
    simp at h
  rcases hmaster (g, kR) (.inl wcell) with h | h | h | ⟨-, -, -, a2, v2, sh2, pc2, hst⟩
  · exact h.symm
  · exfalso
    rcases tmemWrite_of_no_copy (Lib.no_cp hX) (no_shift hX) hw with hsm | hsc
    · obtain ⟨hthr, -⟩ := mma_wb hp hX hf base wcell hsm
      have lt2 := mma_wb_lt hp hX hf base hG wcell hsm h
      simp only at hthr lt2
      subst hthr
      obtain ⟨pc2, d2, s2, acc2, mask2, he2, j2, hpc2⟩ := pv_of_cell hp hX hf base hsm col
      subst hpc2
      have le2 := bound he2 hwb
      have j8 := j2.isLt
      have atS : PvAt X g k2 j2 := ⟨d2, s2, acc2, mask2, he2⟩
      have atW : PvAt X g kR 7 := ⟨d7, s7, a7, m7, gw⟩
      rcases Nat.lt_or_ge (pvKey X g k2 j2) (pvKey X g kR 7) with hlt | hge
      · have := pv_key_lt hp hX hf words hu atW atS hlt
        omega
      · unfold pvKey at hge
        have jj : j2 = 7 := Fin.ext (by have h7 : (7 : Fin 8).val = 7 := rfl; omega)
        subst jj
        have := pv_unique hp hX hf words atS atW (by omega)
        omega
    · obtain ⟨a', vals', sh', jj, ⟨pcs, hy⟩, hlen, hc⟩ := hsc
      obtain ⟨lts, -, k1 | k1⟩ := st_write_cell hp hX hf base (x := (g2, k2))
        (cell := tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j)
        ⟨a', vals', sh', jj, ⟨pcs, hy⟩, hlen, hc⟩
      · obtain ⟨a1, v1, ba, w, j1, g1, ha1, hba, hj1, hc1⟩ := k1
        obtain ⟨-, c2, -⟩ := p_cols (L := L) (g := g2) (w := w) hba hj1
        rw [← ha1, ← hc1] at c2
        omega
      · obtain ⟨a2, v2, w, j2, g2', ha, hj2, hc2⟩ := k1
        rw [ha] at hc2
        have c1 := congrArg Cell.cta hc2
        rw [cell_split L t 256 64 kk j (by omega), cell_split L g2 256 64 w j2 (by omega)] at c1
        dsimp only at c1
        have cw : t = g2 := split_thread (L := L) (off := 64) (ba := 256) (by omega)
          (by omega) (by omega) lt lts c1 hc2
        subst cw
        have ne : (t, k2) ≠ (t, k0) := fun hh => by
          simp at hh
          rw [hh, he] at g2'
          simp at g2'
        rcases late g2' with sd | rb
        · exact cyc sd.tcStep h.tcStep
        · exact cyc (ReadBefore.tcStep rb ne) hwb.tcStep
  · have late : ReadBefore L X .ld (t, k0) (g, kR) := Or.inl h
    exact (cyc (ReadBefore.tcStep late (nld gw)) wbw.tcStep).elim
  · rw [gw] at hst
    simp at hst

/-- **An accumulator load whose source is a last PV step returns that step's real.** -/
theorem ld_pv_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hws : WritesSafe L X)
    (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    (words : RoleBytes L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) (W : Iface.PWords X)
    {pw : Nat → Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) {t k0 pc a vals sh j}
    (hpc : pc = 2260 ∨ pc = 2607) (he : X.get (t, k0) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) {Φ : Nat → Nat → Prop}
    (hsrc : ∀ {src}, ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j) →
      ∃ g kR, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧ Φ g kR ∧ src = (g, kR))
    (valid : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane)) :
    ∃ g kR r1, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧ Φ g kR ∧
      ResReal L X (pvA L X pw) (pvB Q L X) (svOf L X) (g, kR) (tcDataCell L t sh a j) r1 ∧
      vals[j]? = some (.float .f32 r1) := by
  have E := pv_elements hp hX hf hu safe base rows init hG hws ht hmd words nub form W hR
  have V := pv_vals hp hX hf hu safe base rows init hG hws ht hmd words nub form W P hR
  obtain ⟨kk, -, rfl, rfl, hj64, lt, cellEq⟩ := ld_o_cell hp hX hf base he hpc hj
  have col : 256 ≤ (tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j).column := by
    rw [cellEq]
    dsimp only
    omega
  have hl : LoadCell L X (t, k0) j (tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j) :=
    ⟨_, vals, _, ⟨pc, he⟩, hj, rfl⟩
  have hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      X.MmaCell i (tcDataCell L t (.s16x32bx2 64) (256 + kk * 2 ^ 21) j) →
      WriteBefore L X i (t, k0) → CompletedValues L Assumptions.all X i := by
    intro i d s acc mask hi hmc hwb hdi c ⟨d2, s2, a2, m2, r2, c2, hi2, hp2⟩
    obtain ⟨g, k⟩ := i
    obtain ⟨r, hr⟩ := results hp hX hf hu safe base rows init hG hws ht hmd E
      (pv_closed hp hX hf base) k g d2 s2 a2 m2 r2 c2 c (pv_of_cell hp hX hf base hmc col) hi2
      hp2 hdi
    exact ⟨_, hr⟩
  obtain ⟨src, value, hrs, hw, hdone⟩ :=
    ld_source_done hp hX hf hu safe base rows init hG hws ht hCV hl
  obtain ⟨g, kR, cy, pat, hΦ, hsrc'⟩ := hsrc hrs
  subst hsrc'
  obtain ⟨d7, s7, a7, m7, gw⟩ := pat
  rcases hw with hres | hst | hcp | hsh
  · obtain ⟨r1, hv, rr⟩ := result_real hp hX hf base hG V
      (fun hd hi hw hv => pv_link hp hX hf base hd hi hw hv) (pv_closed hp hX hf base) hres
      ⟨_, d7, s7, a7, m7, gw, 7, rfl⟩ (hdone (result_cell hres)) valid
    subst hv
    exact ⟨g, kR, r1, cy, ⟨d7, s7, a7, m7, gw⟩, hΦ, rr,
      LoadReadOk.f32 hX.tcRead.1 ⟨pc, he⟩ hl hrs (.inl hres)⟩
  · obtain ⟨a', vals', sh', j', ⟨pc', hst⟩, -⟩ := hst
    rw [gw] at hst
    simp at hst
  · obtain ⟨c, _, _, _, _, _, _, hp', -⟩ := hcp
    exact (Lib.no_cp hX _ _ hp').elim
  · obtain ⟨_, _, ⟨⟨sp, hp', -⟩, -⟩, -⟩ := hsh
    exact (Tmem.no_shift hX _ _ hp').elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
