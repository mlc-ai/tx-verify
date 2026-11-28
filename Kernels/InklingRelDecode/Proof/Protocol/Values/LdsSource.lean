-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdCand
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderS
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The source of a score load is step 7 of the block of its round

The load of round `r` has the last QK step of block `r` before it (`ld_s_cand`), and a QK MMA of
block `r + 2` follows the load (`ld_s_late`). A write of the cell after the last step of block `r`
and before the load would be a QK step of block `r`, and a QK step is issued once per round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load of round `r` takes its word from step 7 of block `r`.** -/
public theorem ld_s_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hG : SyncGuarded L kernel X)
    {t k0 a vals sh j src r} (he : X.get (t, k0) = some ⟨1265, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1)
    (hrs : ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j))
    (hsm : X.MmaCell src (tcDataCell L t sh a j)) :
    ∃ g k7, src = (g, k7) ∧ g / L.block = t / L.block ∧ QkAt X g k7 7 ∧
      pollRound 2462 ((X.tr g).take k7) = r + 1 := by
  have words : RoleBytes L X := fun h => Shared.role_bytes hp hX h
  obtain ⟨r0, hj64, lt, s1', s3, cellEq⟩ := ld_s_cell hp hX hf base he hj
  obtain ⟨⟨g, kw⟩, hw0, hwb0, r', b, s1c, cnt, parb, dst, sc, acc, mask, gw, q1⟩ :=
    ld_s_cand hp hX hf hu safe base rows init he hj 7
  have hr' : r' = r := by omega
  subst hr'
  simp only at q1 gw hwb0 hw0
  obtain ⟨b2, hdb, q1', q2', -⟩ := Mma.Export.qk_block hp hX hf base gw ⟨7, rfl⟩
  have hbb : b2 = b := by omega
  subst hbb
  have hmw : X.MmaCell (g, kw) (tcDataCell L t sh a j) := mma_of_write gw hw0
  obtain ⟨_, _, _, _, _, _, cw0, -⟩ := mma_write_cell hp hX hf base hmw
  have cw : t / L.block = g / L.block := by
    rw [cellEq] at cw0
    exact cw0
  have hwe : (g, kw) ≠ (t, k0) := fun h => by rw [h, he] at gw; cases gw
  have hbr : b2 = r' := by
    by_contra hne
    have big : r' / 2 < b2 / 2 := by omega
    have late := ld_s_late hp hX hf safe base rows init he lt s1 gw cw q2' (by omega) big
    have late' : ReadBefore L X .ld (t, k0) (g, kw) := Or.inl late
    exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep late' hwe).trans hwb0.tcStep)
  obtain ⟨hne, -, hsw, hmaster, -⟩ := readSource_ld.mp hrs
  rcases hmaster (g, kw) hw0 with h | h | h | ⟨-, -, -, a', v', sh', pc', hst⟩
  · exact ⟨g, kw, h.symm, cw.symm, ⟨dst, sc, acc, mask, gw⟩, by rw [q1, hbr]⟩
  · exfalso
    obtain ⟨hthr, -⟩ := mma_wb hp hX hf base hmw hsm
    have lt1 := mma_wb_lt hp hX hf base hG hmw hsm h
    obtain ⟨gs, ks⟩ := src
    simp only at hthr lt1
    subst hthr
    obtain ⟨pcs, ds, ss, as, ms, hes, cts, dls, dhs, -, -, kind⟩ := mma_write_cell hp hX hf base hsm
    rw [cellEq] at dls dhs
    dsimp only at dls dhs
    obtain ⟨j2, hpcs, -⟩ : ∃ j2 : Fin 8, pcs = Lib.qkIssue j2 ∧ True := by
      rcases kind with ⟨j2, hpcs, -⟩ | ⟨-, -, hd256, -⟩
      · exact ⟨j2, hpcs, trivial⟩
      · exfalso
        split_ifs at dls <;> omega
    obtain ⟨b', hd', q1s, q2s, -⟩ := Mma.Export.qk_block hp hX hf base hes ⟨j2, hpcs⟩
    have hmono := poll_round_mono (X := X) (g := g) lt1.le
    have par : b' % 2 = r' % 2 := by split_ifs at dls dhs <;> omega
    have hb'r : b' = r' := by
      by_contra hne'
      have big : r' / 2 < b' / 2 := by omega
      have late := ld_s_late hp hX hf safe base rows init he lt s1 hes cts q2s par big
      have late' : ReadBefore L X .ld (t, k0) (g, ks) := Or.inl late
      have hne2 : (g, ks) ≠ (t, k0) := fun h => by rw [h, he] at hes; cases hes
      exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep late' hne2).trans hsw.tcStep)
    have hqs : QkAt X g ks j2 := ⟨ds, ss, as, ms, by rw [← hpcs]; exact hes⟩
    have hqw : QkAt X g kw 7 := ⟨dst, sc, acc, mask, gw⟩
    have rr : pollRound 2462 ((X.tr g).take kw) = pollRound 2462 ((X.tr g).take ks) := by omega
    rcases Nat.lt_or_ge j2.val 7 with h7 | h7
    · obtain ⟨kk, ltk, d3, s3', a3, m3, getk, qk⟩ :=
        Mma.Export.qk_prior hp hX hf words hu gw rfl j2 h7
      have := qk_unique hp hX hf words ⟨d3, s3', a3, m3, getk⟩ hqs (by omega)
      omega
    · have : j2 = 7 := Fin.ext (by omega)
      subst this
      have := qk_unique hp hX hf words hqw hqs rr
      omega
  · exfalso
    have late' : ReadBefore L X .ld (t, k0) (g, kw) := Or.inl h
    exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep late' hwe).trans hwb0.tcStep)
  · cases get_tc_inj gw hst
