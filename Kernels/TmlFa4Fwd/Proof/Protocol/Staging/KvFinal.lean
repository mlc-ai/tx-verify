-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Final
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Packets
import Kernels.TmlFa4Fwd.Proof.Mma.Export.ScoreBlock
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.QFinal
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V copies before the final O stores

At a commit to a final O barrier the MMA lane has released every ring use it acquired. A copy of a
packet it released is before a final store of its bytes (`kv_copy_fst`), through the use's operand
read of the byte. The loader's packets are among the uses (`packetsUsed`): the
loader and the MMA warp agree on the tile's blocks. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k i : Nat}

/-- **The loader's packets are among the ring uses released at a final O commit** of the CTA. -/
def PacketsUsed (L : Launch) (X : Execution) : Prop :=
  ∀ {y c pcc y' jc pc : Nat} {s : TcCommit.Spec} {sp : AsyncCopy.Spec} {st : Fin 2},
    Prologue.warpIndex L y = 12 → X.get (y, c) = some ⟨pcc, .tc (.commit s)⟩ →
    s.mbar = Tm.bar L (y / L.block) (144 + 8 * st.val) → y' / L.block = y / L.block →
    X.get (y', jc) = some ⟨pc, .copy sp⟩ → pkt X y' jc < Tm.kvRels L X y c

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The loader's packets are the MMA warp's ring uses.** -/
theorem packetsUsed : PacketsUsed L X := by
  intro y c pcc y' jc pc s sp st hy hc hmb hcta hcp
  obtain ⟨hw, -⟩ := copy_row hp hX hFw (i := (y', jc)) ⟨_, hcp⟩
  obtain ⟨R, bal, hP, hlt⟩ := ld_pkt_lt (g := y') (k := jc) hp hX hFw hw hcp
  obtain ⟨Rm, ⟨R', bal', hP', hRm⟩, hk⟩ := Mma.o_commit_uses hp hX hFw hy st.isLt hc hmb
  obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hcta hP).unique hP'
  have hsv : Loader.sv (Loader.r28Ref p L y' R bal) =
      Mma.Bs p L y (mmaRef p L y R bal) := by
    rw [tile_agree (p := p) hcta R bal]
    simp only [Loader.sv, Mma.Bs, toSigned_r32]
    rfl
  rw [hsv] at hlt
  omega

/-- **An operand read of a row copy's byte**, of the copy's ring use, before a commit to a final O
barrier. -/
theorem kv_read_before {y jc pcc : Nat} {sp : AsyncCopy.Spec}
    (hcp : X.get (y, jc) = some ⟨pcc, .copy sp⟩) {l : Loc} (hcl : sp.dst.Covers l)
    {z c pcz : Nat} {s : TcCommit.Spec} {sto : Fin 2} (hz : z / L.block = y / L.block)
    (hz12 : Prologue.warpIndex L z = 12) (hcz : X.get (z, c) = some ⟨pcz, .tc (.commit s)⟩)
    (hmb : s.mbar = Tm.bar L (z / L.block) (144 + 8 * sto.val)) :
    ∃ k' idx d sp1 acc mask, KvRead L X z k' (pkt X y jc) ∧ X.MmaIssue (z, k') d sp1 acc mask ∧
      idx < 4096 ∧ sp1.byteLoc .b idx = some l := by
  obtain ⟨hy, hC⟩ := copy_row hp hX hFw (i := (y, jc)) ⟨_, hcp⟩
  simp only at hy hC
  obtain ⟨-, -, h3⟩ := Mma.o_commit_counts hp hX hFw hz12 sto.isLt hcz hmb
  have hlt := packetsUsed hp hX hFw hz12 hcz hmb hz.symm hcp
  set t := pkt X y jc with ht
  have h3s := h3 ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  simp only at h3s
  obtain ⟨c', ⟨pc', kd'⟩, hcc, he', hcm, hcnt⟩ := exists_nthEv (X := X) (g := z) (k := c)
    (p := commitsTo (Tm.bar L (z / L.block) (56 + 8 * (t % 3)))) (n := t / 3) (by omega)
  obtain ⟨s', rfl, hmb'⟩ : ∃ s', kd' = .tc (.commit s') ∧
      s'.mbar = Tm.bar L (z / L.block) (56 + 8 * (t % 3)) := by
    unfold commitsTo at hcm
    split at hcm
    · rename_i s' hk
      simp only at hk
      subst hk
      exact ⟨s', rfl, by simpa using hcm⟩
    · cases hcm
  have hsl : InSlot L z (t % 3) l := by
    obtain ⟨off, ho, rfl⟩ := copy_slot hC hcl
    exact ⟨off, ho, by rw [hz]⟩
  obtain ⟨t', k', idx, d, sp1, acc, mask, e1, e2, hk', hR, hmma, hidx, hbl⟩ :=
    kv_release_read hp hX hFw (s := ⟨t % 3, Nat.mod_lt _ (by decide)⟩) hz12 he' hmb' hsl
  have htt : t' = t := by
    simp only at e1 e2
    have : t' / 3 = t / 3 := by
      rw [← e2]
      exact hcnt
    omega
  subst htt
  exact ⟨k', idx, d, sp1, acc, mask, hR, hmma, hidx, hbl⟩

/-- **A row copy is before every final store of its bytes.** -/
theorem kv_copy_fst {y jc pcc : Nat} {sp : AsyncCopy.Spec}
    (hcp : X.get (y, jc) = some ⟨pcc, .copy sp⟩) {l : Loc} (hcl : sp.dst.Covers l)
    (hca : AsyncCovers X (y, jc) (.write .copy) l)
    (hsrc : ∃ b, X.Intent (.async (y, jc) (.write .copy)) b true ∧ b.Covers l)
    (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hl : l.space = .shared) (hc : a.Covers l) (hcta : y / L.block = h / L.block) :
    ByteCausality L X l (.async (y, jc) (.write .copy)) (.thread (h, i)) := by
  obtain ⟨hy, hC⟩ := copy_row hp hX hFw (i := (y, jc)) ⟨_, hcp⟩
  simp only at hy hC
  obtain ⟨z, c, pcz, s, sto, hz, hz12, hcz, hmb⟩ :=
    fst_commit hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  obtain ⟨k', idx, d, sp1, acc, mask, hR, hmma, hidx, hbl⟩ :=
    kv_read_before hp hX hFw hcp hcl (hz.trans hcta.symm) hz12 hcz hmb
  have hcr : AsyncCovers X (z, k') (.mmaRead true idx) l := mma_covers hmma hbl
  have hW := kv_copy_read hp hX hFw hcp hy hC hR (hcta.trans hz.symm) rfl le_rfl hca hcr
  exact through_mma hp hX hFw hw hw1 he hl hc hmma (isB := true) hbl hidx hz hsrc (.direct hW)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
