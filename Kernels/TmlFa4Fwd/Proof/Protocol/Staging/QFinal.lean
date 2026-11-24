-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Final
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FstPoll
import Kernels.TmlFa4Fwd.Proof.Lib.SmemCover
import Kernels.TmlFa4Fwd.Proof.Mma.Export.ScoreBlock
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q copies before the final O stores

The final O poll before a final store observes a commit of the CTA's warp 12 lane, which follows an
S-full commit of each stage, hence the eight QK MMAs of the stage, whose A operands fill the Q
stage (`q_read_before`). So a copy that writes a byte of a Q stage precedes an operand read of the
byte that the poll observes, and the final store (`q_copy_fst`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k i : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The commit a final store follows**, of the MMA warp's lane. -/
theorem fst_commit (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hs : a.loc.space = .shared) : ∃ y c pcc s, ∃ st : Fin 2, y / L.block = h / L.block ∧
      Prologue.warpIndex L y = 12 ∧ X.get (y, c) = some ⟨pcc, .tc (.commit s)⟩ ∧
      s.mbar = Tm.bar L (y / L.block) (144 + 8 * st.val) := by
  obtain ⟨st, -, hk, -⟩ := corr_fst hp hX hFw hw hw1 he hs
  obtain ⟨j, hji, pcj, hj⟩ := corr_o_poll hp hX hFw hw hw1 st hk.ge
  obtain ⟨y, c, pcc, s, rank, hc, -, hy, hy12, hmb, -⟩ := o_handoff hp hX hFw st (g := h) hj
  refine ⟨y, c, pcc, s, st, hy, hy12, hc, ?_⟩
  rw [hmb, ← obj_cta hy]

/-- **An operand read of every byte of a Q stage** before a commit to a final O barrier. -/
theorem q_read_before {y c pcc : Nat} {s : TcCommit.Spec} {sto : Fin 2}
    (hy : y / L.block = h / L.block) (hy12 : Prologue.warpIndex L y = 12)
    (hc : X.get (y, c) = some ⟨pcc, .tc (.commit s)⟩)
    (hmb : s.mbar = Tm.bar L (y / L.block) (144 + 8 * sto.val))
    {st : Nat} (hst : st < 2) {l : Loc} {off : Nat}
    (ho : off < 32768)
    (hl : l = ⟨.shared, h / L.block, L.sharedBase + 3072 + 32768 * st + off⟩) :
    ∃ k u idx, ∃ j : Fin 8, ∃ d sp acc mask, Tm.Qk L X y k st u j ∧
      X.MmaIssue (y, k) d sp acc mask ∧ idx < 4096 ∧ sp.byteLoc .a idx = some l := by
  obtain ⟨h1, -, -⟩ := Mma.o_commit_counts hp hX hFw hy12 sto.isLt hc hmb
  obtain ⟨c', ⟨pc', kd'⟩, hcc, he', hcm, -⟩ := exists_nthEv (X := X) (g := y) (k := c) (n := 0)
    (h1 st hst)
  obtain ⟨s', rfl, hmb'⟩ : ∃ s', kd' = .tc (.commit s') ∧
      s'.mbar = Tm.bar L (y / L.block) (80 + 8 * st) := by
    unfold commitsTo at hcm
    split at hcm
    · rename_i s' hk
      simp only at hk
      subst hk
      exact ⟨s', rfl, by simpa using hcm⟩
    · cases hcm
  have hsh := hp.shared.1
  have hbase : (L.sharedBase + 3072 + 32768 * st + 16384 * (off / 16384)) % 128 = 0 := by omega
  obtain ⟨j4, hj4, idx, hidx, hcov⟩ := Tm.qk_cover (off := off % 16384) hbase
    (Nat.mod_lt _ (by decide))
  obtain ⟨k', -, u, hq⟩ := Mma.s_block hp hX hFw hy12 hst he' hmb'
    ⟨4 * (off / 16384) + j4, by omega⟩
  obtain ⟨pcq, da, db, hi⟩ := hq.issue
  have hmma : X.MmaIssue (y, k') _ _ _ _ := ⟨pcq, hi⟩
  obtain ⟨-, -, -, hsp⟩ := hq.spec_eq hmma
  refine ⟨k', u, idx, _, _, _, _, _, hq, hmma, hidx, ?_⟩
  rw [hsp, hl, ← hy]
  have hcv := (hcov ⟨Tm.qkDsc, Tm.qkA L st ⟨4 * (off / 16384) + j4, by omega⟩,
    Tm.qkB L (2 * u % 3) ⟨4 * (off / 16384) + j4, by omega⟩, y / L.block, y / L.block, none, {}⟩
    (y / L.block) rfl rfl rfl).1 (by
      simp only [Tm.qkA]
      congr 1
      have e1 : (4 * (off / 16384) + j4) / 4 = off / 16384 := by omega
      have e2 : (4 * (off / 16384) + j4) % 4 = j4 := by omega
      rw [e1, e2])
  rw [hcv]
  congr 2
  omega

/-- **A copy into a Q stage is before every final store of its bytes.** -/
theorem q_copy_fst {e : EvId} {pce al : Nat} {s : TensorCopy.Spec}
    (hce : X.get e = some ⟨pce, .tensorIssue al s⟩) {x y z : Nat} {l : Loc}
    (hwl : TensorCopy.writeLoc s x y z = some l) (h1 : L.sharedBase + 3072 ≤ l.addr)
    (h2 : l.addr < L.sharedBase + 68608)
    (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hl : l.space = .shared) (hc : a.Covers l) :
    ByteCausality L X l (.async e (.write (.load x y z))) (.thread (h, i)) := by
  obtain ⟨sto, ⟨-, q, -, w, -, hloc⟩, -⟩ := corr_fst hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  have hcta : l.cta = h / L.block := by rw [hc.2.1, hloc]
  obtain ⟨st, hst, off, ho, hadd⟩ : ∃ st < 2, ∃ off < 32768,
      l.addr = L.sharedBase + 3072 + 32768 * st + off :=
    ⟨(l.addr - L.sharedBase - 3072) / 32768, by omega,
      (l.addr - L.sharedBase - 3072) % 32768, Nat.mod_lt _ (by decide), by omega⟩
  have hleq : l = ⟨.shared, h / L.block, L.sharedBase + 3072 + 32768 * st + off⟩ := by
    obtain ⟨s1, c1, a1⟩ := l
    simp only at hl hcta hadd
    subst hl hcta hadd
    rfl
  obtain ⟨y', c', pcc, sc, stc, hy, hy12, hcc, hmb⟩ :=
    fst_commit hp hX hFw hw hw1 he (hc.1.symm.trans hl)
  obtain ⟨k', u, idx, j, d, sp, acc, mask, hq, hm, hidx, hbl⟩ :=
    q_read_before hp hX hFw hy hy12 hcc hmb hst ho hleq
  have hcr : AsyncCovers X (y', k') (.mmaRead false idx) l := mma_covers hm hbl
  have hW := q_copy_read hp hX hFw hce hwl hq hst hcr (hcta.trans hy.symm) (by omega) (by omega)
  exact through_mma hp hX hFw hw hw1 he hl hc hm (isB := false) hbl hidx hy
    ⟨{ loc := l, size := 1 }, ⟨rfl, s, al, ⟨pce, hce⟩, hwl, rfl⟩, ⟨rfl, rfl, le_rfl, by simp⟩⟩
    (.direct hW)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
