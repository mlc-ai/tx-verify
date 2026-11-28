-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdSrc
import Kernels.InklingRelDecode.Proof.Mma.Export.PvOrdinal
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleBound
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The word the epilogue's load returns

The epilogue's load takes its word from the last PV step of the last ordinal (`ld_e_pv7`): the
other writers of the cell are earlier PV steps, and the rescale stores of rounds below the number
of blocks, all before that step. The word is the `ResReal` of that step. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- **No rescale store has a round of the last block or later.** -/
def RescaleBound (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ t k a vals sh, X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
    pollRound 1257 ((X.tr t).take k) ≤ Lib.blocksOf Q L (t / L.block)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **No rescale store has a round of the last block or later**, proved. -/
theorem rescale_bound (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : RescaleBound Q L X :=
  fun _ _ _ _ _ he => Softmax.Export.rescale_round_le hp hX hf he

/-- **The source of the epilogue's load is the last PV step of the last ordinal.** -/
theorem ld_e_src (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (RB : RescaleBound Q L X)
    {t k0 a vals sh j} (he : X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) {src : EvId}
    (hrs : ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j)) :
    ∃ g kR, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧
      pollRound 2510 ((X.tr g).take kR) = Lib.blocksOf Q L (t / L.block) ∧ src = (g, kR) := by
  obtain ⟨g, kR, cy, ⟨d7, s7, a7, m7, gw⟩, ordN, wbw⟩ := ld_e_pv7 hp hX hf hu rows init he
  refine ⟨g, kR, cy, ⟨d7, s7, a7, m7, gw⟩, ordN,
    ld_src_pv7 hp hX hf hu hG base (Or.inr rfl) he hj gw cy wbw ?_ ?_ hrs⟩
  · intro k2 j2 d2 s2 a2 m2 he2 _
    obtain ⟨-, -, -, -, -, -, warp, -⟩ := Mma.Export.pv_block hp hX hf base he2 ⟨j2, rfl⟩
    have le2 := Mma.Export.pv_ordinal_le hp hX hf warp he2
    rw [ordN, ← cy]
    exact le2
  · intro k2 a2 v2 g2'
    have tc : isTcColl ⟨2328, .tc (.st a2 v2 (.s16x32bx2 64))⟩ = true := rfl
    obtain ⟨rs, ws, s1s, -, -, -⟩ := Proof.Export.st_round hp hX hf base g2' tc (.inr rfl)
    have small : rs < Lib.blocksOf Q L (t / L.block) := by
      have := RB t k2 a2 v2 (.s16x32bx2 64) g2'
      omega
    exact .inl (store_pv_before hp hX hf safe base rows init g2' s1s gw cy.symm ordN small)

/-- **The epilogue's load returns the real of the last PV step of the last ordinal.** -/
theorem ld_e_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
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
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) (RB : RescaleBound Q L X)
    {t k0 a vals sh j} (he : X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length)
    (valid : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane)) :
    ∃ g kR r1, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧
      pollRound 2510 ((X.tr g).take kR) = Lib.blocksOf Q L (t / L.block) ∧
      ResReal L X (pvA L X pw) (pvB Q L X) (svOf L X) (g, kR) (tcDataCell L t sh a j) r1 ∧
      vals[j]? = some (.float .f32 r1) :=
  ld_pv_real hp hX hf hu safe hG base rows init hws ht hmd words nub form W P hR (Or.inr rfl) he hj
    (fun hrs => ld_e_src hp hX hf hu safe hG base rows init RB he hj hrs) valid

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
