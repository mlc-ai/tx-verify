-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.ScoreEv
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvElems
public import Kernels.InklingRelDecode.Proof.Lib.FoldPw
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvWords
import Kernels.InklingRelDecode.Proof.Softmax.Export.PwordEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasEv
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Values.RescaleCell
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount

@[expose] public section

/-! # The probability stores hold the fold's probabilities

Word `jj` of the store of pc 1009 of a row that loads is the pair of the fold's probabilities of the
keys `2 c` and `2 c + 1` of the round's block, `c` the cell's column in its score buffer. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem lane_row_cell (T : Nat) : laneRow (T / 32 % 4 * 32 + T % 32 % 16) = Lib.softRow T := by
  unfold laneRow Lib.softRow
  omega

theorem col_half (T r jj : Nat) :
    r % 2 * 128 + (if T % 32 < 16 then 0 else 32) + jj - 128 * (r % 2) =
      32 * (T / 16 % 2) + jj := by
  split_ifs <;> omega

/-- **A probability store of a valid row writes the fold's probabilities.** -/
theorem pw_store (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    {t k a vals sh jj r}
    (hv : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a jj).lane))
    (get : X.get (t, k) = some ⟨1009, .tc (.st a vals sh)⟩)
    (hr : pollRound 1257 ((X.tr t).take k) = r + 1) (hj : jj < vals.length) :
    vals[jj]? = some (Value.pair
      (Value.float .bf16 (Lib.foldPw Q L (t / L.block) r (laneRow (tcDataCell L t sh a jj).lane)
        (2 * ((tcDataCell L t sh a jj).column - 128 * (r % 2)))))
      (Value.float .bf16 (Lib.foldPw Q L (t / L.block) r (laneRow (tcDataCell L t sh a jj).lane)
        (2 * ((tcDataCell L t sh a jj).column - 128 * (r % 2)) + 1)))) := by
  have lane := Export.tc_data_lane hp hX hf get (by rfl)
  obtain ⟨r', w, h1, -, -, sta⟩ := Export.st_round hp hX hf base get (by rfl) (Or.inl rfl)
  obtain rfl : r = r' := by omega
  simp only [tcStatic, Lib.opStatic, Lib.bcastOffset] at sta
  simp at sta
  obtain ⟨ha, hsh⟩ := sta
  have cs : tcDataCell L t sh a jj = ⟨t / L.block, t % L.block / 32 % 4 * 32 +
      laneOf L t % 16, r % 2 * 128 + (if laneOf L t < 16 then 0 else 32) + jj⟩ := by
    rw [ha, hsh]
    exact cell_split L t (r % 2 * 128) 32 ((Lib.word w).toNat % 4) jj (by omega)
  have hrow : laneRow (tcDataCell L t sh a jj).lane = Lib.softRow (t % L.block) := by
    rw [cs]
    exact lane_row_cell _
  have hcol : (tcDataCell L t sh a jj).column - 128 * (r % 2) =
      32 * (t % L.block / 16 % 2) + jj := by
    rw [cs]
    exact col_half _ _ _
  rw [hrow] at hv
  rw [hrow, hcol]
  obtain ⟨hl32, hlt, hw⟩ := Softmax.Export.pword_ev hp hX hf
    (fun g => Softmax.Export.bias_ev hp hX hf)
    (fun g => score_ev hp hX hf hu safe base rows init hG hws ht hmd words nub form) lane hv get
  rw [h1, Nat.add_sub_cancel] at hlt hw
  have e := hw jj (by omega)
  rw [Lib.lanePw_eq Q L t r (2 * jj) hp.splitsPos hp.scalePos hlt (by omega),
    Lib.lanePw_eq Q L t r (2 * jj + 1) hp.splitsPos hp.scalePos hlt (by omega)] at e
  have k1 : 64 * (t % L.block / 16 % 2) + 2 * jj = 2 * (32 * (t % L.block / 16 % 2) + jj) := by
    omega
  have k2 : 64 * (t % L.block / 16 % 2) + (2 * jj + 1) =
      2 * (32 * (t % L.block / 16 % 2) + jj) + 1 := by omega
  rw [k1, k2] at e
  exact e

/-- **The fold's words** `Lib.foldPw` and `Lib.foldAl` are the fold's, for every dimension. -/
theorem fold_words (Q : Params) (L : Launch) : FoldWords Q L (Lib.foldPw Q L) (Lib.foldAl Q L) := by
  refine ⟨fun c row d b κ _ _ => ?_, fun c row d b _ => ?_⟩
  · unfold Lib.foldPw
    rw [Lib.mUse_d Q _ _ _ _ 0 d b]
    rfl
  · unfold Lib.foldAl
    rw [Lib.alpha_d Q _ _ _ _ 0 d b]

/-- **The probability stores of the rows that load hold the fold's probabilities.** -/
theorem pwords_soft (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X) :
    PWords Q L X (Lib.foldPw Q L) := by
  unfold PWords
  intro t k a vals sh jj r hv get hr hj
  exact pw_store hp hX hf hu safe base rows init hG hws ht hmd words nub form hv get hr hj

/-- **A rescale store of a valid row writes the fold's factor times the loaded word.** -/
theorem rescale_al (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    (hov : ∀ t j a' ov sh', X.get (t, j) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
      ∀ x ∈ ov, ∃ r : ℝ, x = .float .f32 r) :
    RescaleAl Q L X (Lib.foldAl Q L) := by
  unfold RescaleAl
  intro t k a vals sh kl a' ov sh' jj hv get hl hr hj
  have lane := Export.tc_data_lane hp hX hf get (by rfl)
  have cs := st_cell hp hX hf base get jj
  have hrow : laneRow (tcDataCell L t sh a jj).lane = Lib.softRow (t % L.block) := by
    rw [cs]
    exact lane_row_cell _
  rw [hrow] at hv ⊢
  obtain ⟨x, hx, hvals⟩ := Softmax.Export.rescale_ev hp hX hf
    (fun g => Softmax.Export.bias_ev hp hX hf)
    (fun g => score_ev hp hX hf hu safe base rows init hG hws ht hmd words nub form) lane hv
    (hov t) get hl hr hj
  exact ⟨x, hx, hvals⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
