-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsScore
public import Kernels.InklingRelDecode.Proof.Lib.ScoreEv
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderS
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic

@[expose] public section

/-! # The score loads of a lane return the specification's scores

The load of pc 1265 reads 64 cells of the lane's row, from the column of its half of the round's
score buffer (`ld_s_cell`), and `ld_s_score` says what the cell of a row and column holds. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load returns the lane's scores.** -/
theorem score_ev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X) {g : Nat} :
    Lib.ScoreEv Q L g X := by
  intro k a vals sh he hv j hj
  obtain ⟨-, -, -, -, -, hl64⟩ := ld_static hp hX hf base he
  have hjl : j < vals.length := by omega
  obtain ⟨r, -, lt, s1, -, cellEq⟩ := ld_s_cell hp hX hf base he hjl
  obtain ⟨row, col, hr, hc, -, hlane, hcol, hval⟩ :=
    ld_s_score hp hX hf hu safe base rows init hG hws ht hmd words nub form he hjl s1
  rw [cellEq] at hlane hcol
  simp only [laneOf] at hlane hcol
  have hrow : row = Lib.softRow (g % L.block) := by
    unfold Lib.softRow
    clear cellEq
    omega
  have hcol' : col = 64 * (g % L.block / 16 % 2) + j := by
    clear cellEq
    by_cases h : g % L.block % 32 < 16 <;> simp only [h, ite_true, ite_false] at hcol <;> omega
  subst hrow hcol'
  rw [s1, Nat.add_sub_cancel]
  have := hval hv
  rw [this]
  simp only [Lib.laneScore, Lib.laneHead, Lib.laneKey, add_assoc]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
