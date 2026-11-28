-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.SentHalf
import Kernels.InklingRelDecode.Proof.Softmax.Export.SentRound
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand

/-! # The word a lane receives at pc 1838 is the other half's maximum

The lane 16 away works on the other half of the same row and block, and its shuffle of pc 1838 has
the same ordinal, so it is in the same round (the shuffles before a round are a strictly increasing
function of the round). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {g : Nat}

private theorem xor16 : ∀ a < 32, (a ^^^ 16) < 32 ∧ (a ^^^ 16) % 16 = a % 16 ∧
    (a ^^^ 16) / 16 = 1 - a / 16 := by decide

/-- **The received word is the other half's maximum**, when the lanes' loads are exact. -/
public theorem recv_half {m : Mem0} {X : Execution} {k : Nat} {b c : Nat} {recv : Value}
    {ok : Bool} {sent : Value} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X)
    (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (get : X.get (g, k) = some ⟨1838, .shfl .bfly sent b c recv ok⟩) :
    Lib.Ev recv (Lib.halfMax Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g)
      (pollRound 1257 ((X.tr g).take k) - 1) (1 - g % L.block / 16 % 2)) := by
  obtain ⟨rfl, rfl⟩ : b = 16 ∧ c = 31 := by
    obtain ⟨-, h1, h2⟩ := shfl5_shape hp hX get
    exact ⟨h1, h2⟩
  obtain ⟨j, b', c', r', o', got, low, cta, cnt⟩ :=
    late_partner hp hX hf get (Or.inl rfl) (by decide) lane
  set gp := g - g % 32 + (g % 32 ^^^ 16) with hgp
  have hb : L.block = 256 := hp.block
  obtain ⟨x1, x2, x3⟩ := xor16 (g % 32) (Nat.mod_lt _ (by decide))
  have row : Lib.softRow (gp % L.block) = Lib.softRow (g % L.block) := by
    unfold Lib.softRow; rw [hgp, hb]; omega
  have half : gp % L.block / 16 % 2 = 1 - g % L.block / 16 % 2 := by
    rw [hgp, hb]; omega
  have hvp : Lib.QRowValid Q L (gp / L.block) (Lib.softRow (gp % L.block)) := by
    rw [cta, row]; exact hv
  obtain ⟨-, h1⟩ := sent_half hp hX hf (hB gp) (hS gp) hvp got
  obtain ⟨c1, p1⟩ := shfl5_count hp hX hf get
  obtain ⟨c2, p2⟩ := shfl5_count hp hX hf got
  rw [cnt, cta, c1] at c2
  have eq : pollRound 1257 ((X.tr gp).take j) = pollRound 1257 ((X.tr g).take k) := by
    have e : Lib.shflBase (pollRound 1257 ((X.tr g).take k) - 1) =
        Lib.shflBase (pollRound 1257 ((X.tr gp).take j) - 1) := by omega
    rcases lt_trichotomy (pollRound 1257 ((X.tr g).take k) - 1)
      (pollRound 1257 ((X.tr gp).take j) - 1) with h | h | h
    · have := Lib.shflBase_lt h; omega
    · omega
    · have := Lib.shflBase_lt h; omega
  rw [eq, cta, row, half] at h1
  have hd : Lib.laneHead L gp = Lib.laneHead L g := by
    unfold Lib.laneHead; rw [cta, row]
  rw [hd] at h1
  exact h1

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
