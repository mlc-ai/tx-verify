-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiStore
public import Kernels.InklingRelDecode.Proof.Protocol.Values.FinalOut
public import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRun
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Lib.EpiWords


@[expose] public section

/-! # The output words the epilogue stores

The epilogue's load returns, in the registers `1763 + j`, the words `o` of the row's fold at the
columns `64 (tb / 16 % 2) + j` (`final_out` with the cell of the load); the products with the
reciprocal of the row sum are the words `oPart` the word stores write. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem Lib.SoftRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The words of the epilogue's load** of a valid row, from `final_out`. -/
theorem ld_out_vals (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (final : ∀ {t k0 a vals sh j}, X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      j < vals.length → Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane) →
      vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
        (laneRow (tcDataCell L t sh a j).lane / 6)
        (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
        ((tcDataCell L t sh a j).column - 256)).o))
    (hrow : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block))) {k a vals sh}
    (he : X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩) :
    ∀ j, j < 64 → vals[j]? = some (.float .f32 (rowState Q (ctaZ L (g / L.block))
      (ctaXc L (g / L.block)) (Lib.tokM (g % L.block))
      (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6)
      (64 * (g % L.block / 16 % 2) + j)).o) := by
  intro j hj
  obtain ⟨-, -, -, -, -, hlen⟩ := ld_static hp hX hf base he
  obtain ⟨kk, -, rfl, rfl, -, -, hcell⟩ :=
    ld_o_cell hp hX hf base he (Or.inr rfl) (j := j) (by omega)
  have hb : L.block % 32 = 0 := by simp [hp.block]
  have e1 : laneRow (tcDataCell L g (.s16x32bx2 64) (256 + kk * 2 ^ 21) j).lane =
      Lib.rowM (g % L.block) := by
    rw [hcell]
    simp only [laneRow, Lib.rowM, laneOf]
    omega
  have e2 : (tcDataCell L g (.s16x32bx2 64) (256 + kk * 2 ^ 21) j).column - 256 =
      64 * (g % L.block / 16 % 2) + j := by
    rw [hcell]
    by_cases h : g % L.block % 32 < 16 <;> simp only [laneOf, h, ↓reduceIte] <;> omega
  have := final (j := j) he (by omega) (by rw [e1]; exact hrow)
  rw [e1, e2] at this
  exact this

/-- **An epilogue word store of a valid row writes the bytes of `outputWord`.** -/
theorem out_store (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (final : ∀ {t k0 a vals sh j}, X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      j < vals.length → Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane) →
      vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
        (laneRow (tcDataCell L t sh a j).lane / 6)
        (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
        ((tcDataCell L t sh a j).column - 256)).o))
    (hs : 0 < Q.scale) (hrow : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block)))
    {l : ℝ}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (hlk : ∀ d, (Lib.SoftRow.kState Q (ctaZ L (g / L.block)) (ctaXc L (g / L.block))
      (Lib.tokM (g % L.block)) (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6) d).l = l)
    {k j : Nat} {a : Acc} {bs : List Byte} (hj : j < 64)
    (he : X.get (g, k) = some ⟨2751 + j + j / 2, .wr a bs⟩) :
    bs = (if Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = 0 then b32 0
      else Value.float .f32 (oPart Q (ctaZ L (g / L.block)) (ctaXc L (g / L.block))
        (Lib.tokM (g % L.block)) (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6)
        (64 * (g % L.block / 16 % 2) + j))).toBytes := by
  have wait := epi_wait_of (g := g) hp hX hf
  have hpair := pairs_win (o := fun j' => (rowState Q (ctaZ L (g / L.block))
      (ctaXc L (g / L.block)) (Lib.tokM (g % L.block))
      (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6)
      (64 * (g % L.block / 16 % 2) + j')).o) entry wait
    (fun k a vals sh he' j' hj' => ld_out_vals hp hX hf base final hrow he' j' hj')
  rw [store_word hX hpair hj he]
  unfold wordV
  by_cases hb : Q.numIters (ctaZ L (g / L.block)) (ctaXc L (g / L.block)) = 0
  · have hb' : Lib.blocksOf Q L (g / L.block) = 0 := hb
    simp [hb, hb']
  · have hb' : ¬ Lib.blocksOf Q L (g / L.block) = 0 := hb
    simp only [hb, hb', decide_false, Bool.false_eq_true, ↓reduceIte]
    have := Lib.epiOut_eq Q hp.splitsPos hs (ctaZ L (g / L.block)) (ctaXc L (g / L.block))
      (Lib.tokM (g % L.block)) (ctaY L (g / L.block) * 6 + Lib.rowM (g % L.block) % 6)
      (64 * (g % L.block / 16 % 2) + j)
    rw [hlk] at this
    unfold Lib.epiOutWord at this
    rw [mul_comm] at this
    rw [this]

/-- **An epilogue word store of a launch without a block writes the zero word.** -/
theorem out_store_zero (hX : Consistent L kernel Assumptions.all m X) {v : Value}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g true) {k j : Nat} {a : Acc} {bs : List Byte} (hj : j < 64)
    (he : X.get (g, k) = some ⟨2751 + j + j / 2, .wr a bs⟩) : bs = (b32 0).toBytes := by
  have := store_word (b := true) (sc := 0) (o := fun _ => 0) hX
    (fun t ht h1 h2 m hm => by simpa [pairV] using pairs_win_zero entry wait t ht h1 h2 m hm) hj he
  simpa [wordV] using this

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
