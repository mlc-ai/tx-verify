-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Top.Result.OutRest
import Kernels.InklingRelDecode.Proof.Softmax.Export.EpiEntry
import Kernels.InklingRelDecode.Proof.Lib.EpiNext
public import Kernels.InklingRelDecode.Proof.Lib.SoftLane
import Kernels.InklingRelDecode.Proof.Top.Safe.NoUb
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasEv
import Kernels.InklingRelDecode.Proof.Top.Result.OutFinal
import Kernels.InklingRelDecode.Proof.Lib.KStD

@[expose] public section

/-! # The entry of the epilogue, from the softmax's export

The state at pc 2562 of a lane with a block is followed by the epilogue's wait (pc 2565); the
softmax's `epi_sum_entry` gives its registers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX Protocol.Values

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Result.rowK_eq (g d : Nat) : rowK Q L g d = Lib.SoftRow.kState Q
    ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
    (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) d := by
  have : Lib.softRow (g % L.block) = Lib.rowM (g % L.block) := by
    unfold Lib.softRow Lib.rowM; omega
  unfold rowK Lib.laneHead Lib.tokM
  rw [this]

/-- **The sum, maximum and scale registers at pc 2562** of a lane with a block. -/
theorem Result.sumEntry (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hc : Complete L X) (hf : Follow Q L X)
    {g : Nat} (hg : g < L.threads) (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block))) (hn : 0 < cellIters Q L g)
    {t : TState} (hl : Iface.LaneState L X g t) (hpc : t.pc = 2562) :
    ∃ l, t.regs 1915 = some (.float .f32 l) ∧ 0 ≤ l ∧
      (∀ d, l = (rowK Q L g d).l) ∧ (0 < l → ∃ mr, t.regs 1914 = some (.float .f32 mr) ∧
        (∀ d, mr = (rowK Q L g d).m.toReal) ∧
        t.regs 498 = some (.float .f32 (Q.scale * log2eF32))) := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨ev, nxt, h5⟩ := Lib.next_2562 hX hc hg (Result.notCanceled hX g) hr hrt hpc
  have hu := Safe.noUb hp hX hf
  have nu : ∀ f, ev.kind ≠ .ub f := fun f h => hu ⟨(g, k), ev.pc, f, by
    obtain ⟨p, kd⟩ := ev; subst h; exact nxt⟩
  have hev : ev.pc = 2565 := h5.resolve_right fun ⟨f, h⟩ => nu f h
  have sr : Lib.softRow (g % L.block) = Lib.rowM (g % L.block) := by
    unfold Lib.softRow Lib.rowM; omega
  have hB : ∀ g, Lib.BiasEv Q L g X := fun g => Softmax.Export.bias_ev hp hX hf
  obtain ⟨l, r1, nn, col, rest⟩ := Softmax.Export.epi_sum_entry hp hX hf hB
    (Result.scoreEv hp hX hf) lane (by rwa [sr]) hn hr hrt hpc nxt hev nu
  simp only [Result.rowK_eq]
  exact ⟨l, r1, nn, col, fun h => by obtain ⟨mr, a, b, c⟩ := rest h; exact ⟨mr, a, b, c⟩⟩

/-- **The sum register at pc 2562 of a lane without a block** holds the zero bits. -/
theorem Result.emptyEntry (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hc : Complete L X) (hf : Follow Q L X)
    {g : Nat} (hg : g < L.threads) (hn : cellIters Q L g = 0) {t : TState}
    (hl : Iface.LaneState L X g t) (hpc : t.pc = 2562) :
    t.regs 1915 = some (.bits 32 (BitVec.ofNat 64 0)) := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨ev, nxt, h5⟩ := Lib.next_2562 hX hc hg (Result.notCanceled hX g) hr hrt hpc
  have hu := Safe.noUb hp hX hf
  have nu : ∀ f, ev.kind ≠ .ub f := fun f h => hu ⟨(g, k), ev.pc, f, by
    obtain ⟨p, kd⟩ := ev; subst h; exact nxt⟩
  exact Softmax.Export.epi_empty_entry hp hX hf hn hr hrt hpc nxt
    (h5.resolve_right fun ⟨f, h⟩ => nu f h) nu

/-- **The entry of the epilogue** of every complete followed execution. -/
theorem Result.entry (hp : Pre Q L m) : Result.Entry Q L m := fun X hX hc hf =>
  { sum := fun g hg lane hv hn t hl hpc => by
      obtain ⟨l, r, -, col, -⟩ := Result.sumEntry hp hX hc hf hg lane hv hn hl hpc
      rwa [← col 0]
    scale := fun g hg lane hv hn t hl hpc pos => by
      obtain ⟨l, r, -, col, rest⟩ := Result.sumEntry hp hX hc hf hg lane hv hn hl hpc
      obtain ⟨mr, a, b, c⟩ := rest (by rwa [← col 0] at pos)
      exact ⟨by rwa [b 0] at a, c⟩
    column := fun g hg lane hv hn d => by
      unfold rowK
      rw [Lib.SoftRow.kState_eq, Lib.SoftRow.kState_eq]
      exact (Lib.SoftRow.kSt_ml_d Q _ _ _ _ d 0 _).2
    empty := fun g hg lane hv hn t hl hpc => Result.emptyEntry hp hX hc hf hg hn hl hpc }

end PTX.Kernels.InklingRelDecode.Proof.Top
