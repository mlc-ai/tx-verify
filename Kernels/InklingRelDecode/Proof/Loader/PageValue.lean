-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Loader.PageAddr
public import Kernels.InklingRelDecode.Proof.Loader.PageRef
public import Kernels.InklingRelDecode.Proof.Lib.PageWord
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Lemmas.Kernel.Source.Launch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

/-- **A block-table load of the loader reads the bytes of the page of its slab.** -/
theorem page_rebuild {Q L m X g k w rest a bs lo hi} {d : D} {t : TState} {ins o}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨d.site.pc, .rd a bs⟩)
    (hat : (code L g w (inputs Q L g rest)).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (fire : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc, .rd a bs⟩ o)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399) :
    ∃ v, rebuild 3 bs = .ok v ∧ Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (if d.site.pc = 2382 then 0 else 1) d.counter v := by
  obtain ⟨j, s, hj, hj31, hse, hs, rfl⟩ := page_acc hp hg hat hc fire hh hr site
  have hz := (Lib.coordinate_bounds hp hg).2.2
  have ro := Frame.LaunchReads.of_forall (hX.asm _ (show Assumptions.inputReadOnly ∈
    Assumptions.all by simp [Assumptions.all]))
  exact ⟨_, Frame.LaunchReads.value (v := b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) s)) hX
    ro he (by rcases site with h | h <;> rw [h] <;> decide) rfl (fun _ _ => trivial)
    (fun j hj => by
      change m ⟨.global, 0, _ + j⟩ = _
      rw [Nat.mul_comm Q.strideBt]
      exact hp.btInput _ hz s hs j hj) (by decide : 0 < 4) rfl,
    ⟨j, hj, hj31, hse ▸ hs, by rw [hse]⟩⟩

/-- **A block-table load of the loader returns the page of its slab.** -/
theorem page_read {Q L m X g k w rest a bs lo hi} {d : D} {t : TState} {ins o}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨d.site.pc, .rd a bs⟩)
    (hat : (code L g w (inputs Q L g rest)).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (fire : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc, .rd a bs⟩ o)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399) {v : Value} (hv : rebuild 3 bs = .ok v) :
    Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
      (if d.site.pc = 2382 then 0 else 1) d.counter v := by
  obtain ⟨v', h1, h2⟩ := page_rebuild hp hX hg he hat hc fire hh hr site
  rw [hv] at h1
  cases Except.ok.inj h1
  exact h2

end PTX.Kernels.InklingRelDecode.Proof.Loader
