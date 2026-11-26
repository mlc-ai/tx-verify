-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot

@[expose] public section

/-! # An A byte of a PV MMA is in the P tile

`mmaFoot_pvA`: a byte `s.byteLoc .a idx` of a PV MMA (D below column 256) lies in the P tile, the
first 8192 bytes of `pExchange` of the MMA's CTA. `mmaFoot_pv` (`Mma/Export/Foot.lean`) places an
operand byte in the dequantized tile or the P tile; here the event is the PV MMA, so only the
second place is possible. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MmaFoot

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV MMA's A byte is in the P tile of its CTA.** -/
theorem mmaFoot_pvA (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc bb idx : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {l : Loc} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hat : MbarRow.MmaAt L g pc)
    (hbb : bb < 256) (hl : s.byteLoc .a idx = some l) :
    MemRow.LocIn L (g / L.block) .pExchange l ∧ l.addr < L.sharedBase + 204800 + 8192 := by
  obtain ⟨-, hlo, hhi⟩ := id hat
  have hb : 0 < L.block := by rw [hp.block]; decide
  have hcta : L.ctaGroup (g / L.block) .one = some [g / L.block] :=
    ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)
  have hB128 := Mma.base_128 hp 0 rfl
  simp only [Nat.add_zero] at hB128
  obtain ⟨d, hR, ⟨-, hE⟩, hlv, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case pv i =>
    rcases hE with ⟨s', hk, haT, hdi, ⟨ctas, hct, hcl, hch⟩, hAd, -⟩ | ⟨f, hf⟩
    · cases hk
      obtain ⟨h, hh, rfl⟩ : ∃ h < 2, pha = Arith32.W h := by
        simp only [Mma.RefCore, Mma.Site.inLoop, ↓reduceIte] at hc
        obtain ⟨⟨-, -, -, -, -, hpha, -, -⟩, -⟩ := hc
        exact ⟨_, Nat.mod_lt _ (by decide), hpha⟩
      rw [pvD_eq hdi, show pvD.group = .one from rfl, hcta] at hct
      cases hct
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hcl hch
      rw [Mma.pvAW_decode hp i.isLt] at hAd
      obtain ⟨h1, h2, h3, h4⟩ := prob_foot (pvD_eq hdi) i.isLt (Option.some.inj hAd).symm haT hl
      refine ⟨⟨h1, ?_, by simpa [Region.lo] using h3, ?_⟩, by omega⟩
      · rcases h2 with h2 | h2
        · exact h2.trans hcl.symm
        · exact h2.trans hch.symm
      · simp only [Region.lo, Region.size]
        omega
    · cases hf
  case qk i =>
    rcases hE with ⟨s', hk, -⟩ | ⟨f, hf⟩
    · cases hk
      exact absurd hbb (by decide)
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
