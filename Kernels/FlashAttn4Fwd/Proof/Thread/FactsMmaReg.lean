-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWaits
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsStep

@[expose] public section

/-! # The MMA warp never returns to its register request

The MMA warp's successor function never yields its `setmaxnreg` site (`Mma.next_ne_setMaxReg`):
its successor site is that of the site table `sStep` (`next_eq`), which names `setMaxReg` for no
site and outcome (`check_noReg`). This is the MMA warp's part of `Cross.NoRegReentry`
(`Cross.NoRegReentry_mma`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Mma

/-- No step of the site table enters the register request. -/
theorem check_noReg : allSites.all (fun s => [false, true].all fun x => [false, true].all fun y =>
    !decide ((sStep s x y).1 = .setMaxReg)) = true := by
  decide +kernel

/-- The MMA warp's successor is never its register request. -/
theorem next_ne_setMaxReg {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  intro h
  have hc := all_of check_noReg d.site (outcome L g e) (cond L g d)
  rw [← (next_eq hn).1, h] at hc
  simp at hc

end Mma

/-- **The MMA warp's part of `Cross.NoRegReentry`**: a step from an MMA state never reaches a
register request. -/
theorem Cross.NoRegReentry_mma {L : Launch} {g : Nat} {d : Mma.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.mma d)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  simp only [code] at h
  rcases hm : Mma.next L g d e with _ | _ | d'
  · rw [hm] at h
    cases h
  · rw [hm] at h
    cases h
  · rw [hm] at h
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    have hs := Mma.next_ne_setMaxReg hm
    simp only [nextKind]
    cases hd : d'.site <;> simp_all [mmaKind]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
