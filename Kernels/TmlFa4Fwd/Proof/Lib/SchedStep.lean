-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next

@[expose] public section

/-! # The output warp's step without its shape table

Shared by the roles that run the scheduler. Nothing here reads a role's machine. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {ns nv : Nat}

/-- `Epilogue.fits_next` with the counts of the event given instead of its shape. -/
theorem efits_step {d c : Epilogue.D} {e : Event}
    (hF : Epilogue.Fits p L g d ns nv) (hE : Epilogue.Expect p L g d ns e)
    (h1 : Epilogue.sh e = if d.site.shfl then 1 else 0)
    (h2 : Epilogue.vt e = if d.site.ballot then 1 else 0)
    (hn : Epilogue.succ p L g d e = some (some c)) :
    Epilogue.Fits p L g c (ns + Epilogue.sh e) (nv + Epilogue.vt e) := by
  have hn' : (Epilogue.code p L g (fun _ => .pred false)).next d e = some (some c) := hn
  rw [h1, h2]
  cases hs : d.site <;> simp only [Epilogue.Site.shfl, Epilogue.Site.ballot, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero]
  case start => exact Epilogue.fits_next_start hs hF hn'
  case word k => exact Epilogue.fits_next_word hs hF hE hn'
  case down k => exact Epilogue.fits_next_down hs hF hE hn'
  case up k j => exact Epilogue.fits_next_up hs hF hE hn'
  case total k => exact Epilogue.fits_next_total hs hF hE hn'
  case vote l => exact Epilogue.fits_next_vote hs hF hE hn'
  case pre l => exact Epilogue.fits_next_pre hs hF hE hn'
  case tiles l => exact Epilogue.fits_next_tiles hs hF hE hn'
  case exit l =>
    obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
    subst hs
    simp [Epilogue.succ] at hn
  all_goals
    refine Epilogue.fits_next_write ?_ (by simp [hs]) hF hE hn'
    simp only [Epilogue.Fits, hs] at hF
    first
      | exact hF
      | (obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
