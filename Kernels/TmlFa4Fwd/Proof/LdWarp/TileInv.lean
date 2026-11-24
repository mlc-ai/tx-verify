-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrLocal
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrStep
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The tile words of a loader lane's blocks

In its blocks a loader lane's coordinates, setup words and used-K word are those of the tile the
first pass picked (`tile_inv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The tile words of the picked tile.** -/
def TileW (p : Params) (L : Launch) (g : Nat) (v : V) : Prop :=
  ∃ R bal, Epilogue.Picked p L g R bal ∧ v.co = (refVL p L g R bal).co ∧
    v.su = setup p L g (refVL p L g R bal) ∧ v.ukw = (refVL p L g R bal).ukw

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

set_option maxHeartbeats 4000000 in
/-- **The tile words at a block state** of a loader lane. -/
theorem tile_inv : ∀ k, k ≤ (X.tr g).length → ∀ b d n,
    Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
    d.site.blk = true → TileW p L g d.v := by
  refine pos_at (I := fun _ d => d.site.blk = true → TileW p L g d.v)
    (fun k b h => by simp [Site.blk, bc] at h)
    (fun k b d n e d' he hσ hub hJ hF hev hnu hn hm IH => ?_) hp hX hg hw
  have hsame : ∀ f, wr d.site f = false → f.same d.v d'.v := hm.keep
  intro hb'
  by_cases hs : d.site = .uk
  · obtain ⟨s, v, kk⟩ := d
    obtain ⟨pc, kind⟩ := e
    simp only at hs
    subst hs
    obtain ⟨-, hFE, hco⟩ : n (.load .commit) = 0 ∧ Epilogue.Fits p L g (toE ⟨.uk, v, kk⟩)
        (n .shfl) (n .vote) ∧ v.co = coords p L g v.sc := id hF
    simp only [Epilogue.Fits, toE, Site.epi] at hFE
    obtain ⟨R, bal, hC, hc0, hc1⟩ := hFE
    obtain ⟨hPk, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := id hC
    simp only [chosen] at htot hgx hcur hbal hpv hnt hc0 hc1
    have hch : chosen v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
      simp only [chosen, hgx, hbal, Epilogue.chosenD]
    have hcoE : coords p L g v.sc = (refVL p L g R bal).co := by
      simp only [coords, refVL, htot, hcur, hpv, hnt, Epilogue.chosenD]
    have h0 : v.sc.c0 = (refVL p L g R bal).sc.c0 := by
      simp only [refVL, hc0]; exact congrArg (Epilogue.qv p) hch
    have h1 : v.sc.c1 = (refVL p L g R bal).sc.c1 := by
      simp only [refVL, hc1]; exact congrArg (fun z => Epilogue.qv p (addi z 1)) hch
    have hcs : chosen v.sc = chosen (refVL p L g R bal).sc := by
      rw [hch]
      rfl
    simp only [succ] at hn
    cases kind <;> simp only [reduceCtorEq] at hn
    split at hn
    · rename_i a bs x hx
      obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      have hy : y = (refVL p L g R bal).ukw := by
        have hx' := expect_uk hp hX he rfl hF hev rfl
        rw [hx'] at hx
        simp only [Except.ok.injEq, Value.bits.injEq, true_and] at hx
        rw [← hx, hch]
        rfl
      subst hy
      have e1 : (pgEnter p L g (D.mk' .uk (withSetup p L g
          { v with ukw := (refVL p L g R bal).ukw })) .prime 0).v.co = v.co := by
        unfold pgEnter D.iteS; dsimp only; split <;> rfl
      have e2 : (pgEnter p L g (D.mk' .uk (withSetup p L g
          { v with ukw := (refVL p L g R bal).ukw })) .prime 0).v.su =
            setup p L g { v with ukw := (refVL p L g R bal).ukw } := by
        unfold pgEnter D.iteS; dsimp only; split <;> rfl
      have e3 : (pgEnter p L g (D.mk' .uk (withSetup p L g
          { v with ukw := (refVL p L g R bal).ukw })) .prime 0).v.ukw =
            (refVL p L g R bal).ukw := by
        unfold pgEnter D.iteS; dsimp only; split <;> rfl
      refine ⟨R, bal, hPk, by rw [e1, hco, hcoE], ?_, e3⟩
      rw [e2]
      have hco' : v.co = (refVL p L g R bal).co := by rw [hco, hcoE]
      simp only [setup, hco', h0, h1, hcs]
    · simp at hn
  · have hb : d.site.blk = true := by
      rcases hm.edge with h | h
      · exact h ▸ hb'
      · have := blk_edges.ok h
        simp only [blkChk, hb', hs, Bool.not_true, Bool.false_or, decide_false,
          Bool.or_false] at this
        exact this
    obtain ⟨R, bal, hP, h1, h2, h3⟩ := IH k le_rfl b d n hσ hub hb
    have hsu : d'.v.su = d.v.su := hsame .su (by
      revert hb hs; cases d.site <;> simp [wr, Site.blk, bc])
    have hco : d'.v.co = d.v.co := hsame .co (by
      revert hb hs; cases d.site <;> simp [wr, Site.blk, bc])
    have huk : d'.v.ukw = d.v.ukw := hsame .ukw (by
      revert hb hs; cases d.site <;> simp [wr, Site.blk, bc])
    exact ⟨R, bal, hP, hco.trans h1, hsu.trans h2, huk.trans h3⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
