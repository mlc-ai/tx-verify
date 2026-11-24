-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.StepAt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's setup words of the picked tile

Standalone fact. From the used-K read on, the two block words the Bias groups depend on (`%r28`, the
tile's K/V blocks, and `%r29`, the blocks the Bias leaves out) are the setup's of the picked tile
(`SuPick`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked qv)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option linter.unusedSimpArgs false

/-- The block words of the picked tile. -/
def SuS (p : Params) (L : Launch) (g : Nat) (v : V) : Prop :=
  ∃ R bal, Picked p L g R bal ∧ v.su.r28 = (setup p L g (refVL p L g R bal)).r28 ∧
    v.su.r29 = (setup p L g (refVL p L g R bal)).r29

/-- The fact at a state. -/
def SuPick (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  (lc dn.1.site = .blk ∨ lc dn.1.site = .p2 → SuS p L g dn.1.v) ∧
    (lc dn.1.site = .drain → dn.2 .commit = 0 ∨ SuS p L g dn.1.v)

/-- The edge check. -/
def suChk (_ : Bool) (s s' : Site) : Bool :=
  match lc s' with
  | .blk => lc s == .blk || s == .uk
  | .p2 => lc s == .blk || lc s == .p2
  | .drain => lc s == .drain && tag s s' != .commit || lc s == .p2 ||
      lc s == .p1 && tag s s' != .commit
  | _ => true

theorem su_edges : Edges suChk := by unfold Edges AllSites; decide +kernel

variable {p : Params} {L : Launch} {g w : Nat}

theorem setup_r29 {v1 v2 : V} (hco : v1.co.row = v2.co.row) (hu : v1.ukw = v2.ukw)
    (h0 : v1.sc.c0 = v2.sc.c0) (h1 : v1.sc.c1 = v2.sc.c1) :
    (setup p L g v1).r29 = (setup p L g v2).r29 := by
  simp only [setup, hco, hu, h0, h1]

/-- The used-K read records the picked tile's words. -/
theorem su_uk {d d' : D} {e : Event} {ns nv nc ns' nv' nc' : Nat} (hs : d.site = .uk)
    (hF : LFits p L g d ns nv nc) (hF' : LFits p L g d' ns' nv' nc') (hb : d'.site.blk = true)
    (hn : succ p L g w d e = some (some d')) : SuS p L g d'.v := by
  obtain ⟨-, -, -, -, ⟨-, hu', -, -⟩⟩ := lfits_blk_of hb hF'
  obtain ⟨s, v, kk⟩ := d
  simp only at hs; subst hs
  unfold LFits at hF; dsimp only [lc] at hF
  obtain ⟨rfl, hFit, hco⟩ := hF
  simp only [Epilogue.Fits, toE, Site.epi] at hFit
  obtain ⟨R, bal, hC, hc0, hc1⟩ := hFit
  obtain ⟨hPk, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := id hC
  simp only [chosen] at htot hgx hcur hbal hpv hnt hc0 hc1
  have hch : chosen v.sc = chosen (Epilogue.chosenD p (g / L.block) R bal) := by
    simp only [chosen, hgx, hbal, Epilogue.chosenD]
  have hcoE : coords p L g v.sc = coords p L g (refVL p L g R bal).sc := by
    simp only [coords, refVL, htot, hcur, hpv, hnt, Epilogue.chosenD]
  obtain ⟨x, rfl⟩ : ∃ x, d' = pgEnter p L g (D.mk' .uk (withSetup p L g { v with ukw := x }))
      .prime 0 := by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [succ, reduceCtorEq] at hn
    split at hn
    · rename_i y _
      unfold word32 at hn
      split at hn
      · rename_i x
        simp only [Option.some.injEq] at hn
        exact ⟨_, hn.symm⟩
      · simp at hn
    · cases hn
  obtain ⟨p1, p2, -⟩ := pgEnter_props (p := p) (L := L) (g := g)
    (D.mk' .uk (withSetup p L g { v with ukw := x })) .prime 0
  obtain ⟨p7, -⟩ := pgEnter_v (p := p) (L := L) (g := g)
    (D.mk' .uk (withSetup p L g { v with ukw := x })) .prime 0
  rw [p7, p1] at hu'
  have hx : x = ukv p (chosen v.sc) := hu'
  refine ⟨R, bal, hC.1, ?_, ?_⟩ <;> rw [p2] <;> simp only [D.mk']
  · apply setup_r28
    · simp only [hco, hcoE, refVL]
    · simp only [refVL, hx, hch]
    · simp only [refVL, hc0]; exact congrArg (qv p) hch
    · simp only [refVL, hc1]; exact congrArg (fun z => qv p (addi z 1)) hch
  · apply setup_r29
    · simp only [hco, hcoE, refVL]
    · simp only [refVL, hx, hch]
    · simp only [refVL, hc0]; exact congrArg (qv p) hch
    · simp only [refVL, hc1]; exact congrArg (fun z => qv p (addi z 1)) hch

/-- **The block words of the picked tile** at every state of a loader lane. -/
theorem su_pick {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : SuPick p L g (d, LdWarp.lcn n) := by
  refine LdWarp.step_at (w := Prologue.warpIndex L g) (I := fun _ dn => SuPick p L g dn) ?_ ?_ ?_
    hp hX hg hw rfl k b d n hσ hub
  · intro b k n _ _ _
    exact ⟨fun h => absurd h (by simp [lc]), fun h => absurd h (by simp [lc])⟩
  · intro k b n d e d' _ _ _ _ hF ⟨ns', nv', hF'⟩ hev hub hn hm h
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    have hsu : d.site ≠ .uk → d'.v.su = d.v.su := fun hs => hm.keep .su (by
      revert hs; cases d.site <;> simp [wr])
    have hS : d.site ≠ .uk → SuS p L g d.v → SuS p L g d'.v := fun h' hl => by
      unfold SuS at hl ⊢; rw [hsu h']; exact hl
    have hne : lc d.site ≠ .req → d.site ≠ .uk := by rintro h' h''; rw [h''] at h'; exact h' rfl
    have hcm : Code.bump (cls L g) (LdWarp.lcn n) e .commit = LdWarp.lcn n .commit +
        if tag d.site d'.site = .commit then 1 else 0 := by
      rw [bump_tag hm]
      cases tag d.site d'.site <;> simp [Tag.cnt]
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · simp only at hl ⊢
      rcases hm.edge with hs | hs
      · simp only at hs
        rw [hs] at hl
        refine hS (hne ?_) (h1 hl)
        rcases hl with hl | hl <;> rw [hl] <;> simp
      · have hc := su_edges.ok hs
        simp only [suChk] at hc
        rcases hl with hl | hl <;> rw [hl] at hc <;>
          simp only [Bool.or_eq_true, beq_iff_eq] at hc
        · rcases hc with hc | hc
          · exact hS (hne (by rw [hc]; simp)) (h1 (.inl hc))
          · exact su_uk hc hF hF' (lc_blk.mp hl) hn
        · rcases hc with hc | hc
          · exact hS (hne (by rw [hc]; simp)) (h1 (.inl hc))
          · exact hS (hne (by rw [hc]; simp)) (h1 (.inr hc))
    · simp only at hl ⊢
      rw [hcm]
      rcases hm.edge with hs | hs
      · simp only at hs
        rw [hs] at hl ⊢
        rw [tag_self]
        simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero]
        exact (h2 hl).imp_right (hS (hne (by rw [hl]; simp)))
      · have hc := su_edges.ok hs
        simp only [suChk, hl, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
        rcases hc with (⟨hc, ht⟩ | hc) | ⟨hc, ht⟩
        · rw [ite_eq_right ht, Nat.add_zero]
          exact (h2 hc).imp_right (hS (hne (by rw [hc]; simp)))
        · exact .inr (hS (hne (by rw [hc]; simp)) (h1 (.inr hc)))
        · rw [ite_eq_right ht, Nat.add_zero]
          simp only [LFits, hc] at hF
          exact .inl hF.1
  · intro _ _ _ h; exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
