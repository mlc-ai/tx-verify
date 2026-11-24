-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape

@[expose] public section

/-! # The successors of the softmax machine's states: definitions

Every step of the softmax machine (`succ_cases`) either stays at its site with its values and
fires no event of a ledger class (a failed poll, an element of a bias load before the last, the
implicit wait of a delayed P store), or moves to a listed successor of its site (`nexts`) at the
successor's sub-step. A move from a site that does not end a round keeps the parities and the
round counters when it lands in a round or after the rounds, and the scan and the used-K length
when it lands in a round or at the final stores; a move to an end state of a lane without a tile
sets the statistics parity to 1 or comes from such a state; and a move from the election goes to
the elected lane's arrival exactly when the lane won. One theorem per family of sites
(`RefSucc*.lean`, the correction warps' method). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The parities and the round counters are unchanged. -/
def frameP (v v' : V) : Prop :=
  v'.spar = v.spar ∧ v'.ppar = v.ppar ∧ v'.bpar = v.bpar ∧ v'.nb = v.nb ∧ v'.pl = v.pl

/-- The scan and the used-K length (all the tile's words read) are unchanged. -/
def frameT (v v' : V) : Prop := v'.sc = v.sc ∧ v'.ukw = v.ukw

/-- The sub-step a successor starts at: a plain load's implicit wait at 1, others at 0. -/
def kIn : Site → Fin 4
  | .sldw _ => 1
  | _ => 0

def Site.isPel : Site → Bool
  | .pel _ => true
  | _ => false

def Site.isSldw : Site → Bool
  | .sldw _ => true
  | _ => false

variable {p : Params} {L : Launch} {g : Nat}

/-- An event that a staying step fires: a failed poll, a read (an element of a bias load), or
the implicit wait of a delayed P store (sub-step 0). -/
def NoCls (d : D) (e : Event) : Prop :=
  (∃ m par a sc, e.kind = .wait m par false a sc) ∨ (∃ a bs, e.kind = .rd a bs) ∨
    (d.site.delayed = true ∧ d.k = 0)

/-- The step facts of a move to a listed successor. -/
def MoveFacts (L : Launch) (g : Nat) (d d' : D) (e : Event) : Prop :=
  d'.site ∈ nexts (lz L g) d.site ∧ d'.k = kIn d'.site ∧
    (d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) ∧
    (d.site.delayed = true → d.k ≠ 0) ∧
    (d.site.special = false →
      (inBias d'.site.pos = true ∨ inPlain d'.site.pos = true ∨ afterR d'.site = true) →
      frameP d.v d'.v) ∧
    (d.site.special = false →
      (inBias d'.site.pos = true ∨ inPlain d'.site.pos = true ∨ finR d'.site = true) →
      frameT d.v d'.v) ∧
    (d'.site.noTile = true → d'.v.ppar = i32 1 ∨ (d.site.noTile = true ∧ d'.v.ppar = d.v.ppar)) ∧
    (d.site.isPel = true → ∀ m inst ld, e.kind = .elect m inst ld →
      (d'.site.isParr2 = true ↔ laneOf L g = ld))

/-- What a step from `d` to `d'` on `e` satisfies: it stays at its site with its values, or it
moves to a listed successor with the step facts. -/
abbrev StepConcl (L : Launch) (g : Nat) (d d' : D) (e : Event) : Prop :=
  (d'.site = d.site ∧ d'.v = d.v ∧ d.site.isSldw = false ∧ NoCls d e) ∨ MoveFacts L g d d' e

/-- The steps from the states at site `s`. -/
def SuccOk (p : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (v : V) (k : Fin 4) (acc : List Value) (e : Event) (d' : D),
    succ p L g ⟨s, v, k, acc⟩ e = some (some d') → StepConcl L g ⟨s, v, k, acc⟩ d' e

set_option hygiene false in
/-- Unfold a step and split it into its branches, each with its successor substituted. -/
macro "sc_split" : tactic => `(tactic| (
  simp only [succ, word32, scAt, D.mk', D.ite, afterTotal, loopHead, scanExit, passStart,
    afterTiles, afterRound, afterFirst, afterBias, afterPlain, plainEntry, afterLoads, pstNext,
    Epilogue.Scan.late, Epilogue.loopOf, Fin.isValue, ↓reduceIte, Bool.false_eq_true] at h
  repeat' (first | (cases h; done) | split at h |
    simp only [Option.map_some, Option.map_none, reduceCtorEq] at h)
  all_goals first | (cases h; done) | (cases h) | skip))

set_option hygiene false in
/-- Close one branch. -/
macro "sc_close" : tactic => `(tactic| (
  first
    | (left; exact ⟨rfl, rfl, rfl, Or.inl ⟨_, _, _, _, ‹_›⟩⟩)
    | (left; refine ⟨rfl, rfl, rfl, Or.inl ?_⟩
       rename_i hk hok; simp only [Bool.not_eq_true] at hok; subst hok; exact ⟨_, _, _, _, hk⟩)
    | (left; exact ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨_, _, ‹_›⟩)⟩)
    | (left; exact ⟨rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, ‹_›⟩)⟩)
    | (right
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       · first
           | (dsimp only; generalize lz L g = b; cases b <;> decide)
           | (simp_all [nexts, lz]; done)
       · rfl
       · first
           | (intro hf; exact absurd hf (by dsimp only; decide))
           | (intro _ m par a sc hw; simp_all; done)
       · first
           | (intro hf; exact absurd hf (by dsimp only; decide))
           | (intro _ hk0; simp_all; done)
       · first
           | (intro _ _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
           | (intro _ hr; exact absurd hr (by dsimp only; decide))
           | (intro hs _; exact absurd hs (by dsimp only; decide))
       · first
           | (intro _ _; exact ⟨rfl, rfl⟩)
           | (intro _ hr; exact absurd hr (by dsimp only; decide))
           | (intro hs _; exact absurd hs (by dsimp only; decide))
       · first
           | (intro h; exact absurd h (by dsimp only; decide))
           | (intro _; exact Or.inl rfl)
           | (intro _; exact Or.inr ⟨rfl, rfl⟩)
       · first
           | (intro hf; exact absurd hf (by dsimp only; decide))
           | (intro _ m inst ld' hk; simp_all [Site.isParr2]; done))))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
