-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
public import Lemmas.Flow.Recip
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

def rescalePredReg (stage : Fin 2) : Nat := 731 + 2 * stage.val

def rescaleVoteReg (stage : Fin 2) : Nat := if stage.val = 0 then 5979 else 6237

private def compareInstr (stage : Fin 2) : Instr :=
  ⟨none, .float {
    op := .setp (.ord .lt) none
    ty := ⟨.f32, 1⟩
    dsts := [some (rescalePredReg stage)]
    srcs := [.reg (statsReg stage .alpha), .f32imm 1065353216] }⟩

private theorem compareCode (stage : Fin 2) :
    kernel.code[statsPc stage .alpha + 1]? = some (compareInstr stage) := by
  fin_cases stage
  · exact Flow.code_8008
  · exact Flow.code_8227

private def ballotInstr (stage : Fin 2) : Instr :=
  ⟨none, .warp
    ⟨.vote .ballot false, some (.int .b 32), [some (rescaleVoteReg stage)],
      [.reg (rescalePredReg stage)], some (.imm (-1))⟩⟩

private theorem ballotCode (stage : Fin 2) :
    kernel.code[statsPc stage .alpha + 2]? = some (ballotInstr stage) := by
  fin_cases stage
  · exact Flow.code_8009
  · exact Flow.code_8228

/-- A finite coefficient determines the lane's ballot input before the
warp rendezvous. The comparison and its ballot template are local. -/
theorem rescaleBallotNext {p : Params} {l : Launch} {m : Mem0} {g : Nat} {t : TState}
    (hp : Pre p l m) (stage : Fin 2) {value : Value} {x : ℝ}
    {F : List (Nat × Value)}
    (ht : At t (statsPc stage .alpha + 1) ((statsReg stage .alpha, value) :: F))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ rescalePredReg stage ∧ rv.1 ≠ rescaleVoteReg stage)
    (hVal : valFloat .f32 value = .ok x) :
    ∃ s k, s.pc = statsPc stage .alpha+2 ∧
      Next kernel Assumptions.all l g t s (.vote (2^32-1) (decide (x < 1)) k) ∧
      ∀ word, At (k word) (statsPc stage .alpha+3)
        ((rescaleVoteReg stage,b32 word.toNat)::(statsReg stage .alpha,value)::F) := by
  let s := next (setReg t (rescalePredReg stage) (.pred (x < 1)))
  have hSeg : t.pc ∉ Assumptions.swExp2Sites := by rw [ht.1]; fin_cases stage <;> decide
  have hIdeal : IdealAt Assumptions.numeric (.setp .f32) l g t :=
    idealAt_head (by decide) (Assumptions.numeric_segSites.pc hSeg).tail
  have hCode := ht.1.symm ▸ compareCode stage
  have hNumeric : out kernel Assumptions.numeric l g t = .tau s := by
    have hCmp := (fsetp_imm hCode (Or.inl rfl) (by decide) hIdeal ht.2.2.2.1 ht.2.2.2.2.1
      valFloat_one).1 x hVal
    simpa only [s, erealCompare, EReal.coe_lt_coe_iff] using hCmp
  have hStep : Tau kernel Assumptions.all l g t s := by
    change out kernel Assumptions.all l g t = .tau s
    apply Eq.trans (Assumptions.out_all_eq_numeric ?_ ?_) hNumeric
    all_goals rw [ht.1]; fin_cases stage <;> decide
  have hState : At s (statsPc stage .alpha + 2)
      ((rescalePredReg stage, .pred (x < 1)) :: (statsReg stage .alpha, value) :: F) := by
    apply ht.set
    intro pair h
    rcases List.mem_cons.mp h with rfl | h
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh pair h).1
  have hC := hState.1.symm ▸ ballotCode stage
  have hOut : out kernel Assumptions.all l g s = out kernel [] l g s := by
    apply Assumptions.out_all_eq_nil _ _ _ hC rfl
    all_goals rw [hState.1]; fin_cases stage <;> decide
  let k := fun word : BitVec 32 => next (setReg s (rescaleVoteReg stage) (b32 word.toNat))
  have hNext : Next kernel Assumptions.all l g t s (.vote (2 ^ 32 - 1) (decide (x < 1)) k) := by
    refine ⟨.single hStep, ?_⟩
    rw [hOut]
    unfold out
    rw [hState.2.2.2.1, hC]
    change Out.ev (voteTmpl l g s (rescaleVoteReg stage)
      (rescalePredReg stage) false (.imm (-1))) = _
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    simp [voteTmpl, readPred, readReg, hState.2.2.2.2.1, hBlock, readBits, pure, Except.pure,
      b32, k]
    rfl
  refine ⟨s,k,hState.1,hNext,?_⟩
  intro word
  have hs : At s (statsPc stage .alpha + 2) ((statsReg stage .alpha, value) :: F) :=
    hState.mono hState.2.2.2.2.2
  apply hs.set
  intro pair h
  rcases List.mem_cons.mp h with rfl | h
  · fin_cases stage <;> dsimp only <;> decide
  · exact (hFresh pair h).2

/-- A finite alpha reaching either correction predicate contributes exactly `alpha < 1`
to the actual full-mask rescale ballot. -/
theorem observeRescaleBallot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos ordinal : Nat} {t : TState} (hp : Pre p l m) (stage : Fin 2) {value : Value} {x : ℝ}
    {F : List (Nat × Value)}
    (ht : At t (statsPc stage .alpha + 1) ((statsReg stage .alpha, value) :: F))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ rescalePredReg stage ∧ rv.1 ≠ rescaleVoteReg stage)
    (hVal : valFloat .f32 value = .ok x)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none)
    (hOrdinal : ((X.tr g).take pos).countP isFullWarpVote = ordinal) :
    ∃ bs u, X.get (g, pos) =
        some ⟨statsPc stage .alpha + 2, .vote (2 ^ 32 - 1) (decide (x < 1)) bs⟩ ∧
      X.MaskK voteClass (g, pos) (2 ^ 32 - 1) ordinal ∧
      At u (statsPc stage .alpha + 3)
        ((rescaleVoteReg stage, b32 bs.toNat) :: (statsReg stage .alpha, value) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨s,k,hSite,hNext,hReturn⟩ := rescaleBallotNext (g := g) hp stage ht hFresh hVal
  obtain ⟨word,he,hOrd,hRun⟩ := hNext.ballot_at hr hOrdinal
  exact ⟨word,k word,hSite ▸ he,hOrd,hReturn word,hRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
