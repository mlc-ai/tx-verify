-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
public import Kernels.TmlFa4Fwd.Proof.CorrectionReciprocal
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleSignal
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Connect a statistics read's recorded bytes to the loaded register, preserving the frame. -/
theorem observeStatsValuePrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {o : Option TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (kind : StatsKind) (value : ℝ)
    (ht : At t (statsPc stage kind) F)
    (hAddress : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ statsReg stage kind)
    (hRead : ∀ bs, X.get (g, pos) = some
      ⟨statsPc stage kind, .rd {loc := statsLoc l g stage kind, size := 4} bs⟩ →
      bs = (fl value).toBytes.map some)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    ∃ s, X.get (g, pos) = some ⟨statsPc stage kind,
        .rd {loc := statsLoc l g stage kind, size := 4} ((fl value).toBytes.map some)⟩ ∧
      At s (statsPc stage kind + 1) ((statsReg stage kind, fl value) :: F) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨bs, he, hR⟩ := observeStatsPrefix hp stage kind (ht.mono ⟨hAddress, trivial⟩) hr hMore
  have hBytes := hRead bs he
  rw [hBytes] at he hR
  let s := next (setReg t (statsReg stage kind) (fl value))
  have hRebuilt : rebuild 3 ((fl value).toBytes.map some) = .ok (fl value) :=
    rebuild_scalar (by change 0 < 4; decide) rfl
  have hActual : afterLoad t [statsReg stage kind] ((fl value).toBytes.map some) = s := by
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuilt]
    simp [s, next, setReg, ht.2.1, ht.2.2.1]
  exact ⟨s, he, ht.set hFresh, hActual ▸ hR⟩

/-- Connect a statistics read's recorded bytes to the loaded register, preserving the frame. -/
theorem observeStatsValue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (kind : StatsKind) (value : ℝ)
    (ht : At t (statsPc stage kind) F)
    (hAddress : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ statsReg stage kind)
    (hRead : ∀ bs, X.get (g, pos) = some
      ⟨statsPc stage kind, .rd {loc := statsLoc l g stage kind, size := 4} bs⟩ →
      bs = (fl value).toBytes.map some)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ s, X.get (g, pos) = some ⟨statsPc stage kind,
        .rd {loc := statsLoc l g stage kind, size := 4} ((fl value).toBytes.map some)⟩ ∧
      At s (statsPc stage kind + 1) ((statsReg stage kind, fl value) :: F) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 1)) none :=
  observeStatsValuePrefix hp stage kind value ht hAddress hFresh hRead hr
    (by intro h; rw [h] at hr; cases hr)

def finalStatsFacts (stage : Fin 2) (sum max : ℝ) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (statsReg stage .maximum, fl max) :: (statsReg stage .sum, fl sum) :: F

def finalStatsReleaseDst (stage : Fin 2) : Nat := 9258 + 132 * stage.val

private theorem finalStatsReleaseCode (stage : Fin 2) :
    kernel.code[reciprocalPc stage - 1]? = some ⟨none,
      .mbarArrive (rescaleReuseReg (1 - stage)) 0 (.imm 0) (.reg 6498) false true .cta
        (some (finalStatsReleaseDst stage))⟩ := by
  fin_cases stage
  · exact Flow.code_8468
  · exact Flow.code_8764

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat} {t : TState}
    {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2) (sum maximum : ℝ)
    (ht : At t (statsBarrierPc stage false) F)
    (hBarrier : (statsBarrierReg stage, b32 (statsBarrierId l g stage)) ∈ F)
    (hAddress : (1627, b32 (l.sharedBase + 4 * rowOf l g)) ∈ F) (hCount : (6498, b32 1) ∈ F)
    (hBase : (rescaleReuseReg (1 - stage), b32 (rescaleReuseLoc l g (1 - stage)).addr) ∈ F)
    (hFresh : ∀ rv ∈ F, rv.1 ≠ statsReg stage .sum ∧ rv.1 ≠ statsReg stage .maximum ∧
      rv.1 ≠ finalStatsReleaseDst stage ∧
      rv.1 ∉ [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage])
    (hSum : ∀ bs, X.get (g, pos + 1) = some
      ⟨statsPc stage .sum, .rd {loc := statsLoc l g stage .sum, size := 4} bs⟩ →
      bs = (fl sum).toBytes.map some)
    (hMax : ∀ bs, X.get (g, pos + 2) = some
      ⟨statsPc stage .maximum, .rd {loc := statsLoc l g stage .maximum, size := 4} bs⟩ →
      bs = (fl maximum).toBytes.map some)
include hp stage sum maximum ht hBarrier hAddress hCount hBase hFresh hSum hMax

/-- The correction's actual last statistics rendezvous reads the row's sum and maximum,
releases that slot, and computes the guarded normalization reciprocal. -/
theorem observeFinalStatsWithPredicate
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u, X.get (g, pos) = some
      ⟨statsBarrierPc stage false, .bar (statsBarrierId l g stage) (some 64) .sync⟩ ∧
      X.get (g, pos + 1) = some ⟨statsPc stage .sum,
        .rd {loc := statsLoc l g stage .sum, size := 4} ((fl sum).toBytes.map some)⟩ ∧
      X.get (g, pos + 2) = some ⟨statsPc stage .maximum,
        .rd {loc := statsLoc l g stage .maximum, size := 4} ((fl maximum).toBytes.map some)⟩ ∧
      X.get (g, pos + 3) = some ⟨reciprocalPc stage - 1,
        .arrive (rescaleReuseLoc l g (1 - stage)) 0 1 true .cta⟩ ∧
      At u (reciprocalPc stage + 3)
        ((reciprocalReg stage, fl (1 / (if sum = 0 then 1 else sum))) ::
          (reciprocalPred stage, .pred (decide (sum ≠ 0))) :: finalStatsFacts stage sum maximum F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 4)) none := by
  obtain ⟨hb, hs, hR⟩ := observeStatsBarrier hp stage false ht (holds_mem ht.2.2.2.2 hBarrier) hr
  have hs' : At (next t) (statsPc stage .sum) F := by fin_cases stage <;> exact hs
  obtain ⟨s, heSum, hs, hS⟩ := observeStatsValue hp stage .sum sum hs'
    (holds_mem hs'.2.2.2.2 hAddress) (fun rv hm => (hFresh rv hm).1) hSum hR
  have hAtMax : At s (statsPc stage .maximum) ((statsReg stage .sum, fl sum) :: F) := by
    fin_cases stage <;> exact hs
  have hFreshSum {rv : Nat × Value}
      (hm : rv ∈ (statsReg stage .sum, fl sum) :: F) : rv.1 ≠ statsReg stage .maximum := by
    rcases List.mem_cons.mp hm with rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh rv hm).2.1
  obtain ⟨v, heMax, hv, hV⟩ := observeStatsValue hp (pos := pos + 2) stage .maximum maximum
    hAtMax (holds_mem hs.2.2.2.2.2 hAddress) (fun _ hm => hFreshSum hm) hMax hS
  have hAtRel : At v (reciprocalPc stage - 1) (finalStatsFacts stage sum maximum F) := by
    fin_cases stage <;> exact hv
  have hModel : out kernel Assumptions.all l g v = out kernel [] l g v := by
    apply Assumptions.out_all_eq_nil _ _ _ (hAtRel.1.symm ▸ finalStatsReleaseCode stage) rfl
    all_goals rw [hAtRel.1]; fin_cases stage <;> dsimp only <;> decide
  have hW (rv : Nat × Value) (hm : rv ∈ finalStatsFacts stage sum maximum F) :
      rv.1 ≠ finalStatsReleaseDst stage := by
    simp only [finalStatsFacts, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh rv hm).2.2.1
  have hAddressForm : rescaleReuseLoc l g (1 - stage) =
      ⟨.shared, g / l.block, (rescaleReuseLoc l g (1 - stage)).addr⟩ := rfl
  have hBound : (rescaleReuseLoc l g (1 - stage)).addr + 0 < 2 ^ 32 := by
    have hl := hp.shared.2.1
    fin_cases stage <;> simp only [rescaleReuseLoc] <;> omega
  have hAlign : ((rescaleReuseLoc l g (1 - stage)).addr + 0) % 8 = 0 := by
    have hl := hp.shared.1
    fin_cases stage <;> simp only [rescaleReuseLoc] <;> omega
  obtain ⟨w, hw, heRel, hTail⟩ := observeCorrectionRelease
    (base := (rescaleReuseLoc l g (1 - stage)).addr) (off := 0) (pos := pos + 3)
    hAtRel hModel (finalStatsReleaseCode stage)
    (holds_mem hAtRel.2.2.2.2.2.2 hBase) (holds_mem hAtRel.2.2.2.2.2.2 hCount)
    hBound hAlign hW hV
  have hAtRecip : At w (reciprocalPc stage) (finalStatsFacts stage sum maximum F) := by
    fin_cases stage <;> exact hw
  have hKeep (rv : Nat × Value) (hm : rv ∈ finalStatsFacts stage sum maximum F) :
      rv.1 ∉ [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage] := by
    simp only [finalStatsFacts, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh rv hm).2.2.2
  obtain ⟨u, hu, hU⟩ := finalReciprocalWithPredicate (pos := pos + 4) stage hAtRecip
    hAtRecip.2.2.2.2.2.1 rfl hKeep hTail
  have heRel' : X.get (g, pos + 3) = some ⟨reciprocalPc stage - 1,
      .arrive (rescaleReuseLoc l g (1 - stage)) 0 1 true .cta⟩ := by
    rw [hAddressForm]
    simpa only [Nat.add_zero] using heRel
  exact ⟨u, hb, heSum, heMax, heRel', hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
