-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part033
public import Kernels.TmlFa4Fwd.Flow.Code.Part034
public import Kernels.TmlFa4Fwd.Flow.Code.Part035
public import Kernels.TmlFa4Fwd.Flow.Code.Part036
public import Kernels.TmlFa4Fwd.Flow.Code.Part037
public import Kernels.TmlFa4Fwd.Flow.Code.Part038
public import Kernels.TmlFa4Fwd.Flow.Code.Part039
public import Kernels.TmlFa4Fwd.Flow.Code.Part040
public import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

structure ElectSite where
  pc : Nat
  result : Option Nat
  pred : Nat

/-- All MMA issue elections and release elections in program order. -/
def electSite : Fin 20 → ElectSite
  | 0 => ⟨2153, none, 9636⟩
  | 1 => ⟨2205, (some 2561), 382⟩
  | 2 => ⟨2215, none, 9653⟩
  | 3 => ⟨2267, (some 2566), 384⟩
  | 4 => ⟨2271, (some 2567), 386⟩
  | 5 => ⟨2311, none, 9671⟩
  | 6 => ⟨2363, none, 9682⟩
  | 7 => ⟨2415, (some 2593), 390⟩
  | 8 => ⟨2426, none, 9699⟩
  | 9 => ⟨2459, (some 2599), 392⟩
  | 10 => ⟨2464, none, 9709⟩
  | 11 => ⟨2516, (some 2603), 394⟩
  | 12 => ⟨2520, (some 2604), 396⟩
  | 13 => ⟨2534, (some 2607), 400⟩
  | 14 => ⟨2538, (some 2608), 402⟩
  | 15 => ⟨2562, none, 9727⟩
  | 16 => ⟨2602, none, 9738⟩
  | 17 => ⟨2635, (some 2630), 404⟩
  | 18 => ⟨2639, (some 2631), 406⟩
  | _ => ⟨2643, (some 2632), 408⟩

private theorem electCode (i : Fin 20) :
    let site := electSite i
    kernel.code[site.pc]? = some
      ⟨none, .warp ⟨.elect, none, [site.result, some site.pred], [], some (.imm (-1))⟩⟩ := by
  fin_cases i
  · exact Flow.code_2153
  · exact Flow.code_2205
  · exact Flow.code_2215
  · exact Flow.code_2267
  · exact Flow.code_2271
  · exact Flow.code_2311
  · exact Flow.code_2363
  · exact Flow.code_2415
  · exact Flow.code_2426
  · exact Flow.code_2459
  · exact Flow.code_2464
  · exact Flow.code_2516
  · exact Flow.code_2520
  · exact Flow.code_2534
  · exact Flow.code_2538
  · exact Flow.code_2562
  · exact Flow.code_2602
  · exact Flow.code_2635
  · exact Flow.code_2639
  · exact Flow.code_2643

private theorem electRange (i : Fin 20) : 1904 ≤ (electSite i).pc ∧ (electSite i).pc < 2768 := by
  fin_cases i <;> decide

def electState (l : Launch) (g : Nat) (t : TState) (i : Fin 20) (leader : Nat) : TState :=
  let site := electSite i
  let u := site.result.elim t (fun r => setReg t r (b32 leader))
  next (setReg u site.pred (.pred (laneOf l g == leader)))

/-- Each MMA election uses the full warp mask. -/
theorem electTemplate {l : Launch} {g : Nat} (i : Fin 20)
    {t : TState} {F : List (Nat × Value)} (ht : At t (electSite i).pc F) :
    out kernel Assumptions.all l g t =
      .ev (.elect (2 ^ 32 - 1) (electState l g t i)) := by
  have hRange := electRange i
  rw [out_eq_core (by rw [ht.1]; exact hRange.1) (by rw [ht.1]; exact hRange.2),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact electCode i) rfl rfl]
  change Out.ev (electTmpl l g t (electSite i).result (electSite i).pred (.imm (-1))) = _
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hMember : electMember (2 ^ 32 - 1) (laneOf l g) := by
    refine ⟨hLane, ?_⟩
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hLane
  have hRead : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 (2 ^ 32 - 1)) := rfl
  have hReadNat : (BitVec.ofNat 64 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 := rfl
  simp only [electTmpl, hRead, hReadNat, hMember, ↓reduceIte]
  let result := (electSite i).result
  change Out.ev (.elect _ (fun leader =>
    next (setReg (match result with | none => t | some r => setReg t r (b32 leader))
      (electSite i).pred (.pred (laneOf l g == leader))))) =
    Out.ev (.elect _ (fun leader =>
      next (setReg (result.elim t (fun r => setReg t r (b32 leader)))
        (electSite i).pred (.pred (laneOf l g == leader)))))
  cases result <;> rfl

/-- Any two observed full-mask MMA elections in a warp have the same leader. -/
theorem sameLeader {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g h a b pc pc' inst inst' leader leader' : Nat} (hWarp : SameWarp l g h)
    (ha : X.get (g, a) = some ⟨pc, .elect (2 ^ 32 - 1) inst leader⟩)
    (hb : X.get (h, b) = some ⟨pc', .elect (2 ^ 32 - 1) inst' leader'⟩) :
    leader = leader' :=
  hX.elect.2.2 _ _ _ _ _ _ _ _ _ ha hb hWarp

/-- The election continuation preserves any frame that omits its two destinations. -/
theorem electStateFrame {l : Launch} {g : Nat} (i : Fin 20)
    {t : TState} {F : List (Nat × Value)} (ht : At t (electSite i).pc F)
    (leader : Nat) (hPred : ∀ pair ∈ F, pair.1 ≠ (electSite i).pred)
    (hResult : ∀ pair ∈ F, pair.1 ∉ (electSite i).result.toList) :
    At (electState l g t i leader) ((electSite i).pc + 1)
      (((electSite i).pred, .pred (laneOf l g == leader)) :: F) := by
  let u := (electSite i).result.elim t (fun r => setReg t r (b32 leader))
  have hu : At u (electSite i).pc F := by
    dsimp only [u]
    cases h : (electSite i).result with
    | none => exact ht
    | some r =>
      refine ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_update ht.2.2.2.2 ?_⟩
      intro pair hp he
      have h' := hResult pair hp
      rw [he, h] at h'
      exact h' (by simp)
  exact hu.set hPred

end
end PTX.Kernels.TmlFa4Fwd.Mma
