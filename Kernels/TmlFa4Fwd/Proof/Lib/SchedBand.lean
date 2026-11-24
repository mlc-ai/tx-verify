-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads

@[expose] public section

/-! # Where an output-warp state stands in its pass

The scan and ballot positions of a tile choice (`nC`), for every role that runs the output warp's
scheduler. Nothing here reads a role's invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked chosen)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### Positions of the output warp's sites, by pass -/

/-- The position of a tile choice: the first pass's shuffles after its scan ended at round `R`
with ballot `bal`. -/
abbrev nC (R : Nat) (bal : BitVec 64) : Nat := 3 + 7 * (R + 1) + Epilogue.selN bal

/-- The pass of an output-warp site. -/
def ePass : Epilogue.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .exit l => l
  | _ => false

/-- The scan's sites, the ballot and the return: the sites before a pass's choice. -/
def eColl : Epilogue.Site → Bool
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .exit _ => true
  | _ => false

/-- The ballot and the return. -/
def eEnd : Epilogue.Site → Bool
  | .vote _ | .exit _ => true
  | _ => false

/-- `omega` with the choice's position unfolded. -/
local macro "omg" : tactic => `(tactic| ((try unfold nC at *); omega))

theorem scan1_lt {R r o n0 v0 : Nat} {bal : BitVec 64} {k : Epilogue.Scan}
    (hk : k.late = false) (hP : Epilogue.PassStart p L g k.late n0 v0)
    (hR : Epilogue.ScanRound p (g / L.block) k r) (hPk : Picked p L g R bal) (ho : o ≤ 6) :
    n0 + 7 * r + o < nC R bal := by
  rw [hk] at hP
  have h1 := hR.1
  rw [hk] at h1
  have := h1.le_end hPk.1
  have := Epilogue.passStart_n0 hP
  have := (Epilogue.selN_pos bal).1
  omg

theorem pass2_of {n0 v0 : Nat} (hP : Epilogue.PassStart p L g true n0 v0) :
    ∃ R bal, Picked p L g R bal ∧ n0 = nC R bal ∧ v0 = 1 := by
  simp only [Epilogue.PassStart, ↓reduceIte] at hP
  obtain ⟨R, bal, h, rfl, rfl⟩ := hP
  exact ⟨R, bal, h, rfl, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **Where an output-warp state stands in its pass**: a first-pass state is before the CTA's
choice (strictly, unless it holds the choice), and its ballot is the warp's first; a second-pass
state is after the choice. A first-pass return contradicts a choice. -/
theorem eband {dE : Epilogue.D} {ns nv : Nat} (hF : Epilogue.Fits p L g dE ns nv)
    (h0 : dE.site ≠ .start) :
    (ePass dE.site = false ∧ (dE.site.ballot = true → nv = 0) ∧
      ∀ R bal, Picked p L g R bal → ns ≤ nC R bal ∧ (eColl dE.site = true → ns < nC R bal) ∧
        ∀ l, dE.site ≠ .exit l) ∨
    (ePass dE.site = true ∧ 1 ≤ nv ∧ ∃ R bal, Picked p L g R bal ∧ nC R bal ≤ ns ∧
      (eEnd dE.site = true → nC R bal + 7 ≤ ns)) := by
  have hsel := fun b => (Epilogue.selN_pos b).1
  cases hs : dE.site <;> simp only [Epilogue.Fits, hs] at hF
  case start => exact absurd hs h0
  case word k | down k | total k =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    cases hk : k.late
    · refine .inl ⟨by simp [ePass, hk], by simp [Epilogue.Site.ballot], fun R bal hPk => ?_⟩
      have := scan1_lt (o := 6) hk hP hR hPk (by omega)
      exact ⟨by omg, fun _ => by omg, by simp⟩
    · rw [hk] at hP
      obtain ⟨R, bal, hPk, rfl, rfl⟩ := pass2_of hP
      exact .inr ⟨by simp [ePass, hk], by omg, R, bal, hPk, by omg, by simp [eEnd]⟩
  case up k j =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    have := j.isLt
    cases hk : k.late
    · refine .inl ⟨by simp [ePass, hk], by simp [Epilogue.Site.ballot], fun R bal hPk => ?_⟩
      have := scan1_lt (o := 6) hk hP hR hPk (by omega)
      exact ⟨by omg, fun _ => by omg, by simp⟩
    · rw [hk] at hP
      obtain ⟨R, bal, hPk, rfl, rfl⟩ := pass2_of hP
      exact .inr ⟨by simp [ePass, hk], by omg, R, bal, hPk, by omg, by simp [eEnd]⟩
  case vote l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -⟩ := hF
    cases l
    · obtain ⟨rfl, rfl⟩ := Epilogue.passStart_false.mp hP
      refine .inl ⟨rfl, fun _ => by omg, fun R' bal' hPk' => ?_⟩
      obtain rfl := hEV.1.unique hPk'.1
      have := hsel bal'
      exact ⟨by omg, fun _ => by omg, by simp⟩
    · obtain ⟨R', bal', hPk', rfl, rfl⟩ := pass2_of hP
      exact .inr ⟨rfl, by omg, R', bal', hPk', by omg, fun _ => by omg⟩
  case pre l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -⟩ := hF
    cases l
    · obtain ⟨rfl, rfl⟩ := Epilogue.passStart_false.mp hP
      refine .inl ⟨rfl, by simp [Epilogue.Site.ballot], fun R' bal' hPk' => ?_⟩
      obtain rfl := hEV.1.unique hPk'.1
      have := hsel bal'
      exact ⟨by omg, fun _ => by omg, by simp⟩
    · obtain ⟨R', bal', hPk', rfl, rfl⟩ := pass2_of hP
      exact .inr ⟨rfl, by omg, R', bal', hPk', by omg, by simp [eEnd]⟩
  case tiles l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -, hB, -⟩ := hF
    cases l
    · obtain ⟨rfl, rfl⟩ := Epilogue.passStart_false.mp hP
      refine .inl ⟨rfl, by simp [Epilogue.Site.ballot], fun R' bal' hPk' => ?_⟩
      obtain rfl := hEV.1.unique hPk'.1
      obtain rfl := hB.unique hPk'.2.1
      have := hsel dE.bal
      exact ⟨by omg, fun _ => by omg, by simp⟩
    · obtain ⟨R', bal', hPk', rfl, rfl⟩ := pass2_of hP
      exact .inr ⟨rfl, by omg, R', bal', hPk', by omg, by simp [eEnd]⟩
  case exit l =>
    obtain ⟨n0, v0, hP, R, hE, hx⟩ := hF
    cases l
    · obtain ⟨rfl, rfl⟩ := Epilogue.passStart_false.mp hP
      refine .inl ⟨rfl, by simp [Epilogue.Site.ballot], fun R' bal' hPk' => ?_⟩
      exfalso
      obtain rfl := hE.unique hPk'.1
      rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, -, -, hnp⟩
      · exact absurd (hg.symm.trans hPk'.2.2.1) (by simp)
      · obtain rfl := hPk'.2.1.unique hb
        exact hnp rfl hPk'
    · obtain ⟨R', bal', hPk', rfl, rfl⟩ := pass2_of hP
      refine .inr ⟨rfl, ?_, R', bal', hPk', ?_, fun _ => ?_⟩ <;>
        rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega
  all_goals
    have hC : ∃ R bal, Epilogue.ChosenVals p L g R bal dE ns nv := by
      first
        | exact hF
        | (obtain ⟨R, bal, hC, -⟩ := hF; exact ⟨R, bal, hC⟩)
    obtain ⟨R, bal, hPk, -, -, -, -, -, -, hns, hnv⟩ := hC
    refine .inl ⟨rfl, by simp [Epilogue.Site.ballot], fun R' bal' hPk' => ?_⟩
    obtain ⟨hR, hb⟩ := hPk.unique hPk'
    rw [← hR, ← hb]
    exact ⟨by omg, by simp [eColl], by simp⟩

/-- The address of a used-K length word. -/
theorem addrK_toNat (hp : Pre p L m) (hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64) {i : Nat}
    (hi : i < p.batch) :
    (truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase (W i))) + BitVec.ofInt 64 0).toNat =
      p.usedKBase + 4 * i := by
  have hb := Epilogue.batch_lt hp
  have hs : toSigned 32 (r32 (W i)) = i := by
    rw [r32_W (by omega)]; exact toSigned_W (by omega)
  have h4 : toSigned 32 (i32 4) = 4 := by decide
  simp only [Epilogue.vbits, hs, h4]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Nat.reducePow]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
