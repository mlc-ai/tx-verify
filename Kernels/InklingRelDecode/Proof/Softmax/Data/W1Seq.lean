-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Run
public import Lemmas.Flow.BranchU
import Kernels.InklingRelDecode.Flow.Code.Part020
import Kernels.InklingRelDecode.Flow.Code.Part022
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps

@[expose] public section

/-! # The first window on a register file, along its three paths

From the registers the window reads (`kW1`, under any values `V`) the three paths of pcs 1299 to
1837 (skipping the bias at pc 1302, adding it without a mask at pc 1466, or adding it and masking)
reach pc 1838 with the registers `kFin` read under `vFin V`: the value of each is that of the path
the two predicates (`pick96`, `pick97`: the registers `p96` and `p97` of the runs) choose. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section
variable {L : Launch} {g : Nat}

/-- The registers the window reads: the three launch constants (482, 483, 484), the halves of the
head (1, 2), the round's base and number (1912, 1913), the 32 bias words, the column offsets, the
32 pairs of positions and the 32 pairs of scores. -/
def kW1 : List Nat := [1, 2, 482, 483, 484, 1912, 1913] ++ List.range' 1916 32 ++ [1956, 1960] ++
  List.range' 1961 32 ++ List.range' 2447 32

/-- A predicate register's value as a Boolean. -/
def predBool : Value → Bool
  | .pred b => b
  | _ => false

/-- **A conditional branch on a register fact** whose two sides continue under the register's
value: a register that is no predicate faults the branch. -/
theorem bra_split {pc p target c : Nat} {uni : Bool} {K : List Nat} {V : Nat → Value}
    {G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target uni⟩) (hp : p ∈ K)
    (hL : ∀ t a, a ∈ Assumptions.all → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc Assumptions.all pc)
    (hT : ∀ b, V p = .pred b → b = true → SegU kernel Assumptions.all L g target
      (factsFrom K V) c G)
    (hN : ∀ b, V p = .pred b → b = false → SegU kernel Assumptions.all L g (pc + 1)
      (factsFrom K V) c G) :
    SegU kernel Assumptions.all L g pc (factsFrom K V) c G := by
  intro t ht
  obtain ⟨hP, hS0, hAc, hFl, hR⟩ := ht
  have hc' : kernel.code[t.pc]? = some ⟨some (p, false), .bra target uni⟩ := hP ▸ hc
  have hr := holds_mem hR (mem_factsFrom (val := V) hp)
  cases hv : V p with
  | pred b =>
    have h' : At t pc ((p, .pred b) :: factsFrom K V) := ⟨hP, hS0, hAc, hFl, by rw [← hv]; exact hr,
      hR⟩
    cases b
    · exact SegU.comp (SegU.branch false hc hL hA) (hN false hv rfl) t h'
    · exact SegU.comp (SegU.branch true hc hL hA) (hT true hv rfl) t h'
  | _ =>
    rw [hv] at hr
    exact .inr (Machine.dead_of_ub (f := .typeMismatch)
      (by simp [out, hFl, hc', guardHolds, readReg, hr, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, Except.pure, pure]))

/-- A segment's goal restated for fewer registers whose values are another function's. -/
theorem fin_of {s b : Nat} {F : List (Nat × Value)} {K Kf : List Nat} {W Wf : Nat → Value}
    (h : SegU kernel Assumptions.all L g s F b (factsFrom K W)) (hK : ∀ r ∈ Kf, r ∈ K)
    (hW : ∀ r ∈ Kf, W r = Wf r) : SegU kernel Assumptions.all L g s F b (factsFrom Kf Wf) := by
  intro t ht
  rcases h t ht with ⟨u, hr, hu⟩ | hd
  · obtain ⟨-, -, -, -, hur⟩ := id hu
    refine .inl ⟨u, hr, At.mono hu (holds_of_pointwise fun r hr' => ?_)⟩
    rw [← hW r hr']
    exact holds_mem hur (mem_factsFrom (hK r hr'))
  · exact .inr hd

/-! ### The runs in order -/

/-- The register file after the first run (the predicate of the first branch). -/
def vP (V : Nat → Value) : Nat → Value := runP.V' V
def pick96 (V : Nat → Value) : Bool := predBool (vP V 96)
def vA (V : Nat → Value) : Nat → Value := runA.V' (vP V)
def pick97 (V : Nat → Value) : Bool := predBool (vA V 97)
/-- The register file at pc 1838 on the three paths. -/
def vS (V : Nat → Value) : Nat → Value := runM.V' (vP V)
def vU (V : Nat → Value) : Nat → Value := runM.V' (runT.V' (vA V))
def vM (V : Nat → Value) : Nat → Value := runM.V' (runT.V' (runC.V' (runB.V' (vA V))))
/-- **The register file at pc 1838**: the path the two predicates choose. -/
def vFin (V : Nat → Value) (r : Nat) : Value :=
  if pick96 V then vS V r else if pick97 V then vU V r else vM V r

def kP : List Nat := runP.K' kW1
def kA : List Nat := runA.K' kP
def kS : List Nat := runM.K' kP
def kU : List Nat := runM.K' (runT.K' kA)
def kK : List Nat := runM.K' (runT.K' (runC.K' (runB.K' kA)))
/-- The registers every path knows at pc 1838. -/
def kFin : List Nat := kS.filter fun r => kU.contains r && kK.contains r

theorem fin_sub : (∀ r ∈ kFin, r ∈ kS) ∧ (∀ r ∈ kFin, r ∈ kU) ∧ (∀ r ∈ kFin, r ∈ kK) := by
  simp only [kFin, List.mem_filter, Bool.and_eq_true, List.contains_iff_mem]
  exact ⟨fun r h => h.1, fun r h => h.2.1, fun r h => h.2.2⟩

/-- **The first window on a register file**: from the registers it reads to pc 1838, along the
path the predicates of the file choose. -/
theorem w1_fin (V : Nat → Value) :
    SegU kernel Assumptions.all L g 1299 (factsFrom kW1 V) 1838 (factsFrom kFin (vFin V)) := by
  obtain ⟨sS, sU, sK⟩ := fin_sub
  have hp := runP.adv (L := L) (g := g) (K := kW1) runP_ok V (by decide +kernel)
  refine hp.comp (bra_split Flow.code_1302 (p := 96) (K := kP) (by decide +kernel)
    Lib.bra_rule (segFree (by decide)) (fun b hb ht => ?_) (fun b hb hf => ?_))
  · have e : pick96 V = true := by simp [pick96, vP, hb, ht, predBool]
    exact fin_of (runM.adv (L := L) (g := g) (K := kP) runM_ok (vP V) (by decide +kernel)) sS
      (fun r _ => by simp [vFin, e, vS])
  · have e : pick96 V = false := by simp [pick96, vP, hb, hf, predBool]
    have ha := runA.adv (L := L) (g := g) (K := kP) runA_ok (vP V) (by decide +kernel)
    refine ha.comp (bra_split Flow.code_1466 (p := 97) (K := kA) (by decide +kernel)
      Lib.bra_rule (segFree (by decide)) (fun b hb' ht' => ?_) (fun b hb' hf' => ?_))
    · have e' : pick97 V = true := by simp [pick97, vA, hb', ht', predBool]
      exact fin_of ((runT.adv (L := L) (g := g) (K := kA) runT_ok (vA V) (by decide +kernel)).comp
        (runM.adv (L := L) (g := g) (K := runT.K' kA) runM_ok _ (by decide +kernel))) sU
        (fun r _ => by simp [vFin, e, e', vU])
    · have e' : pick97 V = false := by simp [pick97, vA, hb', hf', predBool]
      exact fin_of ((runB.adv (L := L) (g := g) (K := kA) runB_ok (vA V) (by decide +kernel)).comp
        ((runC.adv (L := L) (g := g) (K := runB.K' kA) runC_ok _ (by decide +kernel)).comp
        ((runT.adv (L := L) (g := g) (K := runC.K' (runB.K' kA)) runT_ok _ (by decide +kernel)).comp
        (runM.adv (L := L) (g := g) (K := runT.K' (runC.K' (runB.K' kA))) runM_ok _
          (by decide +kernel))))) sK
        (fun r _ => by simp [vFin, e, e', vM])

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
