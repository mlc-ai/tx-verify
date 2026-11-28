-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Prologue.QLoadPair
import Kernels.InklingRelDecode.Proof.Lib.Havoc
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.Step.GuardedLoadU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

def queryPc (j : Fin 64) := (Site.ldq j).pc
def queryPred (j : Fin 64) := 81+j.val/16

theorem query_live : ∀ j, queryPred j ∈ ctlLive (queryPc j) := by decide +kernel
theorem query_data : ∀ j, ctl (qDst j) = false := by decide +kernel
private theorem length_code : kernel.code.length = 2856 := by kernel_rfl

theorem query_value {Q L g w d} (j : Fin 64) :
    valueOf Q L g w d (queryPred j) = .pred (queryOn (g%L.block) (j.val/16) d) := by
  have h : j.val/16 = 0 ∨ j.val/16 = 1 ∨ j.val/16 = 2 ∨ j.val/16 = 3 := by omega
  unfold queryPred
  rcases h with h|h|h|h <;> rw [h] <;> rfl

private theorem frameCheck : ∀ j : Fin 63,
    let p := 388+2*j.val
    (ctlLive (p+2)).isSublist (ctlLive p) &&
      Havoc.check Lib.hooks (ctlLive (p+2)) (p+1) (p+2) ((kernel.code.drop (p+1)).take 1) := by
  decide +kernel

/-- Sixty inner loads, fifteen per group. The next query payload is unconstrained. -/
theorem step_query_inner {Q L g w d} (j : Fin 64) (hs : d.site = .ldq j)
    (inner : j.val%16 < 15) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let p := 388+2*j.val
  let z : Fin 64 := ⟨j.val+1,by omega⟩
  let d : D := ⟨.ldq j,a,b,c,won,bcast⟩
  let dn := {d with site := Site.ldq z}
  have grp : z.val/16 = j.val/16 := by dsimp [z]; omega
  have bound : j.val < 63 := by omega
  have step (hi : Inv (g%L.block) d) : (code Q L g w).StepAtU d := by
    have guardAt : Code.GuardTrue (facts Q L g w d p) (some (queryPred j,false)) := by
      apply Code.guardTrue_factsFrom (query_live j)
      rw [query_value,show queryOn _ _ d = true from hi]
      rfl
    have fetch := (qLoadPair (L := L) (g := g) j).2
    apply Code.guardedLoadU (C := code Q L g w) (d := d) (dn := dn) fetch rfl guardAt
      rfl rfl rfl rfl rfl rfl rfl rfl
    · intro x bs
      change some (some {d with site := afterQuery d _ j}) = _
      simp only [afterQuery,dite_eq_left (show j.val+1 < 64 by omega),
        ite_eq_right (show ¬ (j.val+1)%16=0 by omega)]
      rfl
    · change queryOn _ (z.val/16) dn = true
      rw [grp]
      exact hi
    · change qDst j ∉ (facts Q L g w d p).map Prod.fst
      rw [facts,factsFrom_keys]
      exact fun h => Bool.noConfusion ((query_data j).symm.trans (List.mem_filter.mp h).2)
    · have checks := frameCheck ⟨j.val,bound⟩
      dsimp only at checks
      simp only [Bool.and_eq_true] at checks
      change SegU _ _ _ _ (p+1) (facts Q L g w d p) (p+2) (facts Q L g w dn (p+2))
      apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by omega)
        (by rw [length_code]; dsimp [p]; omega)
      · rw [facts,factsFrom_keys]
        simpa only [show p+2-(p+1) = 1 by omega] using checks.2
      · intro x hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
        exact mem_factsFrom (val := valueOf Q L g w d)
          ((List.isSublist_iff_sublist.mp checks.1).subset hr)
  exact ⟨fun hi => (step hi).site hi,fun ins ht hi => (step hi).step ins ht hi⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
