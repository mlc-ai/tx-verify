-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Dispatch.FinalSync
public import Kernels.InklingRelDecode.Proof.Epilogue.FinalSync
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow
noncomputable section

private theorem early_pc {p : Nat} (h : p<2850) :
    Lib.afterFinal p=0 ∧ Lib.finalSync p=false := by
  simp [Lib.afterFinal,Lib.finalSync,show p ≠ 2850 by omega,show p ≠ 2851 by omega,
    show p ≠ 2853 by omega,show p ≠ 2854 by omega,show p ≠ 2855 by omega]

private theorem early_step {a b : Nat} (ha : a<2850) (hb : b<2850) :
    Lib.afterFinal b = Lib.afterFinal a + (Lib.finalSync a).toNat := by
  simp [(early_pc ha).1,(early_pc ha).2,(early_pc hb).1]

private theorem soft_low (s : Softmax.Site) : s.pc<2850 := by
  rcases s.pc_range with h|eq
  · omega
  · rw [eq]; decide

private abbrev softFinal {ent L g} (d : (softCode ent L g).D) :=
  Lib.afterFinal ((softCode ent L g).pc d)

private theorem soft_enter {ent L g} (s : Softmax.Control.D) :
    softFinal (Code.enter (Softmax.Control.code ent L g)
      (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s) =
      Lib.afterFinal s.site.pc := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> rfl

private theorem soft_next {ent L g d ev dn} (hn : (softCode ent L g).next d ev = some (some dn)) :
    softFinal dn = softFinal d + (Lib.finalSync ((softCode ent L g).pc d)).toNat := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [soft_enter]
    exact early_step (soft_low s.site) (soft_low sn.site)
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact Epilogue.final_step step

abbrev dataFinal {Q L g w} (d : (dataCode Q L g w).D) :=
  Lib.afterFinal ((dataCode Q L g w).pc d)

private theorem data_enter {Q L g w} (s : Prologue.Control.D) :
    dataFinal (Code.enter (Prologue.Control.checkedCode Q L g w)
      (fun e => softCode e L g) (dataExit Q L g w) s) = Lib.afterFinal s.site.pc := by
  obtain ⟨s,a,b,c,v⟩ := s
  cases s <;> rfl

theorem data_final_next {Q L g w d ev dn}
    (hn : (dataCode Q L g w).next d ev = some (some dn)) :
    dataFinal dn = dataFinal d + (Lib.finalSync ((dataCode Q L g w).pc d)).toNat := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [data_enter]
    have old := s.site.pc_range
    have new := sn.site.pc_range
    exact early_step (a := s.site.pc) (b := sn.site.pc) (by omega) (by omega)
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact soft_next step

abbrev workerFinal {Q L g w x} (d : (workerCode Q L g w x).D) :=
  Lib.afterFinal ((workerCode Q L g w x).pc d)

private theorem worker_enter {Q L g w x} (s : Dispatch.D) :
    workerFinal (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry s) = Lib.afterFinal s.site.pc := by
  obtain ⟨s,n⟩ := s
  cases s <;> rfl

private theorem worker_back {Q L g w x} (r) (s : (workerFrag Q L g w x r).D) :
    workerFinal (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) r s) =
      workerFinal (Q := Q) (L := L) (g := g) (w := w) (x := x) (.inr ⟨r,s⟩) := by
  cases r <;> obtain ⟨site,rest⟩ := s <;> cases site <;> rfl

theorem worker_final_next {Q L g w x d ev dn}
    (hn : (workerCode Q L g w x).next d ev = some (some dn)) :
    workerFinal dn = workerFinal d + (Lib.finalSync ((workerCode Q L g w x).pc d)).toNat := by
  rcases d with s | ⟨r,s⟩
  · change (Dispatch.next L g s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_enter]
    exact Dispatch.final_step step
  · change ((workerFrag Q L g w x r).next s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_back]
    have low (d : (workerFrag Q L g w x r).D) : (workerFrag Q L g w x r).pc d < 2850 := by
      cases r with
      | loader =>
        change d.site.pc<2850
        generalize d.site = site
        cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
      | mma =>
        change d.site.pc<2850
        generalize d.site = site
        cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    exact early_step (low s) (low sn)

end
end PTX.Kernels.InklingRelDecode.Proof
