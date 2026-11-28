-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Prologue.Publication
public import Kernels.InklingRelDecode.Proof.Softmax.Publication
public import Kernels.InklingRelDecode.Proof.Epilogue.Publication
public import Kernels.InklingRelDecode.Proof.Dispatch.Publication
public import Kernels.InklingRelDecode.Proof.Loader.Publication
public import Kernels.InklingRelDecode.Proof.Mma.Publication
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow
noncomputable section

def softPublication {ent L g} : (softCode ent L g).D → Nat
  | .inl s => Softmax.publicationPhase s.site
  | .inr ⟨_,s⟩ => Epilogue.publicationPhase s.site

private theorem soft_enter {ent L g} (s : Softmax.Control.D) :
    softPublication (Code.enter (Softmax.Control.code ent L g)
      (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s) =
      Softmax.publicationPhase s.site := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> rfl

private theorem soft_next {ent L g d ev dn} (hn : (softCode ent L g).next d ev = some (some dn)) :
    softPublication dn = softPublication d + (if (softCode ent L g).pc d ∈ Lib.barOneSites
      then 1 else 0) := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [soft_enter]
    exact Softmax.publication_next step
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact Epilogue.publication_next step

def dataPublication {Q L g w} : (dataCode Q L g w).D → Nat
  | .inl s => Prologue.publicationPhase s.site
  | .inr ⟨_,s⟩ => softPublication s

private theorem data_enter {Q L g w} (s : Prologue.Control.D) :
    dataPublication (Code.enter (Prologue.Control.checkedCode Q L g w)
      (fun e => softCode e L g) (dataExit Q L g w) s) = Prologue.publicationPhase s.site := by
  obtain ⟨s,a,b,c,v⟩ := s
  cases s <;> rfl

theorem data_publication_next {Q L g w d ev dn}
    (hn : (dataCode Q L g w).next d ev = some (some dn)) :
    dataPublication dn = dataPublication d + (if (dataCode Q L g w).pc d ∈ Lib.barOneSites
      then 1 else 0) := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [data_enter]
    exact Prologue.publication_next step
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact soft_next step

def workerPublication {Q L g w x} : (workerCode Q L g w x).D → Nat
  | .inl s => Dispatch.publicationPhase s
  | .inr ⟨.loader n,s⟩ => 3*n + Loader.publicationPhase s.site
  | .inr ⟨.mma n,s⟩ => 3*n + Mma.publicationPhase s.site

private theorem worker_enter {Q L g w x} (s : Dispatch.D) :
    workerPublication (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry s) = Dispatch.publicationPhase s := by
  obtain ⟨s,n⟩ := s
  cases s <;> rfl

private theorem worker_back {Q L g w x} (r) (s : (workerFrag Q L g w x r).D) :
    workerPublication (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) r s) =
      workerPublication (Q := Q) (L := L) (g := g) (w := w) (x := x) (.inr ⟨r,s⟩) := by
  cases r <;> obtain ⟨site,rest⟩ := s <;> cases site <;> rfl

theorem worker_publication_next {Q L g w x d ev dn}
    (hn : (workerCode Q L g w x).next d ev = some (some dn)) :
    workerPublication dn = workerPublication d + (if (workerCode Q L g w x).pc d ∈ Lib.barOneSites
      then 1 else 0) := by
  rcases d with s | ⟨r,s⟩
  · change (Dispatch.next L g s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_enter]
    exact Dispatch.publication_next step
  · change ((workerFrag Q L g w x r).next s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_back]
    cases r with
    | loader n =>
      exact (congrArg (3*n + ·) (Loader.publication_next step)).trans (Nat.add_assoc ..).symm
    | mma n =>
      exact (congrArg (3*n + ·) (Mma.publication_next step)).trans (Nat.add_assoc ..).symm

end
end PTX.Kernels.InklingRelDecode.Proof
