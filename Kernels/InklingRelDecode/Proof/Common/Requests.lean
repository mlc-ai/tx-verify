-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Prologue.Requests
public import Kernels.InklingRelDecode.Proof.Softmax.Requests
public import Kernels.InklingRelDecode.Proof.Epilogue.Requests
public import Kernels.InklingRelDecode.Proof.Dispatch.Requests
public import Kernels.InklingRelDecode.Proof.Loader.Requests
public import Kernels.InklingRelDecode.Proof.Mma.Requests
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow
noncomputable section

def softRequests {ent L g} : (softCode ent L g).D → Nat
  | .inl s => Softmax.requestPhase s.site
  | .inr ⟨_,s⟩ => Epilogue.requestPhase s.site

private theorem soft_enter {ent L g} (s : Softmax.Control.D) :
    softRequests (Code.enter (Softmax.Control.code ent L g)
      (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s) =
      Softmax.requestPhase s.site := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> rfl

private theorem soft_next {ent L g d ev dn} (hn : (softCode ent L g).next d ev = some (some dn)) :
    softRequests dn = softRequests d + (if (softCode ent L g).pc d ∈ Lib.requestPcs
      then 1 else 0) := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [soft_enter]
    exact Softmax.request_next step
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact Epilogue.request_next step

def dataRequests {Q L g w} : (dataCode Q L g w).D → Nat
  | .inl s => Prologue.requestPhase s.site
  | .inr ⟨_,s⟩ => softRequests s

private theorem data_enter {Q L g w} (s : Prologue.Control.D) :
    dataRequests (Code.enter (Prologue.Control.checkedCode Q L g w)
      (fun e => softCode e L g) (dataExit Q L g w) s) = Prologue.requestPhase s.site := by
  obtain ⟨s,a,b,c,v⟩ := s
  cases s <;> rfl

theorem data_requests_next {Q L g w d ev dn}
    (hn : (dataCode Q L g w).next d ev = some (some dn)) :
    dataRequests dn = dataRequests d + (if (dataCode Q L g w).pc d ∈ Lib.requestPcs
      then 1 else 0) := by
  rcases d with s | ⟨_,s⟩
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inl_some hn
    rw [data_enter]
    exact Prologue.request_next step
  · obtain ⟨sn,step,rfl⟩ := Code.glue_inr_some hn
    exact soft_next step

def workerRequests {Q L g w x} : (workerCode Q L g w x).D → Nat
  | .inl s => Dispatch.requestPhase s
  | .inr ⟨.loader n,s⟩ => 3*n + Loader.requestPhase s.site
  | .inr ⟨.mma n,s⟩ => 3*n + Mma.requestPhase s.site

/-- The dispatch states off the retry after an invalid byte, and the rounds at which the roles
are entered (the first) and the thread exits (every later one). -/
def DispatchClean (s : Dispatch.D) : Prop :=
  s.site ≠ .badSync ∧ s.site ≠ .badSyncAgain ∧
    (s.site = .idleDec ∨ s.site = .idleSync ∨ s.site = .idleSyncAgain ∨ s.site = .idleInc ∨
      s.site = .loaderEntry ∨ s.site = .mmaEntry → s.round = 0) ∧
    (s.site = .exitSync ∨ s.site = .exitDealloc ∨ s.site = .ret → 1 ≤ s.round)

def workerClean {Q L g w x} : (workerCode Q L g w x).D → Prop
  | .inl s => DispatchClean s
  | .inr ⟨.loader n,_⟩ | .inr ⟨.mma n,_⟩ => n = 0

private theorem worker_enter {Q L g w x} (s : Dispatch.D) :
    workerRequests (Code.enter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry s) = Dispatch.requestPhase s := by
  obtain ⟨s,n⟩ := s
  cases s <;> rfl

private theorem worker_back {Q L g w x} (r) (s : (workerFrag Q L g w x r).D) :
    workerRequests (Code.backEnter (Dispatch.code L g (startRegs Q L g w x) x 0)
      (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) r s) =
      workerRequests (Q := Q) (L := L) (g := g) (w := w) (x := x) (.inr ⟨r,s⟩) := by
  cases r <;> obtain ⟨site,rest⟩ := s <;> cases site <;> rfl

theorem worker_requests_next {Q L g w x d ev dn} (ok : workerClean (Q := Q) (L := L) (g := g)
      (w := w) (x := x) d)
    (hn : (workerCode Q L g w x).next d ev = some (some dn)) :
    workerRequests dn = workerRequests d + (if (workerCode Q L g w x).pc d ∈ Lib.requestPcs
      then 1 else 0) := by
  rcases d with s | ⟨r,s⟩
  · change (Dispatch.next L g s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_enter]
    exact Dispatch.request_next ok.2.1 step
  · change ((workerFrag Q L g w x r).next s ev).map _ = _ at hn
    obtain ⟨_,step,h⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨sn,rfl,h⟩ := Option.map_eq_some_iff.mp h
    subst dn
    rw [worker_back]
    cases r with
    | loader n =>
      exact (congrArg (3*n + ·) (Loader.request_next step)).trans (Nat.add_assoc ..).symm
    | mma n =>
      exact (congrArg (3*n + ·) (Mma.request_next step)).trans (Nat.add_assoc ..).symm

end
end PTX.Kernels.InklingRelDecode.Proof
