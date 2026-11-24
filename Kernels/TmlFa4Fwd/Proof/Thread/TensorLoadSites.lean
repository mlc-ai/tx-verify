-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemLoadCompletion
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmem
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame

private def noTensorLoad : Tmpl → Prop
  | .tcLd .. | .tc (.ld ..) _ => False
  | _ => True

private theorem noTensorLoadOfExec {r : Exec Tmpl} (h : AllOk noTensorLoad r) :
    noTensorLoad (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

private theorem noTensorLoadOfStore {l : Launch} {g : Nat} {s : TState}
    {addr : Nat} {vals : List Opnd} (shape : TcShape) :
    noTensorLoad (tcTmpl l g s (.tcSt addr vals shape)) := by
  cases shape <;> simp only [tcTmpl] <;> apply noTensorLoadOfExec
  all_goals repeat' first
    | trivial
    | (apply allOk_bind; intro _)
    | apply allOk_ite

private theorem noTensorLoadFires {site address : Nat} {vals : List Value} {shape : TcShape}
    {e : Event} {o : Option TState} {tm : Tmpl} (hNo : noTensorLoad tm)
    (hf : Fires site tm e o) (he : e.kind = .tc (.ld address vals shape)) : False := by
  obtain ⟨pos, kind⟩ := e
  change kind = _ at he
  subst kind
  cases tm <;> simp only [Fires, noTensorLoad] at hf hNo <;> aesop

private def tensorLoadOp : Op → Bool
  | .tcLd .. => true
  | _ => false

private theorem tensorLoadFiresOp {A : List Assumption} {l : Launch} {g : Nat} {s : TState}
    {op : Op} {site address : Nat} {vals : List Value} {shape : TcShape} {o : Option TState}
    (hf : Fires site (eventTmpl A l g s op) ⟨site, .tc (.ld address vals shape)⟩ o) :
    tensorLoadOp op = true := by
  have hTyped := fires_tcData_op hf rfl
  cases op <;> simp only [tcDataOp, Bool.false_eq_true] at hTyped
  case tcLd => rfl
  case tcSt dst values sh =>
    apply (noTensorLoadFires (o := o) (tm := eventTmpl A l g s (.tcSt dst values sh))
      (e := ⟨site, .tc (.ld address vals shape)⟩) _ hf rfl).elim
    simp only [eventTmpl, tcStTmpl]
    split <;> try exact noTensorLoadOfStore _
    split <;> try exact noTensorLoadOfStore _
    split <;> trivial
  all_goals
    apply (noTensorLoadFires _ hf rfl).elim
    simp only [eventTmpl, tcTmpl]
    apply noTensorLoadOfExec
    split <;> trivial

private def explicitSites : List Nat := (List.finRange 2).flatMap fun stage =>
  List.ofFn (TmlFa4Fwd.Correction.finalizeLoadPc stage)

private def biasedScoreSites (repeated : Bool) : List Nat :=
  List.ofFn (Softmax.scorePc (if repeated then .biased else .first))

set_option maxRecDepth 100000 in
private theorem loadSiteAudit : OpPcsFast kernel.code tensorLoadOp
    (Assumptions.tcLdDataflowSites ++ explicitSites ++ biasedScoreSites false ++
      biasedScoreSites true) = true := by decide +kernel

/-- A score load that completes at the first probability store of its biased round. -/
@[no_expose] def DelayedScoreLoad (X : Execution) (i : EvId) (repeated : Bool) (quarter : Fin 4) :
    Prop :=
  ∃ address values shape, X.get i = some
    ⟨Softmax.scorePc (if repeated then .biased else .first) quarter,
      .tc (.ld address values shape)⟩

theorem DelayedScoreLoad.decoded {X : Execution} {i : EvId} {repeated : Bool} {quarter : Fin 4}
    (h : DelayedScoreLoad X i repeated quarter) :
    ∃ address values shape, X.get i = some
      ⟨Softmax.scorePc (if repeated then .biased else .first) quarter,
        .tc (.ld address values shape)⟩ := h

theorem DelayedScoreLoad.of_decoded {X : Execution} {i : EvId} {repeated : Bool}
    {quarter : Fin 4} {address : Nat} {values : List Value} {shape : TcShape}
    (h : X.get i = some ⟨Softmax.scorePc (if repeated then .biased else .first) quarter,
      .tc (.ld address values shape)⟩) : DelayedScoreLoad X i repeated quarter :=
  ⟨address,values,shape,h⟩

/-- Every actual load is a score read, an output rescale read, or a finalization read. -/
theorem tensorLoadSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {site address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨site, .tc (.ld address values shape)⟩) :
    (∃ round : Softmax.Round, ∃ q : Fin 4, site = Softmax.scorePc round q) ∨
    (∃ stage : Fin 2, ∃ chunk : Fin 8, site = TmlFa4Fwd.Correction.rescaleLoadPc stage chunk) ∨
    (∃ stage : Fin 2, ∃ chunk : Fin 16,
      site = TmlFa4Fwd.Correction.finalizeLoadPc stage chunk) := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, _, _, _, hc, hFire⟩
  · cases hf
  have hs := OpPcsFast.mem loadSiteAudit hc (tensorLoadFiresOp hFire)
  simp only [List.mem_append] at hs
  rcases hs with ((h | h) | h) | h
  · have hDataflow : Assumptions.tcLdDataflowSites =
        (List.ofFn (Softmax.scorePc .unbiased)) ++ (List.finRange 2).flatMap
          (fun stage => List.ofFn (TmlFa4Fwd.Correction.rescaleLoadPc stage)) := by decide
    rw [hDataflow] at h
    rcases List.mem_append.mp h with hs | hrs
    · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hs
      exact .inl ⟨.unbiased,q,rfl⟩
    · obtain ⟨stage, _, hStage⟩ := List.mem_flatMap.mp hrs
      obtain ⟨chunk, rfl⟩ := List.mem_ofFn.mp hStage
      exact .inr (.inl ⟨stage,chunk,rfl⟩)
  · obtain ⟨stage, _, hStage⟩ := List.mem_flatMap.mp h
    obtain ⟨chunk, rfl⟩ := List.mem_ofFn.mp hStage
    exact .inr (.inr ⟨stage,chunk,rfl⟩)
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp h
    exact .inl ⟨.first,q,rfl⟩
  · obtain ⟨q, rfl⟩ := List.mem_ofFn.mp h
    exact .inl ⟨.biased,q,rfl⟩

/-- The actual Tensor Memory load either completes at its load wait or belongs to a biased
score round whose completion is recorded at the first probability store. -/
theorem tensorLoadCases {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {address : Nat} {values : List Value} {shape : TcShape}
    (hLoad : X.TLd i address values shape) :
    DataflowLoad X i ∨ ExplicitWaitLoad X i ∨ ∃ repeated quarter,
      DelayedScoreLoad X i repeated quarter := by
  obtain ⟨site, he⟩ := hLoad
  rcases tensorLoadSite hX he with ⟨round,q,rfl⟩ | ⟨stage, chunk, rfl⟩ | ⟨stage, chunk, rfl⟩
  · cases round
    · exact .inr (.inr ⟨false,q,_,_,_,he⟩)
    · exact .inr (.inr ⟨true,q,_,_,_,he⟩)
    · exact .inl (DataflowLoad.of_decoded
        ((by decide : ∀ k, Softmax.scorePc .unbiased k ∈ Assumptions.tcLdDataflowSites) q) he)
  · exact .inl (DataflowLoad.of_decoded
      ((by decide : ∀ s k, TmlFa4Fwd.Correction.rescaleLoadPc s k ∈
        Assumptions.tcLdDataflowSites) stage chunk) he)
  · exact .inr (.inl (ExplicitWaitLoad.finalization stage chunk he))

/-- The only load completion that requires a later window is a delayed score load. -/
theorem tensorLoadCompletedBeforeReleaseOrDelayed {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i d : EvId} {address : Nat} {values : List Value} {shape : TcShape}
    (hScope : i.1 / l.block = d.1 / l.block) (h : X.TLd i address values shape)
    (hd : Deallocation X d) : TcMma.WaitBefore l X .waitLd i d ∨
      ∃ repeated quarter, DelayedScoreLoad X i repeated quarter := by
  rcases tensorLoadCases hX h with hData | hExplicit | hDelayed
  · exact .inl (dataflowLoadCompletedBeforeRelease hp hX hScope hData hd)
  · exact .inl (explicitLoadCompletedBeforeRelease hp hX hScope hExplicit hd)
  · exact .inr hDelayed

end PTX.Kernels.TmlFa4Fwd.Thread
