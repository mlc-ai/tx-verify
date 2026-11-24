-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderVCopies
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.CpAsyncIssueProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy Prologue

/-- Both decoded V vectors are appended by maximality at the prepared copy cursor. -/
theorem vCopyPairOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pos tid src bytes : Nat} (hg : g < l.threads)
    (hSrc : src < 2^64) (hAlign : src%16 = 0) (hBytes : bytes ≤ 16) (group : Fin 16)
    {s t : TState} {ending : Option TState}
    (ht : At t (vCopyPc group) (vCopyFacts l tid src bytes group))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨vCopyPc group,.copy (vCopySpec l g tid src bytes group false)⟩ ∧
    X.get (g,pos+1) = some ⟨vCopyPc group+1,.copy (vCopySpec l g tid src bytes group true)⟩ ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+2)) (some (next (next t))) ∧
    Run kernel Assumptions.all l g (next (next t)) ((X.tr g).drop (pos+2)) ending := by
  let lo := vCopySpec l g tid src bytes group false
  let hi := vCopySpec l g tid src bytes group true
  have hn₀ : Next kernel Assumptions.all l g s t (.copy lo (next t)) :=
    ⟨hSteps,vCopyTemplate hp hSrc hAlign hBytes group false ht⟩
  obtain ⟨he₀,hPast,hRest⟩ := Step.cp_async_issue_of_maximal hMax hg hn₀
    (fun _ _ => Iff.rfl) (.inl ⟨lo,rfl,rfl⟩) hPrefix hTail hPos hBound hRelease
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  have hn₁ : Next kernel Assumptions.all l g (next t) (next t) (.copy hi (next (next t))) :=
    ⟨.refl,vCopyTemplate hp hSrc hAlign hBytes group true ht.next⟩
  obtain ⟨he₁,hDone,hRemain⟩ := Step.cp_async_issue_of_maximal hMax hg hn₁
    (fun _ _ => Iff.rfl) (.inl ⟨hi,rfl,rfl⟩) hPast hRest (by omega)
    (len_of_get he₀) (releasedIfLast he₀ (by intro h; cases h))
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  simp only [show (next t).pc = vCopyPc group+1 from ht.next.1] at he₁
  exact ⟨ht.1 ▸ he₀,he₁,hDone,hRemain⟩

end PTX.Kernels.TmlFa4Fwd.Loader
