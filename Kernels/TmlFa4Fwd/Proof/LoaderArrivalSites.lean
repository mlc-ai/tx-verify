-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyCommit
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private def arrivalSites : List Nat := [674, 904, 1137, 1342, 1602, 1735]

private theorem arrivalSitesAudit : OpPcsFast kernel.code asyncArriveOp arrivalSites = true := by
  decide +kernel

private theorem arrivalSitesImage : arrivalSites = (List.finRange 6).map (copyCommitPc · + 1) := by
  decide

/-- Every actual ordinary-copy arrival is the no-increment arrival of a decoded packet. -/
theorem actualAsyncArrival {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {loc : Loc} {noinc : Bool}
    (h : X.get i = some ⟨pc, .asyncArrive loc noinc⟩) :
    (∃ site : Fin 6, pc = copyCommitPc site + 1) ∧ noinc = true ∧
      loc.space = .shared ∧ loc.cta = i.1 / l.block := by
  rcases get_source hX h with ⟨_, hf⟩ | ⟨t, ins, _, _, hCode, hf⟩
  · cases hf
  have hSite := OpPcsFast.mem arrivalSitesAudit hCode (fires_asyncArrive_op hf rfl)
  rw [arrivalSitesImage] at hSite
  obtain ⟨site, _, hPc⟩ := List.mem_map.mp hSite
  change copyCommitPc site + 1 = pc at hPc
  subst pc
  have hIns := Option.some.inj (hCode.symm.trans (copyCommitCode site).2)
  rw [hIns] at hf
  simp only [eventTmpl, cpAsyncTmpl, Bool.false_eq_true, ↓reduceIte] at hf
  cases hm : mbarLoc l i.1 t (copyArrivalAddress site).1 (copyArrivalAddress site).2 with
  | error f =>
    simp only [hm, Except.bind, bind, ofExec, Fires] at hf
    obtain ⟨he, _⟩ := hf
    cases he
  | ok mb =>
    simp only [hm, Except.bind, bind, ofExec, pure, Except.pure, Fires,
      Event.mk.injEq, Kind.asyncArrive.injEq] at hf
    obtain ⟨_, hLoc, hNoInc⟩ := hf.1
    subst loc
    exact ⟨⟨site, rfl⟩, hNoInc, mbarLoc_local hm⟩

/-- The frozen ordinary copy protocol never issues an incrementing arrive-on. -/
theorem noIncrementingCopyArrival {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {loc : Loc} : ¬ X.AsyncArrive i loc false := by
  rintro ⟨pc, h⟩
  exact Bool.noConfusion (actualAsyncArrival hX h).2.1

end
end PTX.Kernels.TmlFa4Fwd.Loader
