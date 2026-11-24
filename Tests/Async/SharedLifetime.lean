-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Core.Assembly.Correctness
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Flow.SpinsAtLoop

namespace PTX.Tests.SharedLifetime
noncomputable section

private def launch : Launch := { grid := 2, block := 384, clusterSize := 2, params := fun _ =>
                                 none }
private def m : Loc := ⟨.shared, 0, 128⟩
/-- The owner's poll at position 1 is the canonical spin `L: poll; @p bra 4; bra L; 4: exit`, so
its successful return enables the exit that follows it. Register 5 holds the poll's predicate and
register 6 the address of the mbarrier object. -/
private def K : Kernel := { name := "k", params := [], code := [
  { op := .mbarInit 6 0 (.imm 1) }, { op := .mbarWait 5 6 0 (.imm 0) true .cta },
  { guard := some (5, false), op := .bra 4 false }, { op := .bra 1 false }, { op := .exit }] }
private def early : Execution := {
  tr := fun g => if g = 384 then [⟨0, .arrive m 0 1 true .cta⟩] else []
  rf := fun _ _ => none
}

private theorem usesPeer : SharedUse launch early (.thread (384, 0)) 0 :=
  .inl ⟨⟨_, rfl⟩, .inr ⟨128, .arrive 1 0, rfl⟩⟩

-- A remote operation cannot establish the owner's existence by its own source event.
private theorem notStarted : ¬ PeerSharedStarted launch K [] early (.thread (384, 0)) 0 := by
  rintro ⟨⟨g, i⟩, ev, _, hc, hp, _⟩
  have hne : g ≠ 384 := by change g / 384 = 0 at hc; omega
  simp [Execution.get, early, hne] at hp

example : SharedLifetimeUnsafe launch K [] early :=
  ⟨_, 0, usesPeer, .inl ⟨by decide, notStarted⟩⟩
example : Unsafe launch K [] (fun _ => none) early := by
  have h : SharedLifetimeUnsafe launch K [] early :=
    ⟨_, 0, usesPeer, .inl ⟨by decide, notStarted⟩⟩
  unfold Unsafe
  tauto

private def ops : List (AsyncCopy.Ref × MBarrier.Action) := [
  (.thread (0, 0), .init 1), (.thread (384, 0), .arrive 1 0), (.thread (0, 1), .pollParity 0 true)]
private def log : List (MBarrier.Record AsyncCopy.Ref) :=
  match MBarrier.replay none ops with | .ok xs => xs | .error _ => []
private def finished : Execution := {
  tr := fun g => if g = 0 then [⟨0, .mbInit m 1⟩, ⟨1, .wait m 0 true⟩, ⟨4, .exit⟩]
    else if g < 384 then [⟨0, .exit⟩]
    else if g = 384 then [⟨0, .arrive m 0 1 true .cta⟩] else []
  rf := fun _ _ => none
  objects := fun addr => if addr = m then log else []
}

-- All owner threads have exited, but just one is sufficient as the final lifetime witness.
example : CtaExited launch finished 0 := by
  intro g hg hc
  have hlt : g < 384 := by change g / 384 = 0 at hc; omega
  by_cases hz : g = 0
  · subst g
    exact ⟨4, rfl⟩
  · exact ⟨0, by simp [finished, hz, hlt]⟩

-- The remote arrival is recorded before the owner's successful poll, which enables the owner's
-- exit.
example : SharedFinished launch K [] finished (.thread (384, 0)) 0 := by
  refine ⟨⟨_, rfl⟩, (0, 2), 4, by decide, rfl, rfl, ?_⟩
  have hbefore : MBarrier.Before (finished.objects m) (.thread (384, 0)) (.thread (0, 1)) :=
    ⟨1, 2, _, _, rfl, rfl, rfl, rfl, by decide⟩
  have hspin : K.CanonicalSpin 1 4 := ⟨rfl, 5, rfl, rfl⟩
  have htrace : TraceBefore finished (0, 1) (0, 2) := by simp [TraceBefore, finished]
  have hres : Resumes K finished (0, 1) (0, 2) := by
    refine ⟨htrace, ?_⟩
    simp only [Execution.get, finished, ↓reduceIte, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Kind.resume]
    exact ⟨1, 4, m, 0, true, .cta, by simp [Execution.get], hspin, htrace⟩
  exact CompletedBefore.of_before hbefore (.single (DepStep.of_resumes (L := launch) hres))

/-! The rule also covers the issuer's own CTA: a tensor store whose source CTA is the issuer's
own, issued by its only thread, which exits before the source reads complete. -/
private def single : Launch := { grid := 1, block := 1, clusterSize := 1, params := fun _ => none }
private def u8 : TensorDescriptor.Descriptor 1 :=
  ⟨.u8, 4096, ![256, 64], ![256], ⟨![64, 8], ![1, 1]⟩, .none, .zero, .small⟩
private def store : TensorStore.Spec := ⟨⟨1, u8, ![0, 0], ⟨.shared, 0, 1024⟩, none⟩, none⟩
private def ownStore : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorStore 4096 store⟩, ⟨1, .exit⟩] else []
  rf := fun _ _ => none
}

private theorem ownExited : CtaExited single ownStore 0 := by
  intro g hg _
  have hz : g = 0 := by change g < 1 at hg; omega
  subst g
  exact ⟨1, rfl⟩

-- The own-CTA use needs no startup evidence, but its unperformed completion is unsafe.
example : SharedLifetimeUnsafe single K [] ownStore :=
  ⟨.async (0, 0) .readsDone, 0,
    .inr (.inr (.inr (.inl ⟨(0, 0), 4096, store, rfl, ⟨0, rfl⟩, rfl⟩))),
    .inr ⟨ownExited, fun ⟨⟨_, ho, _⟩, _⟩ => by simp [ownStore] at ho⟩⟩

end
end PTX.Tests.SharedLifetime
