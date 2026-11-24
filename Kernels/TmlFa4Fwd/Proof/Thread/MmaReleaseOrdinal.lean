-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The four places in the MMA pipeline that return a K/V buffer. -/
inductive ReleaseForm where
  | firstKey | loopValue | loopKey | tailValue
  deriving DecidableEq

/-- The decoded release-site class associated with each semantic form. -/
def releaseIndex : ReleaseForm → Fin 4
  | .firstKey => 0
  | .loopValue => 1
  | .loopKey => 2
  | .tailValue => 3

/-- An actual commit returning a K/V buffer. -/
def ReleaseIssue (X : Execution) (g index : Nat) (form : ReleaseForm) (spec : TcCommit.Spec) :
    Prop :=
  X.get (g, index) = some ⟨(commitSite (releaseCommitSite (releaseIndex form))).pc,
    .tc (.commit spec)⟩

/-- An actual successful ready wait from the part of the pipeline paired with this release. -/
def ReleaseReadyObservation (X : Execution) (g index : Nat) (form : ReleaseForm)
    (loc : Loc) (parity : Nat) : Prop :=
  X.get (g, index) =
    some ⟨(slotWait (releaseIndex form)).pc, .wait loc parity true true .cta⟩

/-- The ready observation's actual event determines its release form. -/
theorem ReleaseReadyObservation.form_eq {X : Execution} {g wait : Nat}
    {a b : ReleaseForm} {loc₁ loc₂ : Loc} {q₁ q₂ : Nat}
    (ha : ReleaseReadyObservation X g wait a loc₁ q₁)
    (hb : ReleaseReadyObservation X g wait b loc₂ q₂) : a = b := by
  have hSite : ∀ i j : Fin 4, (slotWait i).pc = (slotWait j).pc → i = j := by decide
  have hIndex : Function.Injective releaseIndex := by
    intro i j h
    cases i <;> cases j <;> simp_all [releaseIndex]
  have hPc := congrArg Event.pc (Option.some.inj (ha.symm.trans hb))
  exact hIndex (hSite _ _ hPc)

/-- Prior successful observations of this periodic part of the pipeline. -/
def readyOccurrence (X : Execution) (g index : Nat) (form : ReleaseForm) : Nat :=
  ((X.tr g).take index).countP (readyAtSite (releaseIndex form))

/-- Prior elections for releases of this form in the lane's prefix. -/
def releaseElections (X : Execution) (g index : Nat) (form : ReleaseForm) : Nat :=
  ElectOrd.siteOrdinal (fun pc => pc == (slotElect (releaseIndex form)).pc) X g index

/-- Prior release elections of the same form on the release issuer. -/
def releaseOccurrence (X : Execution) (g index : Nat) (form : ReleaseForm) : Nat :=
  ElectOrd.siteOrdinal (fun pc => pc == (slotElect (releaseIndex form)).pc) X g (index - 1)

/-- The release depends on its precise occurrence's successful ready wait in any peer lane. -/
theorem ReleaseIssue.readyOccurrence {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h index : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    (hWarp : SameWarp l g h) (hIssue : ReleaseIssue X g index form spec) :
    ∃ (j : Nat) (loc : Loc) (parity : Nat),
      ReleaseReadyObservation X h j form loc parity ∧
      readyOccurrence X h j form = releaseOccurrence X g index form ∧
      Relation.TransGen (DepStep l kernel X)
        (.thread (h, j), true) (.thread (g, index), false) :=
  readyWaitAtReleaseOrdinal hp hX (releaseIndex form) hWarp hIssue

/-- A fragment in the pending occurrence of this release precedes its issue. -/
theorem ReleaseIssue.afterCacheFragment {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index commit d : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hCommit : ReleaseIssue X g commit form spec)
    (hMma : X.MmaIssue (g, index) d op accum mask)
    (hOrdinal : releaseElections X g index form = releaseOccurrence X g commit form) :
    TraceBefore X (g, index) (g, commit) := by
  obtain ⟨hCommitPos, inst, lead, hElect⟩ :=
    readyReleaseElection hp hX (releaseIndex form) hCommit
  obtain ⟨_, he⟩ := hMma
  have hOrder : index < commit - 1 := by
    by_contra! hBad
    rcases hBad.lt_or_eq with hLt | hEq
    · let selected := ElectOrd.atSites (fun pc => pc == (slotElect (releaseIndex form)).pc)
      have hGet : (X.tr g)[commit - 1]? =
          some ⟨(slotElect (releaseIndex form)).pc, .elect (2 ^ 32 - 1) inst lead⟩ := hElect
      have hStep : ((X.tr g).take ((commit - 1) + 1)).countP selected =
          releaseOccurrence X g commit form + 1 := by
        rw [List.take_add_one, hGet]
        simp [List.countP_append, selected, ElectOrd.atSites, isElectEv,
          releaseOccurrence, ElectOrd.siteOrdinal]
      have hMono := (List.take_sublist_take_left (l := X.tr g)
        (show (commit - 1) + 1 ≤ index by omega)).countP_le (p := selected)
      change ((X.tr g).take index).countP selected = _ at hOrdinal
      omega
    · have hMmaAt := he
      rw [← hEq] at hMmaAt
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hElect.symm.trans hMmaAt)))
  exact ⟨rfl, by omega, PTX.len_of_get hCommit⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
