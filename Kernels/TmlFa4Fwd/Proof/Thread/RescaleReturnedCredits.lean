-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpRoundProgress
public import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- A rescale stage returns the opposite statistics slot. Its previous credit
count is one below the actual number of visits of that named barrier. -/
theorem RescaleWarpReturned.statisticsCreditAt {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch blocks ord rank : Nat} {stage : Fin 2} {gen : Fin 2 → Nat}
    (c : RescaleWarpReturned p l X g batch blocks stage gen ord rank)
    {h : Nat} (hs : SameWarp l g h) (hw : 8 ≤ warpIndex l h ∧ warpIndex l h < 12) :
    let j := (c.lane h hs).pos-1
    ∃ e, X.get (h,j) = some e ∧ correctionAction e = some (.statsCredit stage.rev) ∧
      (correctionBefore X (h,j)).count (.statsCredit stage.rev)+1 = gen stage.rev := by
  let d := c.lane h hs
  have addr : rescaleReuseLoc l h stage = statsCreditLoc l (h/l.block) stage.rev := by
    fin_cases stage <;> rfl
  obtain ⟨pc,he⟩ := (c.credits h hs).2
  rw [addr] at he
  let e : Event := ⟨pc,.arrive (statsCreditLoc l (h/l.block) stage.rev) 0 1 true .cta⟩
  have recorded : X.get (h,d.pos-1) = some e := he
  have action := statsCreditArrivalAction hp hX stage.rev recorded
  have mark := (correctionStatsCreditMark_iff stage.rev e).mpr
    ((correctionStatsCreditObservation stage.rev (show e.kind = _ from rfl)).mp action)
  have balance := correctionCreditRequiresWait hX stage.rev recorded mark
  rw [correctionWaitPrefixCount hp hX stage.rev (len_of_get recorded) hw] at balance
  have next : d.pos-1+1 = d.pos := by have := d.positive; omega
  have named := c.named h hs stage.rev
  change ((X.tr h).take d.pos).countP (Execution.isBarId (statsBarrierId l h stage.rev)) =
    gen stage.rev at named
  rw [← next,countP_take_succ_false (p := Execution.isBarId _) recorded rfl,balance] at named
  exact ⟨e,recorded,action,by rw [correctionCreditCursor hp hX stage.rev recorded]; exact named⟩

theorem RescaleWarpReturned.statisticsCredit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch blocks ord rank : Nat} {stage : Fin 2} {gen : Fin 2 → Nat}
    (c : RescaleWarpReturned p l X g batch blocks stage gen ord rank)
    {h : Nat} (hs : SameWarp l g h) (hw : 8 ≤ warpIndex l h ∧ warpIndex l h < 12) :
    ∃ j e, X.get (h,j) = some e ∧ correctionAction e = some (.statsCredit stage.rev) ∧
      (correctionBefore X (h,j)).count (.statsCredit stage.rev)+1 = gen stage.rev := by
  exact ⟨_,c.statisticsCreditAt hp hX hs hw⟩

/-- The probability release and the opposite statistics release are consecutive
in the actual correction lane. -/
def PairedRescaleCredit (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (generation : Nat) : Prop :=
  ∃ i, Scores.ProbabilityCredit l X (g,i) (g/l.block) stage 0 ∧
    ∃ e, X.get (g,i+1) = some e ∧ correctionAction e = some (.statsCredit stage.rev) ∧
      (correctionBefore X (g,i+1)).count (.statsCredit stage.rev) = generation

theorem RescaleWarpReturned.pairedCredit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch blocks ord rank n : Nat} {stage : Fin 2} {gen : Fin 2 → Nat}
    (c : RescaleWarpReturned p l X g batch blocks stage gen ord rank)
    {h : Nat} (hs : SameWarp l g h) (hw : 8 ≤ warpIndex l h ∧ warpIndex l h < 12)
    (count : gen stage.rev = n+1) : PairedRescaleCredit l X h stage n := by
  let d := c.lane h hs
  obtain ⟨e,he,ha,ord⟩ := c.statisticsCreditAt hp hX hs hw
  have pos : d.pos-2+1 = d.pos-1 := by
    by_contra! small
    have eq : d.pos-2 = d.pos-1 := by omega
    obtain ⟨pc,hp⟩ := (c.credits h hs).1
    obtain ⟨pr,hr⟩ := (c.credits h hs).2
    change X.get (h,d.pos-2) = _ at hp
    change X.get (h,d.pos-1) = _ at hr
    rw [eq,hr] at hp
    have addr := congrArg (fun e : Event => e.kind) (Option.some.inj hp)
    simp only [Kind.arrive.injEq,and_true] at addr
    have bad := congrArg Loc.addr addr
    fin_cases stage <;> simp [rescaleReuseLoc,creditLoc] at bad
  refine ⟨d.pos-2,(c.credits h hs).1,e,?_,ha,?_⟩
  · rwa [pos]
  · rw [pos]
    rw [count] at ord
    exact Nat.add_right_cancel ord

end PTX.Kernels.TmlFa4Fwd.Correction
