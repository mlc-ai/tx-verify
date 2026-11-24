-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasBoxGenerations
import all Kernels.TmlFa4Fwd.Proof.Protocol.BiasBoxGenerations
import all Kernels.TmlFa4Fwd.Proof.Protocol.BiasCredits
import all Lemmas.Protocol.PairTxCredits
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.MbarPending
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.MBarrier PTX.AsyncCopy Thread.Loader

/-- Both physical halves have completed their 16 KiB transactions in this
specific generation of the CTA's Bias-ready barrier. -/
def NotifiedHalves (p : Params) (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2)
    (gen : Nat) : Prop :=
  let log := X.objects (biasReadyObject l cta stage)
  ∀ half : Fin 2, ∃ i r e spec, log[i]? = some r ∧ r.id = .async e (.notify .load) ∧
    e.1/l.block = cta ∧ BiasSubbox p l X e stage half spec ∧ r.action = .completeTx 16384 ∧
    phaseAt log i = some gen

private theorem notifiedHalvesCard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta gen : Nat} (stage : Fin 2) (delivered : NotifiedHalves p l X cta stage gen) :
    let log := X.objects (biasReadyObject l cta stage)
    (pairTxPhaseRecords log log.length gen (.completeTx 16384)).card = 2 := by
  classical
  let log := X.objects (biasReadyObject l cta stage)
  choose i r e spec record id owner box action phase using delivered
  have mem (h : Fin 2) : i h ∈ pairTxPhaseRecords log log.length gen (.completeTx 16384) :=
    memPairTxPhaseRecords.mpr ⟨(List.getElem?_eq_some_iff.mp (record h)).1,phase h,_,record h,
      biasReadyHistoryClean hp hX stage (List.mem_of_getElem? (record h)),action h⟩
  have distinct : i 0 ≠ i 1 := by
    intro eq
    have recEq := Option.some.inj ((record 0).symm.trans (eq ▸ record 1))
    have eventEq := (Ref.async.inj ((id 0).symm.trans ((congrArg Record.id recEq).trans (id 1)))).1
    obtain ⟨_,first⟩ := (box 0).1
    obtain ⟨_,second⟩ := (box 1).1
    rw [← eventEq] at second
    have specs := (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj
      (first.symm.trans second)))).2
    have addrs := congrArg Loc.addr ((box 0).2.2.1.symm.trans
      ((congrArg (fun s : TensorCopy.Spec => s.sharedBase) specs).trans (box 1).2.2.1))
    change l.sharedBase+(166912+32768*stage.val+16384*0) =
      l.sharedBase+(166912+32768*stage.val+16384*1) at addrs
    omega
  refine Finset.card_eq_two.mpr ⟨i 0,i 1,distinct,Finset.ext fun j => ?_⟩
  constructor
  · intro member
    obtain ⟨_,ph,s,found,_,act⟩ := memPairTxPhaseRecords.mp member
    obtain ⟨issue,h,b,id',own,issued⟩ := biasCompleteOrigin hp hX stage found act
    have age := biasNotificationPhaseExact hp hX stage found id' own issued act ph
    have peer := biasNotificationPhaseExact hp hX stage (record h) (id h) (owner h) (box h)
      (action h) (phase h)
    have eq := biasTensorOrdinalInjective hp hX issued (box h) (own.trans (owner h).symm)
      (age.trans peer.symm)
    have pos := ObjectInit.checked_record_index_eq (X.objects_checked hX _) found (record h)
      (id'.trans ((congrArg (fun x => Ref.async x (.notify .load)) eq).trans (id h).symm))
    subst j
    fin_cases h <;> simp
  · intro member
    rcases Finset.mem_insert.mp member with rfl | single
    · exact mem 0
    · exact (Finset.mem_singleton.mp single) ▸ mem 1

/-- One 32 KiB expectation plus both delivered halves advances the physical
barrier beyond their shared generation, at every logical Bias visit. -/
theorem biasPhaseAdvancedOfHalves {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta gen : Nat} (stage : Fin 2) {i : Nat} {r : Record Ref}
    (record : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (expectation : r.action = .arrive 1 32768)
    (atGen : phaseAt (X.objects (biasReadyObject l cta stage)) i = some gen)
    (delivered : NotifiedHalves p l X cta stage gen) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ gen+1 ≤ s.phase := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have init := biasInitialized hp hX stage (List.mem_of_getElem? record)
  have noInv := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have checked := X.objects_checked hX loc
  obtain ⟨s,found⟩ := MbarRing.Unit.final_of_init hX init noInv
    (List.ne_nil_of_mem (List.mem_of_getElem? record))
  refine ⟨s,found,?_⟩
  have bound := checked.phaseAt_le noInv le_rfl (List.getElem?_eq_some_iff.mp record).1.le
    found atGen
  by_contra! short
  have eq : s.phase = gen := by omega
  have mark : i ∈ pairTxPhaseRecords log log.length gen (.arrive 1 32768) :=
    memPairTxPhaseRecords.mpr
    ⟨(List.getElem?_eq_some_iff.mp record).1,atGen,r,record,
      biasReadyHistoryClean hp hX stage (List.mem_of_getElem? record),expectation⟩
  have pos := Finset.card_pos.mpr ⟨_,mark⟩
  obtain ⟨units,bytes⟩ := MBarrier.unitsAndBytes (stop := log.length) (phase := gen)
    (fun _ hr => biasPairTxActions hp hX stage hr)
  have inc := phaseIncrements_eq_zero (log := log) (fun r hr => by
    cases biasPairTxActions hp hX stage hr with
    | init ha => obtain ⟨_,ha⟩ := ha; rw [ha]; exact nofun
    | poll ha => obtain ⟨_,_,ha⟩ := ha; rw [ha]; exact nofun
    | expect ha | notify ha => rw [ha]; exact nofun) log.length gen
  have sum := checked.pending_eq noInv le_rfl found
  rw [eq,units,inc,PairTmaRing.expected_of_init hX init noInv found] at sum
  change s.pending + (pairTxPhaseRecords log log.length gen (.arrive 1 32768)).card = 1+0 at sum
  change 0 < (pairTxPhaseRecords log log.length gen (.arrive 1 32768)).card at pos
  have one : (pairTxPhaseRecords log log.length gen (.arrive 1 32768)).card = 1 := by omega
  have tx := checked.tx_eq noInv le_rfl found
  rw [eq,bytes,one,notifiedHalvesCard hp hX stage delivered] at tx
  rw [one] at sum
  have live : 0 < s.pending := stateBefore_pending_pos checked found (by omega : s.tx = 0)
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
