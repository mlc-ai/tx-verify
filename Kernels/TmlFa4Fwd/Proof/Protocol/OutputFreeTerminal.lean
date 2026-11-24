-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputFree
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleOutputFree
import Lemmas.Protocol.MbarCount
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.MbarPending

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Output

private theorem outputFreeCreditsCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2)
    (hCredits : ∀ lane : Fin 32, ∃ j, FreeCredit l X cta stage (outputLane l cta lane,j)) :
    arrivalUnits (X.objects (freeObject l cta stage)) = 32 := by
  classical
  let loc := freeObject l cta stage
  let log := X.objects loc
  let position (lane : Fin 32) := Classical.choose (hCredits lane)
  let key (lane : Fin 32) := Ref.thread (outputLane l cta lane,position lane)
  let select (r : Record Ref) := decide (r.action = .arrive 1 0)
  let refs := (log.filter select).map Record.id
  let keys := Finset.univ.image key
  have hInj : Function.Injective key := by
    intro a b he
    have hh := congrArg Prod.fst (Ref.thread.inj he)
    change cta*l.block+416+a.val = cta*l.block+416+b.val at hh
    exact Fin.ext (by omega)
  have hCard : keys.card = 32 := by
    rw [show keys = Finset.univ.image key from rfl,Finset.card_image_of_injective _ hInj,
      Finset.card_univ,Fintype.card_fin]
  have hNodup : refs.Nodup :=
    (X.objects_checked hX loc).1.sublist ((List.filter_sublist (p := select)).map Record.id)
  have hKeys : refs.toFinset = keys := by
    ext ident
    constructor
    · intro h
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      obtain ⟨hLog,hAction⟩ := List.mem_filter.mp hr
      have hUpdate : CounterUpdate r.action := by
        rw [show r.action = .arrive 1 0 from of_decide_eq_true hAction]
        trivial
      obtain ⟨lane,j,hId,hCredit,_⟩ := freeUpdate hp hX stage hLog hUpdate
      exact Finset.mem_image.mpr ⟨lane,Finset.mem_univ _,by
        rw [hId,hCredit.indexUnique hp hX (Classical.choose_spec (hCredits lane))]⟩
    · intro h
      obtain ⟨lane,_,rfl⟩ := Finset.mem_image.mp h
      have he : X.get (outputLane l cta lane,position lane) = some
        ⟨Epilogue.freePc stage,.arrive loc 0 1 true .cta⟩ :=
        (Classical.choose_spec (hCredits lane)).decoded
      have hA : objectAction X X.async loc (key lane) = some (.arrive 1 0) := by
        simp [key,objectAction,he,loc]
      obtain ⟨_,r,hr,hId,hAction⟩ := MbarOneShot.Hist.record_of_action hX hA
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨List.mem_of_getElem? hr,
        decide_eq_true hAction⟩,hId⟩
  have hUnits {xs : List (Record Ref)} (h : ∀ r ∈ xs, r ∈ log) :
      arrivalUnits xs = xs.countP select := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      have hTail := ih (fun q hm => h q (List.mem_cons_of_mem _ hm))
      have hLog := h r List.mem_cons_self
      have hf := outputFreeHistoryClean hp hX stage hLog
      cases hA : r.action with
      | arrive n b =>
        obtain ⟨_,_,_,_,hOne⟩ := freeUpdate hp hX stage hLog (by rw [hA]; trivial)
        simp [arrivalUnits,hOne,hf,hTail,select,Nat.add_comm]
      | init | pollParity | inval | completeTx | increment =>
        simp [arrivalUnits,select,hA,hTail]
  change arrivalUnits log = 32
  rw [hUnits (fun _ h => h),List.countP_eq_length_filter,
    ← List.length_map Record.id,← List.toFinset_card_of_nodup hNodup,hKeys,hCard]

/-- The 32 actual stage releases advance the staging slot to its next generation. -/
theorem freePhaseOneOfCredits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid) (stage : Fin 2)
    (hCredits : ∀ lane : Fin 32, ∃ j, FreeCredit l X cta stage (outputLane l cta lane,j)) :
    let log := X.objects (freeObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  dsimp only
  let loc := freeObject l cta stage
  let log := X.objects loc
  have hX := hMax.1
  obtain ⟨r,hr,hInit⟩ := freeInitializedOfMaximal hp hMax hc stage
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,hs⟩ := stateBefore_length_some hChecked hNo hr hInit (by decide)
  have hExpected := PairTmaRing.expected_of_init hX (freeInitialized hp hX stage hr) hNo hs
  have hShape {r : Record Ref} (hr : r ∈ log) (h : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := freeUpdate hp hX stage hr h
    exact ha
  have hInc : incrementsBefore log log.length = 0 := incrementsBefore_length_of log (by
    intro r hr h
    have ha := hShape hr (by rw [h]; trivial)
    rw [h] at ha
    cases ha)
  have hTx := PTX.MBarrier.tx_zero hChecked hNo
    (fun r hr n b h => (Action.arrive.inj (h.symm.trans (hShape hr (by rw [h]; trivial)))).2)
    (by
      intro r hr n h
      have ha := hShape hr (by rw [h]; trivial)
      rw [h] at ha
      cases ha) hs
  have hPending := stateBefore_pending_pos hChecked hs hTx
  have hCount : unitsBefore log log.length = 32 := by
    rw [unitsBefore,List.take_length]
    exact outputFreeCreditsCount hp hX stage hCredits
  obtain ⟨hBound,hSum⟩ := (hChecked.accounted hNo (le_refl log.length)).2 s hs
  change unitsBefore log log.length + s.pending = _ at hSum
  rw [hExpected,hInc] at hBound hSum
  rw [hCount] at hSum
  refine ⟨s,hs,?_⟩
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
