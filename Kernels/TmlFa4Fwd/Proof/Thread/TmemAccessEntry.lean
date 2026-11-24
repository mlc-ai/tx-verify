-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
public import Core.Tmem.TmemPairAccess
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierTerminal
import Lemmas.Flow.NotTcData

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- A role has issued a Tensor Memory data operation or a Tensor Core MMA. -/
def TensorDataEvent (X : Execution) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧
    (isTcData e = true ∨ ∃ dst spec accum mask, e.kind = .tc (.mma dst spec accum mask))

/-- The final allocation arrival follows every Tensor Memory operation of its lane. -/
theorem tensorDataBeforeTerminalArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {count : Option Nat} (hTensor : TensorDataEvent X (g,i))
    (hArrival : BarrierArrival X (g,j) 2 count .arrive) : i < j := by
  obtain ⟨e, he, hData⟩ := hTensor
  have notData {kind : Kind} (hKind : e.kind = kind) (hTc : isTcData ⟨e.pc, kind⟩ = false)
      (hMma : ∀ dst spec acc mask, kind ≠ .tc (.mma dst spec acc mask)) : False := by
    obtain ⟨pc, actual⟩ := e
    cases hKind
    rcases hData with h | ⟨dst, spec, acc, mask, h⟩
    · rw [hTc] at h
      cases h
    · exact hMma dst spec acc mask h
  by_contra! hEarlier
  rcases hEarlier.eq_or_lt with rfl | hEarlier
  · obtain ⟨b, hb, hKind⟩ := hArrival
    obtain rfl := Option.some.inj (he.symm.trans hb)
    exact notData hKind rfl (by intros; nofun)
  · rcases finalArrivalTerminates hp hX hArrival hEarlier he with hExit | ⟨_, hFault⟩
    · exact notData hExit rfl (by intros; nofun)
    · exact notData hFault rfl (by intros; nofun)

/-- Any active Tensor Memory data operation is ordered after the actual 512-column allocation
of its CTA, through the first returned collective entry rendezvous. -/
theorem allocationBeforeTensorData {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (hEvent : TensorDataEvent X i) :
    ∃ r ∈ X.tmemHistory (i.1 / l.block), r.action = .alloc 512 0 ∧
      baseCausality l X (r.own.event l 0) i := by
  obtain ⟨g, j⟩ := i
  obtain ⟨e, he, hTensor⟩ := hEvent
  have hg := event_thread_lt hX he
  obtain ⟨k, hk, site, hs, hEntry⟩ := tensorEventAfterAllocationEntry hp hX he hTensor
  have hRole : warpIndex l g < 13 := by
    rcases allocationEntryRole hp hX hs hEntry with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega
  obtain ⟨hDone, user, hUser, hUserKey⟩ :=
    allocationGenerationZeroBefore hp hX hg hRole hk he hEntry
  let owner := (g / l.block) * l.block + 384
  have hCta : owner / l.block = g / l.block := by dsimp [owner]; rw [hp.block]; omega
  have hOwner : owner < l.threads := by
    have hGrid : g / l.block < l.grid := NamedBar.cta_lt hg
    change (g / l.block) * l.block + 384 < l.grid * l.block
    rw [hp.block] at hGrid ⊢
    omega
  have hWarp : warpIndex l owner = 12 := by unfold warpIndex owner; rw [hp.block]; omega
  have hLane : laneOf l owner = 0 := by unfold laneOf owner; rw [hp.block]; omega
  obtain ⟨mark, source, hSource, hMark, hMarkKey⟩ :=
    allocationGenerationZeroMember hp hX hOwner (by omega) (by simpa only [hCta] using hDone)
  have hSite : source = 1910 := by
    rcases allocationEntryRole hp hX hSource hMark with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega
  subst source
  obtain ⟨n, bar, hBarOrder, _, _, hResult⟩ :=
    allocationPrefixAtBarrierReadOrExit hp hX hOwner hWarp hMark (.inr (.inl rfl))
  obtain ⟨col, _, hOrder, hStore⟩ := hResult hLane
  obtain ⟨r, hr, hAction, hAlloc, _, _⟩ := allocationStoreRecord hp hX hStore
  have hLen := (List.getElem?_eq_some_iff.mp he).1
  have hSync : CtaBarSync l X (owner, n) (g, j) :=
    ⟨⟨hOwner, hg, hCta⟩, 2, mark, user, hMarkKey.arrival, hUserKey, by omega, hUser, hLen⟩
  refine ⟨r, hCta ▸ hr, hAction, ?_⟩
  rw [hAlloc, Nat.add_sub_cancel]
  exact .single (.inr (.inl hSync))

/-- The actual allocation covers all physical columns of the issuing CTA. -/
theorem allocatedTensorColumn {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (he : TensorDataEvent X i) {column : Nat} (hc : column < 512) :
    ∃ r ∈ X.tmemHistory (i.1 / l.block), Tmem.Pair.Covers l X r (i.1 / l.block) i column := by
  obtain ⟨r, hr, ha, hb⟩ := allocationBeforeTensorData hp hX he
  exact ⟨r, hr, .own ⟨512, 0, ha, ((hX.tmemPair.1 _).2.1 r hr).symm, Nat.zero_le _, hc, hb⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread
