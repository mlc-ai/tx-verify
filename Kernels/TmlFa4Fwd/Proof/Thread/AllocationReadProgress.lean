-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationRecordProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
public import Kernels.TmlFa4Fwd.Proof.MmaAllocationRead
public import Lemmas.Step.Read
import Lemmas.Flow.AllocTmpl
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Prologue AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Mma (allocationSlot allocationReadTemplateFromBase
  allocationBarrierCanRelease allocationBarrierPos)

noncomputable section

/-- The four shared bytes containing the allocator result. -/
def resultAccess (l : Launch) (g : Nat) : Acc :=
  {loc := allocationSlot l g, size := 4}

private theorem resultSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g site : Nat} {e : Event}
    (hStore : X.get (g / l.block * l.block + 384, 7) =
      some ⟨site, .wr (resultAccess l g) (b32 0).toBytes⟩) :
    NewRead l m X g e (fun _ => some (.thread (g / l.block * l.block + 384, 7)))
      (resultAccess l g) ((b32 0).toBytes.map some) := by
  let a := resultAccess l g
  let w : EvId := (g / l.block * l.block + 384, 7)
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk
    have hCovers : a.Covers (a.loc.at k) := Acc.covers_at hk
    refine ⟨a, (b32 0).toBytes, .inl ⟨site, hStore⟩, hCovers, ?_⟩
    change k < 4 at hk
    simp only [wbyte, Loc.at, resultAccess, a, Nat.add_sub_cancel_left, List.getElem?_map]
    rw [List.getElem?_eq_getElem (show k < (b32 0).toBytes.length from hk)]
    rfl
  · intro k w' a' bs' hk hWrite hCover _
    have he : w' = .thread w := allocationResultWriter hp hX hk hWrite hCover
    rw [he]
    intro hByte
    cases hByte with
    | direct hDirect =>
      rcases hDirect with hBase | ⟨_, _, _, _, hResult, _, _, ⟨_, hLoad⟩, _⟩
      · exact baseCausality_irrefl hX.object.cause hBase
      · obtain ⟨_, _, hStore⟩ := hResult.writes
        rw [hLoad] at hStore
        cases hStore
    | commitOperand _ _ _ hRead =>
      obtain ⟨_, hRead⟩ := hRead
      have hRange := mmaSharedByteRange hp hX hRead.1
      have hLower := hRange.lower
      change l.sharedBase + 3072 ≤ l.sharedBase + 312 + k at hLower
      change k < 4 at hk
      omega

/-- A released allocator lane at the result read can read column zero using the unique writer. -/
theorem resultReadExtends {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g site : Nat} (hg : g < l.threads) (hStart : X.tr g ≠ []) (hReleased : Step.Released l X g)
    {t : TState} {facts : List (Nat × Value)}
    (ht : At t 1911 facts) (hBase : t.regs 2535 = some (b32 l.sharedBase))
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t))
    (hStore : X.get (g / l.block * l.block + 384, 7) =
      some ⟨site, .wr (resultAccess l g) (b32 0).toBytes⟩) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  let bs := (b32 0).toBytes.map some
  let r : Nat → Option Ref := fun _ => some (.thread (g / l.block * l.block + 384, 7))
  let ev : Event := ⟨t.pc, .rd (resultAccess l g) bs⟩
  have hOut := allocationReadTemplateFromBase (g := g) hp ht hBase
  have hStep : EStep kernel Assumptions.all l g t ev (some (afterLoad t [1179] bs)) :=
    ⟨_, hOut, bs, rfl, rfl, rfl⟩
  exact Step.read_counted_extension hX hg hStart hReleased hRun .refl hStep
    (r := r) (resultSource hp hX hStore) (Assumptions.wf_snoc_nonGlobal hX (by
      simp [resultAccess, allocationSlot]))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
include hp hMax

private theorem resultWriterExists (hg : g < l.threads) :
    ∃ site, X.get (g / l.block * l.block + 384, 7) =
      some ⟨site, .wr (resultAccess l g) (b32 0).toBytes⟩ := by
  let c := g / l.block
  let owner := c * l.block + 384
  have hc := NamedBar.cta_lt hg
  have hb : 384 < l.block := by rw [hp.block]; decide
  have hOwner : owner < l.threads := NamedBar.cta_thread_lt hc hb
  have hPos : 0 < l.block := by rw [hp.block]; decide
  have ⟨hCta, hLocal⟩ := NamedBar.lane_cta (c := c) hPos hb
  have hw : warpIndex l owner = 12 := by unfold warpIndex owner; rw [hLocal]
  have hz : laneOf l owner = 0 := by unfold laneOf owner; rw [hLocal]
  obtain ⟨t, _, ht, he, hPrefix, hTail⟩ := allocatorIssues hp hMax hOwner hw
  simp only [hz, ↓reduceIte] at hPrefix hTail
  obtain ⟨e, hGet, hKind, _, _, _⟩ := allocatorStores hp hMax hOwner hw hz ht he hPrefix hTail
  obtain ⟨site, kind⟩ := e
  cases hKind
  have hSame : allocationSlot l owner = allocationSlot l g := by
    unfold allocationSlot owner
    rw [hCta]
  exact ⟨site, by rwa [hSame] at hGet⟩

/-- Replay the maximal allocator lane through its actual allocation-result read. -/
theorem allocatorReadsResultPrefixWithBase (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ t o, X.get (g, allocationBarrierPos l g + 1) =
        some ⟨1911, .rd (resultAccess l g) ((b32 0).toBytes.map some)⟩ ∧
      At t 1912 [(1179,b32 0), (1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (allocationBarrierPos l g + 2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  obtain ⟨pos, t, o, hPos, hBar, hOrdZero, ht, hPrefix, hTail⟩ :=
    allocatorRendezvousPrefix hp hMax hg hw
  have hBase : t.regs 2535 = some (b32 l.sharedBase) := ht.2.2.2.2.2.2.1
  have hOut := allocationReadTemplateFromBase (g := g) hp ht hBase
  have hLen : pos + 1 ≤ (X.tr g).length := len_of_get hBar
  have hLt : pos + 1 < (X.tr g).length := by
    by_contra! hLe
    have hLast : (X.tr g).length - 1 = pos := by omega
    obtain ⟨Y, hY, hTr, hRel⟩ := allocationBarrierCanRelease hp hMax hg
      (by decide) (hLast.symm ▸ hBar) (hLast.symm ▸ hOrdZero)
      (fun h hh _ hRole => participantsArrive hp hMax hh hRole)
    obtain ⟨site, hStore⟩ := resultWriterExists hp hMax hg
    have hStoreY : Y.get (g / l.block * l.block + 384, 7) =
        some ⟨site, .wr (resultAccess l g) (b32 0).toBytes⟩ := by
      change (Y.tr _)[7]? = _
      rwa [hTr]
    have hStarted : Y.tr g ≠ [] := by
      rw [hTr]
      intro h
      rw [h, List.length_nil] at hLen
      omega
    have hRun : Run kernel Assumptions.all l g {} (Y.tr g) (some t) := by
      rw [hTr, ← List.take_of_length_le hLe]
      exact hPrefix
    exact hY.not_grows (resultReadExtends hp hY.1 hg hStarted hRel ht hBase hRun hStoreY)
  have hn : Next kernel Assumptions.all l g t t
      (.read (resultAccess l g) (afterLoad t [1179])) := ⟨.refl, hOut⟩
  obtain ⟨e, v, he, ⟨bytes, hBytes, rfl, hv⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_, _, _, h⟩; cases h) hTail
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  obtain rfl := Option.some.inj hv
  have hEvent : X.get (g, pos + 1) = some ⟨1911, .rd (resultAccess l g) bytes⟩ := ht.1 ▸ he
  have hZero := mmaAllocationReadZero hp hMax.1 hEvent
  subst bytes
  have hAfter : At (afterLoad t [1179] ((b32 0).toBytes.map some)) 1912
      [(1179, b32 0), (1062, b32 12), (2535, b32 l.sharedBase)] := by
    have hRebuild := rebuild_b32 0
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
    have hEq : {setReg t 1179 (b32 0) with pc := t.pc + 1, sub := 0, acc := []} =
        next (setReg t 1179 (b32 0)) := by
      have hs := ht.2.1
      have ha := ht.2.2.1
      cases t
      simp_all [setReg, next]
    rw [hEq]
    have ht' := ht.mono (G := [(1062, b32 12), (2535, b32 l.sharedBase)])
      ht.2.2.2.2.2
    have hSet := ht'.set (r := 1179) (v := b32 0) (by
      intro pair hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact (by decide : 1062 ≠ 1179)
      · exact (by decide : 2535 ≠ 1179))
    exact hSet
  have hRun : Run kernel Assumptions.all l g {} ((X.tr g).take (pos + 1 + 1))
      (some (afterLoad t [1179] ((b32 0).toBytes.map some))) := by
    rw [List.take_succ_eq_append_getElem hLt]
    have hEq : (X.tr g)[pos + 1] = ⟨t.pc, .rd (resultAccess l g) ((b32 0).toBytes.map some)⟩ := by
      change (X.tr g)[pos + 1]? = _ at he
      rwa [List.getElem?_eq_getElem hLt, Option.some.injEq] at he
    rw [hEq]
    exact hPrefix.snoc .refl ⟨_, hOut, _, hBytes, rfl, rfl⟩
  subst pos
  exact ⟨_, o, hEvent, hAfter, hRun, hRest⟩

/-- Replay the maximal allocator lane through its actual allocation-result read. -/
theorem allocatorReadsResultPrefix (hg : g < l.threads) (hw : warpIndex l g = 12) :
    ∃ t o, X.get (g, allocationBarrierPos l g + 1) =
        some ⟨1911, .rd (resultAccess l g) ((b32 0).toBytes.map some)⟩ ∧
      At t 1912 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (allocationBarrierPos l g + 2)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  obtain ⟨t, o, hGet, ht, hPrefix, hTail⟩ :=
    allocatorReadsResultPrefixWithBase hp hMax hg hw
  exact ⟨t,o,hGet,ht.mono ht.2.2.2.2.2,hPrefix,hTail⟩

/-- The first allocation rendezvous has released in every CTA of a maximal execution. -/
theorem initialBarrierReleased (hg : g < l.threads) :
    CtaBarDone l X (g/l.block) 2 := by
  let c := g/l.block
  let allocator := c*l.block + 384
  have hWithin : 384 < l.block := by rw [hp.block]; decide
  have hActor : allocator < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hWithin
  obtain ⟨hCta,hMod⟩ := NamedBar.lane_cta (c := c) (by rw [hp.block]; decide) hWithin
  have hWarp : warpIndex l allocator = 12 := by
    unfold warpIndex allocator
    rw [hMod]
  obtain ⟨_, _, hRead, _, _, _⟩ :=
    allocatorReadsResultPrefix hp hMax hActor hWarp
  obtain ⟨j, _, _, hJ, hBar, _, _, _, _⟩ :=
    allocatorRendezvousPrefix hp hMax hActor hWarp
  have hPast : j+1 < (X.tr allocator).length := by rw [hJ]; exact len_of_get hRead
  change CtaBarDone l X c 2
  rw [← hCta]
  exact CtaBarrier.first_generation_released_of_returned hMax.1 (by decide) hBar hPast

end
end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
