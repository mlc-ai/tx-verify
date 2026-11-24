-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingScratchLoop

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private def primingKWaitSite : DrainWaitSite := ⟨517, 9606, 1848, 1849⟩

/-- The initial K-ring reuse wait acquires slot zero at parity one. -/
def primingKWaitEvent (l : Launch) (g : Nat) (ok : Bool) : Event :=
  ⟨517, .wait ⟨.shared, g / l.block, l.sharedBase + 56⟩ 1 ok true .cta⟩

/-- The first K empty acquire operands and retained scratch facts. -/
def primingKWaitFacts (p : Params) (l : Launch) (batch base : Nat) :
    List (Nat × Value) :=
  (1848, b32 (l.sharedBase + 56)) :: (1849, b32 1) :: primingScratchFacts p l batch base 1

private theorem primingKWaitPrep {l : Launch} {g : Nat} (hAddr : l.sharedBase + 56 < 2 ^ 32) :
    Seg kernel [] l g 2 515 [(2535, b32 l.sharedBase)] 517
      [(1848, b32 (l.sharedBase + 56)), (1849, b32 1)] := by
  intro t ht
  seg_fp ht using norm_bits

/-- Extra facts must survive the wait preparation and exclude its result predicate. -/
structure PrimingKWaitExtra (G : List (Nat × Value)) : Prop where
  prepKeep : ((kernel.code.drop 515).take 2).all
    (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  resultFresh : ∀ x ∈ G, x.1 ≠ 9606

set_option maxRecDepth 3000 in
/-- Prepare the initial K release poll while retaining the scratch and copy frame. -/
theorem primingKWaitPrepare {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch base : Nat} {t : TState} {G : List (Nat × Value)} (hG : PrimingKWaitExtra G)
    (ht : At t 515 (primingScratchFacts p l batch base 1 ++ G)) :
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t v ∧
      At v 517 (primingKWaitFacts p l batch base ++ G) := by
  let F := primingScratchFacts p l batch base 1
  have hAddr : l.sharedBase + 56 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hArg : At t 515 [(2535, b32 l.sharedBase)] := ht.mono (by
    exact ⟨holds_lookup ht.2.2.2.2 (by rfl), trivial⟩)
  obtain ⟨v, hv, hV⟩ := primingKWaitPrep hAddr t hArg
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++ G).map Prod.fst) (by decide) (by decide) ht.1
    (primingKeepAppend (F := F) (G := G) (pc := 515) (n := 2)
      (by set_option maxRecDepth 100000 in kernel_rfl) hG.prepKeep)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hFrame : Holds v.regs (F ++ G) := holdsSchedulerFrame ht.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hFacts : At v 517 (primingKWaitFacts p l batch base ++ G) :=
    hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1, hFrame⟩
  exact ⟨v,run_rtg hvA,hFacts⟩

set_option maxRecDepth 3000 in
/-- The actual execution following the two scratch iterations retries the K release
poll until it succeeds, then continues at the first local-source preparation. -/
theorem primingKWaitObservedFrameInPrefix {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch base : Nat} {t : TState} {events : List Event} {ending : Option TState}
    {G : List (Nat × Value)} (hG : PrimingKWaitExtra G)
    (ht : At t 515 (primingScratchFacts p l batch base 1 ++ G))
    (hr : Run kernel Assumptions.all l g t events ending)
    (hProgress : ending = none ∨ ∃ e ∈ events, 517 < e.pc) :
    ∃ n u rest, events = List.replicate n (primingKWaitEvent l g false) ++
        (primingKWaitEvent l g true :: rest) ∧
      At u 520 (primingScratchFacts p l batch base 1 ++ G) ∧
      Run kernel Assumptions.all l g u rest ending := by
  have hAddr : l.sharedBase + 56 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 56) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨v, hv, hFacts⟩ := primingKWaitPrepare (g := g) hp hG ht
  have hMore : events ≠ [] := by
    intro h
    rw [h] at hr hProgress
    rcases hProgress with hDone | ⟨e, he, _⟩
    · rw [hDone] at hr
      cases hr
    · cases he
  obtain ⟨n, u, rest, he, hu, hRest⟩ :=
    loaderWaitTraceInPrefix (phase := 1) primingKWaitSite
      ⟨Flow.code_517, Flow.code_518, Flow.code_519⟩
      (by decide) hAddr hAlign (by decide)
      (by
        intro x hm he
        rcases List.mem_append.mp hm with hOld | hNew
        · have hx := List.mem_map_of_mem (f := Prod.fst) hOld
          rw [he] at hx
          exact (show primingKWaitSite.result ∉
            (primingKWaitFacts p l batch base).map Prod.fst from of_decide_eq_true rfl) hx
        · exact hG.resultFresh x hNew he)
      (by simp [primingKWaitFacts, primingKWaitSite])
      (by simp [primingKWaitFacts, primingKWaitSite]) hFacts
      (hr.after_local_nonempty hv hMore) hProgress
  exact ⟨n, u, rest, he, hu.mono hu.2.2.2.2.2.2, hRest⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g i batch base : Nat} (hb : batch < p.batch)
    (hRows : base + 64 < 2 ^ 31)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {t : TState}
include hp hX hb hRows writes

/-- The actual scratch and release-poll prefix of a priming K packet. -/
theorem primingScratchAndWaitObservedFrameInPrefix {G : List (Nat × Value)}
    (hScratch : PrimingScratchExtra G) (hWait : PrimingKWaitExtra G)
    (ht : At t 488 (primingScratchFacts p l batch base 0 ++ G)) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hDemand : PrefixDemand X g i 517 ending) :
    ∃ n u rest, (X.tr g).drop i =
      primingScratchEvents p l g batch base 0 ++ primingScratchEvents p l g batch base 1 ++
        List.replicate n (primingKWaitEvent l g false) ++ (primingKWaitEvent l g true :: rest) ∧
      At u 520 (primingScratchFacts p l batch base 1 ++ G) ∧
      Run kernel Assumptions.all l g u rest ending := by
  obtain ⟨v, hPages, hV, hRun⟩ :=
    primingScratchLoopObservedFrameInPrefix hp hX hb hRows writes hScratch ht hr
      (hDemand.weaken (by decide))
  have hAfter := hDemand.advanceList hPages (by
    intro e he
    have hSite : e.pc ≤ 514 := (List.mem_append.mp he).elim
      (primingScratchEvents_before e) (primingScratchEvents_before e)
    omega)
  obtain ⟨n, u, rest, hWait, hu, hRest⟩ :=
    primingKWaitObservedFrameInPrefix hp hWait hV hRun hAfter.eventInSuffix
  exact ⟨n, u, rest, by rw [hPages, hWait]; simp only [List.append_assoc], hu, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
