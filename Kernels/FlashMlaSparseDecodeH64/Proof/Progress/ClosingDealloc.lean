-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Closing
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingDealloc
import Lemmas.Kernel.ProgressDescent
import Lemmas.Protocol.NamedBarLedger
import Lemmas.Step.TcLoad
import Lemmas.Step.TmemPair

public section

/-! # Maximal progress at the closing Tensor Memory deallocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
include hpre hmax

/-- With the closing barrier released, a softmax lane must issue its pending deallocation
in a maximal execution. -/
theorem dealloc_not_pending (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {g : Nat}
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g) {d : Wg0.D}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hsite : d.site = .exit) : False := by
  obtain ⟨t, t1, tag, hRun, hLocal, he⟩ := ClosingDealloc.event hpre hmax.1 hs hub hp hd hsite
  exact hmax.not_grows (PTX.Step.tccoll_counted_extension hmax.1 hp.1
    (.inl (ClosingProgress.nonempty_tail hd (by simp))) hrel hRun hLocal he rfl
    (hmax.1.tmemPairResult.snoc_not_wr (by intros; simp))
    (hmax.1.tcRead_snoc_tc (by intros; simp))
    (Interface.all_wf_snoc_of_not_nc hmax.1 (by intros; simp) (by simp)))

open Tmem.Pair PTX.Step in
/-- Once every lane of warp zero has issued the matching deallocation, its final operation
is covered in a maximal execution. -/
private theorem dealloc_publication_aligned (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) {cta tag : Nat} (hcta : cta < L.grid)
    (hops : ∀ lane : Fin 32, X.get (cta * L.block + lane.val,
      (X.tr (cta * L.block + lane.val)).length - 1) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    (hordinal : ∃ k, ∀ lane : Fin 32, X.TcK (cta * L.block + lane.val,
      (X.tr (cta * L.block + lane.val)).length - 1) k) :
    Covered L X (cta * L.block, (X.tr (cta * L.block)).length - 1) := by
  classical
  let g := cta * L.block
  have hPos : 0 < L.block := by rw [hpre.block]; decide
  have hg : g < L.threads := PTX.NamedBar.cta_thread_lt hcta hPos
  have hCta : g / L.block = cta := Nat.mul_div_cancel _ hPos
  have hLane (lane : Fin 32) : warpThread L g lane.val = g + lane.val := by
    simp [warpThread, hCta, g]
  let r := ownerRecord L X g tag none (.dealloc 0 512)
  have hCurrent (lane : Fin 32) : r.own.event L lane =
      (g + lane.val, (X.tr (g + lane.val)).length - 1) := by
    simp [r, ownerRecord, warpRequest, WarpRequest.event, hCta, hLane, g]
  have hValid : r.own.Valid L X .one := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [r, ownerRecord, warpRequest, hCta] using hcta
    · simp [r, ownerRecord, warpRequest, g, hpre.block]
    · intro lane
      rw [hCurrent]
      exact hops lane
    · obtain ⟨k, hk⟩ := hordinal
      exact ⟨k, fun lane => hCurrent lane ▸ hk lane⟩
  have hReady : CompletionReady L X [r.own] := by
    intro w hm prev group hv hbefore i hi
    obtain rfl := List.mem_singleton.mp hm
    obtain ⟨a, ha, haOwn⟩ := recorded_of_before hmax.1.tmemPair hmax.1.tmemPairBlocking
      hv hValid hbefore
    have hGroup : a.group = .one := by
      obtain ⟨_, _, hWarpValid⟩ := ((hmax.1.tmemPair.1 _).1 a ha)
      have hx := hWarpValid.2.2.1 0
      have hx' := hv.2.2.1 0
      rw [haOwn, hx'] at hx
      have hEq := congrArg Event.kind (Option.some.inj hx)
      have hShape := (TcKind.resource.inj (Kind.tc.inj hEq)).1
      have hp := Frame.lt_of_get hmax.1 hx'
      obtain ⟨d, hd⟩ := Frame.event_state hs hmax.1 ht hx' (by simp)
      have hOne := (ResourceEvents.ordinal hpre hmax.1 (hs _ hp).machine hx' hd).2.1
      exact hShape.symm.trans hOne
    exact ⟨[a.own], .inl ⟨prev.cta, a, ha, hGroup, rfl⟩, a.own, by simp, haOwn ▸ hi⟩
  by_contra hPending
  have hFree (lane : Fin 32) :
      ¬ Covered L X (warpThread L g lane.val, (X.tr (warpThread L g lane.val)).length - 1) := by
    rw [hLane, ← hCurrent]
    rintro ⟨ws, hDone, w, hw, lane', he⟩
    have hwValid : ∃ group, w.Valid L X group := by
      rcases hDone with ⟨c, a, ha, hgrp, rfl⟩ | ⟨pair, hPair, rfl⟩
      · obtain rfl := List.mem_singleton.mp hw
        exact ⟨a.group, ((hmax.1.tmemPair.1 c).1 a ha).2.2⟩
      · have hp := hmax.1.tmemPair.2.1 pair hPair
        rcases List.mem_cons.mp hw with rfl | h
        · exact ⟨.two, hp.1.2.1⟩
        · obtain rfl := List.mem_singleton.mp h
          exact ⟨.two, hp.1.2.2.1⟩
    obtain ⟨group, hwValid⟩ := hwValid
    obtain rfl := hwValid.ext hValid he
    apply hPending
    have hZero := hCurrent 0
    simp only [Fin.val_zero, Nat.add_zero] at hZero
    exact ⟨ws, hDone, r.own, hw, 0, hZero⟩
  have he0 := hops 0
  simp only [Fin.val_zero, Nat.add_zero] at he0
  have hb32 : L.block % 32 = 0 := by rw [hpre.block]
  have hRun : runRequests {} (X.tmemHistory (g / L.block) ++ [r]) ≠ .blocked := by
    rw [hCta]
    exact Safety.run_before_dealloc hpre hmax.1 hs ht he0 hPending rfl
  exact hmax.not_grows (Exists.imp (fun Y hh => ⟨hh.1, hh.2.1, hh.2.2.2⟩)
    (warp_entry_counted hmax.1 hg hb32 (fun lane => hLane lane ▸ hops lane)
      (by obtain ⟨k, hk⟩ := hordinal; exact ⟨k, fun lane => hLane lane ▸ hk lane⟩)
      hFree hReady hRun (Interface.all_wf_effects hmax.1 le_recordEntry rfl rfl rfl)))

/-- A maximal execution has covered the final deallocation once all warp-zero lanes
have issued it and are still at that collective. -/
theorem dealloc_publication (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) {cta : Nat} (hcta : cta < L.grid)
    (hops : ∀ lane : Fin 32, ∃ tag, X.get (cta * L.block + lane.val,
      (X.tr (cta * L.block + lane.val)).length - 1) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩) :
    Tmem.Pair.Covered L X (cta * L.block, (X.tr (cta * L.block)).length - 1) := by
  let g := cta * L.block
  have hPos : 0 < L.block := by rw [hpre.block]; decide
  have hg : g < L.threads := by simpa [g] using PTX.NamedBar.cta_thread_lt hcta hPos
  obtain ⟨tag, he⟩ := hops 0
  simp only [Fin.val_zero, Nat.add_zero] at he
  let k := ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl
  have hk : X.TcK (g, (X.tr g).length - 1) k := ⟨⟨_, he, rfl⟩, rfl⟩
  have halign (lane : Fin 32) :
      X.get (g + lane.val, (X.tr (g + lane.val)).length - 1) =
        some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ ∧
      X.TcK (g + lane.val, (X.tr (g + lane.val)).length - 1) k := by
    obtain ⟨tag', hget⟩ := hops lane
    have hl := lane.isLt
    have hlt : lane.val < L.block := by rw [hpre.block]; omega
    have hwarp : SameWarp L g (g + lane.val) := by
      refine ⟨⟨hg, PTX.NamedBar.cta_thread_lt hcta hlt, ?_⟩, ?_⟩
      · simp only [g, Nat.mul_div_cancel _ hPos, Nat.add_comm (cta * L.block),
          Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt hlt, Nat.zero_add]
      · simp only [g, Nat.mul_mod_left, Nat.zero_div, Nat.add_mod, Nat.zero_add,
          Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hl]
    obtain ⟨htag, hOrdinal⟩ := TcCollectiveTrace.dealloc_aligned hpre hmax.1 hs ht hwarp he hget
    exact ⟨htag.symm ▸ hget, (hOrdinal k).mp hk⟩
  exact dealloc_publication_aligned hpre hmax hs ht hcta (fun lane => (halign lane).1)
    ⟨k, fun lane => (halign lane).2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
