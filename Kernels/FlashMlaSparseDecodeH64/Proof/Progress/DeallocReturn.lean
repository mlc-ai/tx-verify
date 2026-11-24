-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingDealloc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.OutputDrain
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace
import Lemmas.Protocol.NamedBarLedger
import Lemmas.Tmem.TmemPairHistory

public section

/-! # Returning after the performed closing deallocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Tmem.Pair

private theorem warp_lane_of_request {L : Launch} {X : Execution} {w : WarpRequest}
    {group : CtaGroup} (hv : w.Valid L X group) (lane l : Fin 32) :
    warpLane L (w.event L lane).1 l.val = (w.event L l).1 := by
  have hlt : w.warp * 32 + lane.val < L.block := by
    have hw := hv.2.1
    have hl := lane.isLt
    omega
  have hIdx : (w.event L lane).1 % L.block = w.warp * 32 + lane.val := by
    change (w.cta * L.block + w.warp * 32 + lane.val) % L.block = _
    rw [Nat.add_assoc, Nat.add_comm (w.cta * L.block), Nat.mul_comm w.cta L.block,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hLane : PTX.laneOf L (w.event L lane).1 = lane.val := by
    rw [PTX.laneOf, hIdx, Nat.mul_comm w.warp 32, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt lane.isLt]
  rw [warpLane, hLane]
  simp only [WarpRequest.event, Nat.add_sub_cancel]

/-- A covered last deallocation supplies all the needs of the lane's next event. -/
theorem released_of_dealloc {L : Launch} {mem0 : Mem0} {X : Execution} {g tag : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, (X.tr g).length - 1) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    (hCovered : Covered L X (g, (X.tr g).length - 1)) : PTX.Step.Released L X g := by
  let i := (g, (X.tr g).length - 1)
  have hPerformed := hCovered.performed hX.tmemPair
  obtain ⟨cta, r, hMem, lane, hLane⟩ := hPerformed
  obtain ⟨_, _, hv⟩ := ((hX.tmemPair.1 cta).1 r hMem)
  obtain ⟨k, hk⟩ := hv.2.2.2
  have hK := hk lane
  rw [hLane] at hK
  have hTc (n : Need) : n ∈ tcNeeds L X i →
      (match n with
      | .node fills => ∃ x, X.RefPresent x ∧ fills x
      | .cond holds => holds) := by
    intro hn
    obtain ⟨g', hm, rfl⟩ := List.mem_map.mp hn
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    have hl32 : l < 32 := lt_of_lt_of_le (List.mem_range.mp hl) (min_le_left ..)
    let t : Fin 32 := ⟨l, hl32⟩
    have hThread := warp_lane_of_request hv lane t
    rw [hLane] at hThread
    refine ⟨.thread (r.own.event L t), ?_, (r.own.event L t).2, ?_, ?_⟩
    · obtain ⟨e, he', _⟩ := (hk t).1
      exact ⟨e, he'⟩
    · rw [hThread]
    · rw [hThread, hK.2]
      exact hk t
  refine ⟨fun tag' kind he' _ => ?_⟩
  cases Option.some.inj (he.symm.trans he')
  intro n hn
  simp only [Needs, he, KindNeeds, resourceNeeds, allocResultNeeds, List.append_nil] at hn
  rcases List.mem_append.mp hn with hn | hn
  · exact hTc n hn
  · simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact hCovered.performed hX.tmemPair
    · simp [needsIf] at hn
      obtain ⟨_, rfl⟩ := hn
      exact hCovered

private theorem covered_warp_dealloc {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {e f : EvId} {tag tag' : Nat} (hw : SameWarp L e.1 f.1)
    (he : X.get e = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    (hf : X.get f = some ⟨tag', .tc (.resource .one none (.dealloc 0 512))⟩)
    (hc : Covered L X e) : Covered L X f := by
  obtain ⟨cta, r, hMem, lane, hLane⟩ := hc.performed hX.tmemPair
  have hv := ((hX.tmemPair.1 cta).1 r hMem).2.2
  have hr := hv.2.2.1 lane
  rw [hLane, he] at hr
  have hOne : r.group = .one := (TcKind.resource.inj (Kind.tc.inj
    (congrArg Event.kind (Option.some.inj hr)))).1.symm
  obtain ⟨k, hk⟩ := hv.2.2.2
  have hKe := hk lane
  rw [hLane] at hKe
  have hKf := ((TcCollectiveTrace.dealloc_aligned hpre hX hs ht hw he hf).2 k).mp hKe
  let t : Fin 32 := ⟨PTX.laneOf L f.1, Nat.mod_lt _ (by decide)⟩
  have hThread := warp_lane_of_request hv lane t
  rw [hLane] at hThread
  have hfThread : (r.own.event L t).1 = f.1 := hThread.symm.trans (sameWarp_lane L hw).symm
  have hEvent := hk t
  have hIndex : (r.own.event L t).2 = f.2 := by
    have hPair : r.own.event L t = (f.1, (r.own.event L t).2) := Prod.ext hfThread rfl
    rw [hPair] at hEvent
    exact Execution.TcK.unique hEvent hKf
  exact ⟨[r.own], .inl ⟨cta, r, hMem, hOne, rfl⟩, r.own, by simp, t, Prod.ext hfThread hIndex⟩

private theorem same_warp_zero {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) {cta : Nat} (hc : cta < L.grid) (i j : Fin 32) :
    SameWarp L (cta * L.block + i.val) (cta * L.block + j.val) := by
  have hPos : 0 < L.block := by rw [hpre.block]; decide
  have hlo (l : Fin 32) : l.val < L.block := by
    have := l.isLt
    rw [hpre.block]
    omega
  have hDiv (l : Fin 32) : (cta * L.block + l.val) / L.block = cta := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt (hlo l), Nat.zero_add]
  have hWarp (l : Fin 32) : (cta * L.block + l.val) % L.block / 32 = 0 := by
    rw [Nat.add_comm, Nat.mul_comm cta L.block, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hlo l), Nat.div_eq_of_lt l.isLt]
  exact ⟨⟨PTX.NamedBar.cta_thread_lt hc (hlo i), PTX.NamedBar.cta_thread_lt hc (hlo j),
    (hDiv i).trans (hDiv j).symm⟩, (hWarp i).trans (hWarp j).symm⟩

/-- Once all warp-zero lanes have issued the deallocation, the request is covered for
every participant, including when some lanes have already exited. -/
theorem dealloc_covered_of_issued {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {cta : Nat} (hcta : cta < L.grid)
    (hIssued : ∀ lane : Fin 32, ∃ i tag, X.get (cta * L.block + lane.val, i) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    {lane : Fin 32} {i tag : Nat}
    (he : X.get (cta * L.block + lane.val, i) =
      some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩) :
    Covered L X (cta * L.block + lane.val, i) := by
  classical
  by_contra hMissing
  have hLast (l : Fin 32) :
      ∃ t, X.get (cta * L.block + l.val, (X.tr (cta * L.block + l.val)).length - 1) =
        some ⟨t, .tc (.resource .one none (.dealloc 0 512))⟩ := by
    obtain ⟨j, t, hj⟩ := hIssued l
    have hjlt : j < (X.tr (cta * L.block + l.val)).length := PTX.len_of_get hj
    have hjlast : j = (X.tr (cta * L.block + l.val)).length - 1 := by
      by_contra hn
      have hp : j + 1 < (X.tr (cta * L.block + l.val)).length := by omega
      have hc := hmax.1.tmemPairBlocking.covered
        (show MustWait X (cta * L.block + l.val, j) from ⟨t, .one, none, _, hj, .inl rfl⟩) hp
      exact hMissing (covered_warp_dealloc hpre hmax.1 hs ht
        (same_warp_zero hpre hcta l lane) hj he hc)
    exact ⟨t, hjlast ▸ hj⟩
  obtain ⟨t, htEvent⟩ := hLast 0
  have hc := dealloc_publication hpre hmax hs ht hcta hLast
  exact hMissing (covered_warp_dealloc hpre hmax.1 hs ht
    (same_warp_zero hpre hcta 0 lane) htEvent he (by simpa using hc))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
