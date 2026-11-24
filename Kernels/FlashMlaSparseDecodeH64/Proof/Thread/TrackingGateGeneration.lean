-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateExit
public import Lemmas.Order.DependencyWitness
import Lemmas.Order.WaitOrderEnables
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # Resource generation order for actual prologue gate successors -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.CtaBarrier

private theorem generation_le_of_index_le {L : Launch} {X : Execution} {c i j id : Nat}
    {s t : State} (hi : At L.block (X.barriers c) i s) (hj : At L.block (X.barriers c) j t)
    (hij : i ≤ j) : (s.slots id).generation ≤ (t.slots id).generation := by
  apply at_generation_mono (i := i) (h := (X.barriers c).take j) _ hj
  unfold At at hi ⊢
  rwa [List.take_take, Nat.min_eq_left hij]

/-- After a thread has passed a CTA barrier, any later recorded arrival of the same thread
on that ID belongs to a strictly later resource generation. -/
theorem barrier_generation_lt_after_return {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i j key later tag : Nat} {id : Fin 16} {count : Option Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.get (g, i) = some ⟨tag, .bar id.val count .sync⟩)
    (hj : i < j) (hjlen : j < (X.tr g).length)
    (hFirst : CtaBarK L X (g, i) key)
    (hDone : CtaBarDone L X (g / L.block) key)
    (hLater : CtaBarArrivalK L X (g, j) later)
    (hId : key % 16 = id.val) (hIdLater : later % 16 = id.val) :
    key / 16 < later / 16 := by
  have hres : DepStep L kernel X (.thread (g, i), true) (.thread (g, j), false) :=
    DepStep.of_resumes L (Resumes.of_blocking (f := (g, j)) hi rfl ⟨rfl, hj, hjlen⟩)
  have henable : (OrderObject.ctaBar (g / L.block) id).Enabling := trivial
  by_contra! hle
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · have hk : key = later := by omega
    subst later
    obtain ⟨c, hc⟩ := hDone
    have hw := Witness.of_ctaBarCounted hFirst hc hLater rfl
    have hback : DepStep L kernel X (.thread (g, j), false) (.thread (g, i), true) :=
      DepStep.of_witness L hw
    exact (hX.dependency.acyclic _ henable _) (.tail (.single (.inl hres)) (.inl hback))
  · obtain ⟨a, s, w, cnt, lanes, l, ha, haState, hm, haPhase, _⟩ := hFirst.2.2
    obtain ⟨b, t, w', cnt', lanes', l', hb, hbState, hm', hbPhase, _⟩ := hLater.2.2
    rw [hId] at ha haPhase
    rw [hIdLater] at hb hbPhase
    have hba : b < a := by
      by_contra! h
      have hmono := generation_le_of_index_le haState hbState h (id := id.val)
      rw [haPhase, hbPhase] at hmono
      omega
    have hjPresent : ∃ ev, X.get (g, j) = some ev := by
      obtain ⟨_, _, _, hf⟩ := hLater.2.1
      exact ⟨_, hf⟩
    have ho : ObjectOrder L X (.ctaBar (g / L.block) id)
        (.thread (g, j), false) (.thread (g, i), false) :=
      ⟨rfl, rfl, (g, j), (g, i), rfl, rfl, hjPresent, ⟨_, hi⟩, b, a,
        _, _, hb, ha, hba, rfl, rfl, List.mem_map.mpr ⟨_, hm', rfl⟩,
        List.mem_map.mpr ⟨_, hm, rfl⟩⟩
    have hstage : DepStep L kernel X (.thread (g, i), false) (.thread (g, i), true) :=
      DepStep.node ⟨_, hi⟩
    exact (hX.dependency.acyclic _ henable _) (.tail (.tail
      (.single (.inl hstage)) (.inl hres)) (.inr ho))

/-- Every real arrival recorded in generation zero of barrier zero comes from the
thread's followed prologue gate. A dismissed body cannot contribute to this generation. -/
theorem zero_generation_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hzero : CtaBarArrivalK L X (g, i) 0) :
    X.get (g, i) = some ⟨97, .bar 0 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)) := by
  obtain ⟨count, tag, mode, he⟩ := hzero.2.1
  rcases Frame.fired hs hX he with ⟨q, _, hst, hf⟩ | ⟨_, _, _, h⟩
  · cases q with
    | none =>
      obtain ⟨j, hj, hGate, _⟩ := dismissal_after_gate hpre hX (fun g hg => (hs g hg).machine)
        (PTX.len_of_get he).le hst
      have hlen : j + 1 < (X.tr g).length := hj.trans (PTX.len_of_get he)
      obtain ⟨key, hFirst, hDone⟩ := ctaBarDone_of_returned hX hGate hlen
      obtain ⟨_, _, he'⟩ := hFirst.2.1
      have hid : key % 16 = 0 :=
        (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hGate))).2).1
      have hlt := barrier_generation_lt_after_return (id := 0) hX hGate
        (by omega : j < i) (PTX.len_of_get he) hFirst hDone hzero hid rfl
      omega
    | some d =>
      obtain ⟨rfl, rfl, rfl⟩ := RingGateEvents.gate_source hf rfl
      have hpc : tag = 97 := Frame.event_pc hs hX he hst
      exact ⟨by rwa [hpc] at he, hst⟩
  · cases h

/-- Only full-CTA prologue arrivals can occur on barrier zero in the history up to the
resource's first release. The untracked suffix imposes no premise on that history. -/
theorem zero_generation_protocol {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {c index : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hc : c < L.grid) (hcomp : CompletesAt L.block (X.barriers c) index 0 0) :
    NamedBar.Protocol none (Finset.range 12) 0 ((X.barriers c).take (index + 1)) := by
  intro r hr
  cases r with
  | exit g e => trivial
  | arrival id warp count lanes =>
    intro hid
    subst id
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    have hiLt := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at hiLt
    have hle : i ≤ index := by omega
    have hrecord : (X.barriers c)[i]? = some (.arrival 0 warp count lanes) := by
      rwa [List.getElem?_take, ite_eq_left (by omega : i < index + 1)] at hi
    obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
    obtain ⟨s, t, hAt, hperf⟩ := run_at_record hlast hrecord
    obtain ⟨_, u, _, _, hAtEnd, _, hUPhase, _⟩ := hcomp
    have hphase := generation_le_of_index_le hAt hAtEnd hle (id := 0)
    rw [hUPhase] at hphase
    have hphase : (s.slots 0).generation = 0 := Nat.le_zero.mp hphase
    obtain ⟨e, heRef⟩ := perform_ref_exists hperf
    obtain ⟨⟨g, e'⟩, hm, he⟩ := List.mem_map.mp heRef
    change e' = e at he
    subst e'
    obtain ⟨hg, hge, tag, mode, he⟩ :=
      ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hrecord)) (g, e) hm
    have hcta : e.1 / L.block = c := PTX.cta_ref_cta hX hc hrecord heRef
    have hthread : e.1 < L.threads := Frame.lt_of_get hX he
    have hGen : GenerationOf L.block (X.barriers (e.1 / L.block)) e 0 0 := by
      rw [hcta]
      exact ⟨i, s, warp, count, lanes, g, hrecord, hAt, hm, hphase, t, hperf⟩
    have hReal := (zero_generation_source hpre hX hs
      (CtaBarArrivalK.of_generation hX.ctaBar hthread (by decide) hGen)).1
    have hn := (Kind.bar.inj (Event.mk.inj (Option.some.inj (he.symm.trans hReal))).2).2.1
    have hw := (perform_arrival_lanes hperf).2.1 (g, e) hm |>.2.1
    exact ⟨Finset.mem_range.mpr (by rw [← hw, hpre.block] at *; omega), hn⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
