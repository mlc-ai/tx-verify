-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Init
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OFullHandoff
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputHandoff
public import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # The other barriers' records are fault-free

`Safety.OtherFaultFree`: the records other than initializations of the table barriers that are
neither ring nor handshake barriers do not fault (`otherFaultFree`). Each barrier is initialized
first (`InitFirst`); by its protocol:

* **S-full and O-full** (count 1): a commit object of the pair's MMA thread
  (`Score.fullObj`); its notifications are gated (`SFullGated`, `OFullGated`: the notification of
  the commit with `t ≥ 1` earlier ones is enabled by a poll with `t - 1` earlier successful ones),
  so it is fault-free (`MbarRing.Notify.Obj.fault_free`).
* **P-ready and second P-ready** (counts 512 and 8) of a pair leader: unit objects
  (`Score.pObj`, `Score.p2Obj`) with gated arrivals (`PReadyGated`, `P2Gated`), so fault-free
  (`MbarRing.Unit.Obj.fault_free`). In the other CTA of the pair nothing arrives on them (the
  producers arrive on the leader's), so their records are polls (`MbarRing.fault_free_of_polls`).
* **Statistics credit** (count 128): a gated unit object (`Stats.gate`, its gate from
  `SoftArrives` and the spinning polls).
* **Output staged and free** (counts 128 and 32) of a launched CTA: the gated unit objects of the
  output ring (`Output.unitRing`, `MbarRing.Unit.Ring.fullGate`, `emptyGate`); in a CTA beyond
  the grid nothing arrives on them.
* **Spare** barriers: no operation but their initialization names them (`SpareUnused`), and no
  copy completes on them (a copy completes on a ring barrier, `AsyncFacts.copy_ring`), so they
  have no other record.

The gates are stated for every arrival event, not only the counted ones (those with a fault-free
record): an arrival that would fault is not counted, so the reuse premises `PReadyReach`,
`P2Reach`, `SFullReach` and `OAcc.OFullReach`, stated for counted arrivals, do not exclude it.
The gate paths are the ones `TmemReach` builds for the counted arrivals; that construction does
not use that the arrival is counted, and `TmemReachGates` restates it for every arrival
(`Faults.otherFaultFree_of_route`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Faults

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The gate premise of the P-ready objects**: a producer's arrival of use `s ≥ 1` on stage
`st`'s P-ready object of the pair led by `c` is enabled by a successful poll of the object with
`s - 1` earlier ones. -/
def PReadyGated (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 →
    MbarRing.Unit.Gated L K A X (pReadyBar L c st) 512 (Score.pThread L c st) 0

/-- **The gate premise of the second P-ready objects**, as `PReadyGated`. -/
def P2Gated (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 →
    MbarRing.Unit.Gated L K A X (pReady2Bar L c st) 8 (Score.p2Prod L X c st) 0

/-- **The gate premise of the S-full objects**: the recorded notification on stage `st`'s S-full
object of CTA `c` of a commit of thread `g` naming its own CTA's object, with `t ≥ 1` earlier
ones, is enabled by a successful poll of the object with `t - 1` earlier ones. -/
def SFullGated (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st g, st < 2 →
    MbarRing.Notify.Gated L K A X (sFullBar L c st) g (sFullBar L (ctaOf L g) st) 0

/-- **The gate premise of the O-full objects**, as `SFullGated`. -/
def OFullGated (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st g, st < 2 →
    MbarRing.Notify.Gated L K A X (oFullBar L c st) g (oFullBar L (ctaOf L g) st) 0

/-- **No operation but its initialization names a spare barrier** (arrival, poll, commit target,
bulk copy, invalidation): a fact of the threads' barrier sites, none of which but the prologue's
initializations names the offsets `+176`, `+184`, `+208`, `+216`, `+224`, `+232`. -/
def SpareUnused (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {m : Loc}, X.UsesMbar e m → (¬ ∃ count, X.MbInit e m count) →
    ∀ k st c, m ≠ (FBar.spare k st).loc L c

/-- **`PReadyInit` for every CTA**: the P-ready object of any CTA is initialized first. -/
theorem pReadyInit_all (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hp : PReadyFacts L X)
    (c : Nat) {st : Nat} (hst : st < 2) : PairTmaRing.InitFirst X (pReadyBar L c st) 512 := by
  refine InitFirst.init_first hpre hX hc htm hi (.pReady ⟨st, hst⟩) c ⟨fun hg he => ?_,
    fun hg he => ?_, fun he hm => absurd hm (hp.p_tensor hst he)⟩
  · obtain ⟨hl, -⟩ := hp.p_arrive hg hst he
    show _ = c / 2
    rw [← hl, leadCta]
    omega
  · obtain ⟨rfl, -⟩ := hp.p_poll hg hst he
    rfl

/-- **`P2Init` for every CTA.** -/
theorem p2Init_all (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (hp : P2Facts L X)
    (c : Nat) {st : Nat} (hst : st < 2) : PairTmaRing.InitFirst X (pReady2Bar L c st) 8 := by
  refine InitFirst.init_first hpre hX hc htm hi (.pReady2 ⟨st, hst⟩) c ⟨fun hg he => ?_,
    fun hg he => ?_, fun he hm => absurd hm (hp.p2_tensor hst he)⟩
  · obtain ⟨hl, -⟩ := hp.p2_arrive hg hst he
    show _ = c / 2
    rw [← hl, leadCta]
    omega
  · obtain ⟨rfl, -⟩ := hp.p2_poll hg hst he
    rfl

theorem leadCta_leadCta (c : Nat) : leadCta (leadCta c) = leadCta c := by
  unfold leadCta
  omega

/-- **The other barriers' records are fault-free.** -/
theorem otherFaultFree (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (ha : AsyncFacts P L X)
    (hs : SFullFacts L X) (ho : OFullFacts L X) (hp : PReadyFacts L X) (hp2 : P2Facts L X)
    (hst : StatsFacts L X) (hout : OutputFacts L X) (hsoft : Stats.SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit)
    (hSG : SFullGated L kernel asms X) (hOG : OFullGated L kernel asms X)
    (hPG : PReadyGated L kernel asms X) (hP2G : P2Gated L kernel asms X)
    (hspare : SpareUnused L X) : Safety.OtherFaultFree L X := by
  have hni : ∀ m, NoInval (X.objects m) :=
    objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he)
  intro b hb hd cta r hr hn
  cases b with
  | qFull _ | qEmpty _ | kvFull _ | kvEmpty _ => simp [FBar.ring] at hb
  | dealloc => exact absurd rfl hd
  | sFull st =>
    change r ∈ X.objects (sFullBar L cta st) at hr
    obtain ⟨g, O⟩ := Score.fullObj hX htm (Score.sFullCommit hX hs) st.isLt
      (InitFirst.sFullInit hpre hX hc htm hi hs cta st st.isLt) (hs.s_arrive st.isLt)
      (hs.s_tensor st.isLt) (fun he => (hs.s_poll (event_thread_lt hX he) st.isLt he).2.2.2.1)
    exact O.fault_free hX (hSG cta st g st.isLt) r hr
  | oFull st =>
    change r ∈ X.objects (oFullBar L cta st) at hr
    obtain ⟨g, O⟩ := Score.fullObj hX htm (OAcc.oFullCommit hX ho) st.isLt
      (InitFirst.oFullInit hpre hX hc htm hi ho cta st st.isLt) (ho.o_arrive st.isLt)
      (ho.o_tensor st.isLt) (fun he => (ho.o_poll (event_thread_lt hX he) st.isLt he).2.2.2.1)
    exact O.fault_free hX (hOG cta st g st.isLt) r hr
  | pReady st =>
    change r ∈ X.objects (pReadyBar L cta st) at hr
    have hinit := pReadyInit_all hpre hX hc htm hi hp cta st.isLt
    by_cases hl : leadCta cta = cta
    · exact (Score.pObj hpre hX hp htm (fun c st _ hst => pReadyInit_all hpre hX hc htm hi hp c hst)
        hl st.isLt).fault_free hX (hPG cta st hl st.isLt) r hr
    · refine MbarRing.fault_free_of_polls hX hinit (hni _) (fun q hq hqn => ?_) r hr
      cases record_source hX.tma.2.2.1 hq with
      | init _ _ ha => exact absurd ha (hqn _)
      | inval _ he _ => exact (htm.no_inval he).elim
      | arrive _ he _ =>
        obtain ⟨hl', -⟩ := hp.p_arrive (event_thread_lt hX he) st.isLt he
        exact absurd (by rw [← hl', leadCta_leadCta]) hl
      | wait _ _ ha => exact ⟨_, _, ha⟩
      | tensor _ he hm _ => exact (hp.p_tensor st.isLt he hm).elim
      | increment _ he _ => exact (htm.no_arriveOn he).elim
      | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
      | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
      | commit _ he htg _ => exact (hp.p_commit st.isLt he htg).elim
      | clc _ he _ _ _ => exact (htm.no_clc he).elim
  | pReady2 st =>
    change r ∈ X.objects (pReady2Bar L cta st) at hr
    have hinit := p2Init_all hpre hX hc htm hi hp2 cta st.isLt
    by_cases hl : leadCta cta = cta
    · exact (Score.p2Obj hpre hX hp2 htm (fun c st _ hst => p2Init_all hpre hX hc htm hi hp2 c hst)
        hl st.isLt).fault_free hX (hP2G cta st hl st.isLt) r hr
    · refine MbarRing.fault_free_of_polls hX hinit (hni _) (fun q hq hqn => ?_) r hr
      cases record_source hX.tma.2.2.1 hq with
      | init _ _ ha => exact absurd ha (hqn _)
      | inval _ he _ => exact (htm.no_inval he).elim
      | arrive _ he _ =>
        obtain ⟨hl', -⟩ := hp2.p2_arrive (event_thread_lt hX he) st.isLt he
        exact absurd (by rw [← hl', leadCta_leadCta]) hl
      | wait _ _ ha => exact ⟨_, _, ha⟩
      | tensor _ he hm _ => exact (hp2.p2_tensor st.isLt he hm).elim
      | increment _ he _ => exact (htm.no_arriveOn he).elim
      | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
      | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
      | commit _ he htg _ => exact (hp2.p2_commit st.isLt he htg).elim
      | clc _ he _ _ _ => exact (htm.no_clc he).elim
  | stats st =>
    change r ∈ X.objects (statsBar L cta st) at hr
    have G := Stats.gate (c := cta) hpre hX hst htm (InitFirst.statsInit hpre hX hc htm hi hst)
      hsoft hspin st.isLt
    exact G.toObj.fault_free hX G.gated r hr
  | oStaged st =>
    change r ∈ X.objects (stagedBar L cta st) at hr
    have hinit := InitFirst.outputInit hpre hX hc htm hi hout
    by_cases hg : cta < L.grid
    · have G := (Output.unitRing hpre hX hout htm hinit hspin hg st.isLt).fullGate hX
      exact G.toObj.fault_free hX G.gated r hr
    · refine MbarRing.fault_free_of_polls hX (hinit cta st st.isLt).1 (hni _)
        (fun q hq hqn => ?_) r hr
      cases record_source hX.tma.2.2.1 hq with
      | init _ _ ha => exact absurd ha (hqn _)
      | inval _ he _ => exact (htm.no_inval he).elim
      | arrive _ he _ =>
        have hgl := event_thread_lt hX he
        obtain ⟨-, -, hcg, -⟩ := hout.staged_arrive hgl st.isLt he
        exact absurd (hcg ▸ cta_lt hgl) hg
      | wait _ _ ha => exact ⟨_, _, ha⟩
      | tensor _ he hm _ => exact ((hout.stage_tensor st.isLt he).1 hm).elim
      | increment _ he _ => exact (htm.no_arriveOn he).elim
      | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
      | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
      | commit _ he htg _ => exact ((hout.stage_commit st.isLt he).1 htg).elim
      | clc _ he _ _ _ => exact (htm.no_clc he).elim
  | oFree st =>
    change r ∈ X.objects (freeBar L cta st) at hr
    have hinit := InitFirst.outputInit hpre hX hc htm hi hout
    by_cases hg : cta < L.grid
    · have G := (Output.unitRing hpre hX hout htm hinit hspin hg st.isLt).emptyGate hX
      exact G.toObj.fault_free hX G.gated r hr
    · refine MbarRing.fault_free_of_polls hX (hinit cta st st.isLt).2 (hni _)
        (fun q hq hqn => ?_) r hr
      cases record_source hX.tma.2.2.1 hq with
      | init _ _ ha => exact absurd ha (hqn _)
      | inval _ he _ => exact (htm.no_inval he).elim
      | arrive _ he _ =>
        have hgl := event_thread_lt hX he
        obtain ⟨-, hcg, -⟩ := hout.free_arrive hgl st.isLt he
        exact absurd (hcg ▸ cta_lt hgl) hg
      | wait _ _ ha => exact ⟨_, _, ha⟩
      | tensor _ he hm _ => exact ((hout.stage_tensor st.isLt he).2 hm).elim
      | increment _ he _ => exact (htm.no_arriveOn he).elim
      | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
      | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
      | commit _ he htg _ => exact ((hout.stage_commit st.isLt he).2 htg).elim
      | clc _ he _ _ _ => exact (htm.no_clc he).elim
  | spare k st =>
    exfalso
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact hn _ ha
    | inval _ he _ => exact htm.no_inval he
    | wait _ he _ =>
      exact hspare (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))))
        (fun ⟨_, _, h⟩ => by rw [he] at h; cases h) k st cta rfl
    | arrive _ he _ =>
      exact hspare (.inl ⟨_, _, _, _, _, he⟩) (fun ⟨_, _, h⟩ => by rw [he] at h; cases h)
        k st cta rfl
    | tensor _ he hm _ =>
      obtain ⟨b', c', hring, hm'⟩ := ha.copy_ring he
      obtain ⟨rfl, -⟩ := FBar.loc_inj (hm.symm.trans hm')
      simp [FBar.ring] at hring
    | increment _ he _ => exact htm.no_arriveOn he
    | arriveOn _ he _ _ _ => exact htm.no_arriveOn he
    | bulk _ he _ _ _ => exact htm.no_bulk he
    | commit _ he htg _ =>
      exact hspare (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, htg⟩))))
        (fun ⟨_, _, h⟩ => by rw [he] at h; cases h) k st cta rfl
    | clc _ he _ _ _ => exact htm.no_clc he

end Faults

end
end PTX.Kernels.FlashAttn4Fwd.Proof
