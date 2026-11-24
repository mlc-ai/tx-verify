-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The P-ready objects are unit objects

Stage `st`'s P-ready object of the pair led by CTA `c` (`pReadyBar`, count 512) is a unit object
(`MbarRing.Unit.Obj`, offset 0): its arrivals are the release arrivals without transaction bytes
of its 512 producers (`pThread`: the stage's 128 softmax threads and the 128 correction threads of
each CTA of the pair, `PReadyFacts.p_arrive`), its polls the leader's MMA warp's, with the parity
of their earlier successful polls (`p_poll`); no copy, commit, bulk copy, cancellation request or
invalidation touches it. Its history starts with its only initialization (`PReadyInit`, a
premise, as `Stats.StatsInit` for the credit barriers).

**PPhase** (`pReadyHandoff`): the unit handoff (`PReadyHandoff`) holds when the MMA warp's polls
enable the producers' later arrivals (`PReadyReach`, `MbarRing.Unit.Reach`: a producer's arrival
of use `t` is enabled by each MMA lane's polls for the uses before `t`), by the counting argument
on the object's history (`MbarRing.Unit.Obj.handoff`, `MbarRing.Multi.Units`). The enabling paths
cross the S-full objects (a softmax arrival of tile `t` follows its poll observing the commit of
tile `t`, which follows the MMA thread's poll of phase `t - 1`) and the statistics and O-full
objects (a correction arrival of credit `t`); their joint induction is the premise
`PReadyReach`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- Producer `a` (of the 512) of stage `st`'s P-ready object of the pair led by `c`: softmax
thread `a % 128` of the stage (`a < 256`) or correction thread `a % 128` (`a ≥ 256`), of CTA
`c + a % 256 / 128`. -/
def pThread (L : Launch) (c st : Nat) (a : Fin 512) : Nat :=
  if a.val < 256 then (c + a.val / 128) * L.block + 128 * st + a.val % 128
  else (c + (a.val - 256) / 128) * L.block + 256 + (a.val - 256) % 128

/-- **The initialization premise** of the P-ready objects: each history starts with its only
initialization, without fault, with count 512. -/
def PReadyInit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 → PairTmaRing.InitFirst X (pReadyBar L c st) 512

/-- **The reuse premise** of the P-ready objects: each MMA lane's polls of the object for the uses
before `t` enable each producer's arrival of use `t`. -/
def PReadyReach (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 → ∀ h, mmaIn L c h →
    MbarRing.Unit.Reach L K A X (pReadyBar L c st) 512 (pThread L c st) 0 h

theorem pThread_inj (hpre : Pre P L mem0) (c : Nat) {st : Nat} (hst : st < 2) :
    Function.Injective (pThread L c st) := by
  intro a b h
  have hb := hpre.block
  have ha := a.isLt
  have hb' := b.isLt
  unfold pThread at h
  rw [hb] at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- A producer of the pair led by `c` is one of the 512. -/
theorem pThread_of (hpre : Pre P L mem0) {c st g : Nat} (hc : leadCta c = c)
    (h : pProd L c st g) : ∃ a, g = pThread L c st a := by
  obtain ⟨-, hl, hr⟩ := h
  have hb := hpre.block
  unfold leadCta at hl hc
  unfold ctaOf at hl
  unfold warpOf at hr
  rw [hb] at hl hr
  rcases hr with ⟨h8, hs⟩ | ⟨h8, h12⟩
  · refine ⟨⟨(g / 512 - c) * 128 + (g % 512 - 128 * st), by omega⟩, ?_⟩
    unfold pThread
    rw [hb]
    simp only
    split_ifs <;> omega
  · refine ⟨⟨256 + (g / 512 - c) * 128 + (g % 512 - 256), by omega⟩, ?_⟩
    unfold pThread
    rw [hb]
    simp only
    split_ifs <;> omega

/-- **Stage `st`'s P-ready object of the pair led by `c` is a unit object** of its 512
producers. -/
theorem pObj (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (hp : PReadyFacts L X)
    (htm : TmemFacts L X) (hinit : PReadyInit L X) {c st : Nat} (hc : leadCta c = c)
    (hst : st < 2) : MbarRing.Unit.Obj X (pReadyBar L c st) 512 (pThread L c st) 0 where
  pos := by decide
  inj := pThread_inj hpre c hst
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (htm.no_inval he).elim
    | @arrive g j pc tx cnt rel sc hid he ha =>
      have hg := event_thread_lt hX he
      obtain ⟨hl, hrole, rfl, rfl, rfl, -⟩ := hp.p_arrive hg hst he
      exact .arrive hid (pThread_of hpre hc ⟨hg, hl, hrole⟩) he ha
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact (hp.p_tensor hst he hm).elim
    | increment _ he _ => exact (htm.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
    | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
    | commit _ he htg _ => exact (hp.p_commit hst he htg).elim
    | clc _ he _ _ _ => exact (htm.no_clc he).elim
  init := hinit c st hc hst
  noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he) _
  parity he := by simpa using (hp.p_poll (event_thread_lt hX he) hst he).2.2.1
  δ_le := Nat.zero_le _

/-- Two threads of one pair are of one cluster. -/
theorem sameCluster_of_pair (hpre : Pre P L mem0) {g h : Nat} (hg : g < L.threads)
    (hh : h < L.threads) (hc : leadCta (ctaOf L g) = leadCta (ctaOf L h)) : SameCluster L g h := by
  refine ⟨hg, hh, ?_⟩
  simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]
  unfold leadCta ctaOf at hc
  omega

/-- **PPhase**: the P-ready handoff of every stage of every pair, given the reuse premise. -/
theorem pReadyHandoff (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (hp : PReadyFacts L X) (htm : TmemFacts L X) (hinit : PReadyInit L X)
    (hR : PReadyReach L K A X) : PReadyHandoff L X := by
  intro c st hc hst
  have hsc : ∀ {a : Fin 512} {h i j pc pc' p : Nat} {acq : Bool} {sc sc' : MbarScope},
      mmaIn L c h →
      X.get (pThread L c st a, i) = some ⟨pc, .arrive (pReadyBar L c st) 0 1 true sc⟩ →
      X.get (h, j) = some ⟨pc', .wait (pReadyBar L c st) p true acq sc'⟩ →
      ScopesMeet L sc (pThread L c st a) sc' h := by
    intro a h i j pc pc' p acq sc sc' hh ha hw
    have hga := event_thread_lt hX ha
    obtain ⟨hl, -, -, -, -, rfl⟩ := hp.p_arrive hga hst ha
    obtain ⟨-, -, -, hok⟩ := hp.p_poll hh.1 hst hw
    obtain ⟨-, rfl⟩ := hok rfl
    have hcl : leadCta (ctaOf L (pThread L c st a)) = leadCta (ctaOf L h) := by
      rw [hl, hh.2.1, hc]
    exact ⟨sameCluster_of_pair hpre hga hh.1 hcl, sameCluster_of_pair hpre hh.1 hga hcl.symm⟩
  have hU := (pObj hpre hX hp htm hinit hc hst).handoff hX (hR c st hc hst)
    (fun hh he => ((hp.p_poll hh.1 hst he).2.2.2 rfl).1) hsc
  exact fun h j pc p acq sc q hh hw hq g hg =>
    hU h j pc p acq sc q hh hw hq g (pThread_of hpre hc hg)

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
