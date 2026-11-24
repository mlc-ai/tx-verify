-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyObj
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2

@[expose] public section

/-! # The second P-ready objects are unit objects

Stage `st`'s second P-ready object of the pair led by CTA `c` (`pReady2Bar`, count 8) is arrived
on once per tile by one lane of each of the stage's 4 softmax warps of each CTA of the pair: the
lane each of the warp's elections of all lanes returned. Elections of one warp with one mask
return one leader (DEP-WARP-ELECT, `selected_elect_thread_unique`), so the threads of a warp that
arrive on the object are one thread. Producer `a` of the 8 (`p2Prod`) is that thread of warp
`a` (CTA `c + a / 4`, warp `4 st + a % 4`), when the warp arrived; any thread of the warp else.

So the object is a unit object (`MbarRing.Unit.Obj`, offset 0) of the 8 producers (`p2Obj`), from
the thread layer's facts (`P2Facts`) and its only initialization (`P2Init`, a premise as
`PReadyInit`). **The handoff** (`p2Handoff`): the MMA warp's poll with `u` earlier successful
polls synchronizes with each producer's arrival with `u` earlier ones, when the MMA warp's polls
enable the producers' later arrivals (`P2Reach`, a premise as `PReadyReach`, whose enabling paths
cross the S-full objects). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- Thread `g` is of warp `a` (of 8) of stage `st`'s softmax in the pair led by `c`. -/
def InP2Warp (L : Launch) (c st : Nat) (a : Fin 8) (g : Nat) : Prop :=
  g < L.threads ∧ ctaOf L g = c + a.val / 4 ∧ warpOf L g = 4 * st + a.val % 4

/-- Thread `g` arrives on stage `st`'s second P-ready object of CTA `c`. -/
def P2Arrives (L : Launch) (X : Execution) (c st g : Nat) : Prop :=
  ∃ k pc tx cnt rel sc, X.get (g, k) = some ⟨pc, .arrive (pReady2Bar L c st) tx cnt rel sc⟩

open Classical in
/-- Producer `a` of stage `st`'s second P-ready object of the pair led by `c`: the thread of warp
`a` that arrives on it, or the warp's first thread when none does. -/
def p2Prod (L : Launch) (X : Execution) (c st : Nat) (a : Fin 8) : Nat :=
  if h : ∃ g, InP2Warp L c st a g ∧ P2Arrives L X c st g then Classical.choose h
  else (c + a.val / 4) * L.block + 32 * (4 * st + a.val % 4)

/-- **The initialization premise** of the second P-ready objects: each history starts with its
only initialization, without fault, with count 8. -/
def P2Init (L : Launch) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 → PairTmaRing.InitFirst X (pReady2Bar L c st) 8

/-- **The reuse premise** of the second P-ready objects: each MMA lane's polls of the object for
the uses before `t` enable each producer's arrival of use `t`. -/
def P2Reach (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 → ∀ h, mmaIn L c h →
    MbarRing.Unit.Reach L K A X (pReady2Bar L c st) 8 (p2Prod L X c st) 0 h

/-- **The handoff** of every stage's second P-ready object of every pair. -/
def P2Handoff (L : Launch) (X : Execution) : Prop :=
  ∀ c st, leadCta c = c → st < 2 →
    MbarRing.UnitHandoff L X (pReady2Bar L c st) (fun g => ∃ a, g = p2Prod L X c st a)
      (mmaIn L c) 0

/-- A producer is of its warp. -/
theorem p2Prod_spec (hpre : Pre P L mem0) {c st : Nat} (hst : st < 2) (a : Fin 8) :
    ctaOf L (p2Prod L X c st a) = c + a.val / 4 ∧
      warpOf L (p2Prod L X c st a) = 4 * st + a.val % 4 := by
  unfold p2Prod
  split
  · next h => exact ⟨(Classical.choose_spec h).1.2.1, (Classical.choose_spec h).1.2.2⟩
  · have ha := a.isLt
    unfold ctaOf warpOf
    rw [hpre.block]
    omega

theorem p2Prod_inj (hpre : Pre P L mem0) (c : Nat) {st : Nat} (hst : st < 2) :
    Function.Injective (p2Prod L X c st) := by
  intro a b h
  have ha := p2Prod_spec (X := X) hpre (c := c) hst a
  have hb := p2Prod_spec (X := X) hpre (c := c) hst b
  rw [h] at ha
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  omega

/-- Two threads of one CTA and warp position are of one warp. -/
theorem sameWarp_of {g h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hc : ctaOf L g = ctaOf L h) (hw : warpOf L g = warpOf L h) : SameWarp L g h :=
  ⟨⟨hg, hh, hc⟩, hw⟩

/-- **The threads of a warp that arrive on a second P-ready object are one thread.** -/
theorem p2_arrive_unique (hX : Consistent L K A mem0 X) (hF : P2Facts L X) {g g' c st : Nat}
    (hst : st < 2) (hw : SameWarp L g g') (hg : P2Arrives L X c st g)
    (hg' : P2Arrives L X c st g') : g = g' := by
  obtain ⟨k, pc, tx, cnt, rel, sc, hk⟩ := hg
  obtain ⟨k', pc', tx', cnt', rel', sc', hk'⟩ := hg'
  obtain ⟨-, -, -, -, -, -, -, -, -, e, pce, inst, -, he⟩ := hF.p2_arrive hw.1.1 hst hk
  obtain ⟨-, -, -, -, -, -, -, -, -, e', pce', inst', -, he'⟩ :=
    hF.p2_arrive hw.1.2.1 hst hk'
  exact selected_elect_thread_unique (e := (g, e)) (f := (g', e')) hX.elect he he' hw rfl rfl

/-- An arriving thread of warp `a` is producer `a`. -/
theorem p2Prod_eq (hX : Consistent L K A mem0 X) (hF : P2Facts L X) {g c st : Nat} {a : Fin 8}
    (hst : st < 2) (hin : InP2Warp L c st a g) (ha : P2Arrives L X c st g) :
    g = p2Prod L X c st a := by
  have hex : ∃ g, InP2Warp L c st a g ∧ P2Arrives L X c st g := ⟨g, hin, ha⟩
  unfold p2Prod
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨⟨hg', hc', hw'⟩, harr⟩ := Classical.choose_spec hex
  exact p2_arrive_unique hX hF hst (sameWarp_of hin.1 hg' (hin.2.1.trans hc'.symm)
    (hin.2.2.trans hw'.symm)) ha harr

/-- **An arriving thread is a producer.** -/
theorem p2Prod_of (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (hF : P2Facts L X)
    {g c st : Nat} (hc : leadCta c = c) (hst : st < 2) (hg : g < L.threads)
    (ha : P2Arrives L X c st g) : ∃ a, g = p2Prod L X c st a := by
  obtain ⟨k, pc, tx, cnt, rel, sc, hk⟩ := ha
  obtain ⟨hl, hw8, hws, -⟩ := hF.p2_arrive hg hst hk
  have hb := hpre.block
  have hlt : 4 * (ctaOf L g - c) + warpOf L g % 4 < 8 := by
    unfold leadCta at hl hc
    omega
  refine ⟨⟨_, hlt⟩, p2Prod_eq hX hF hst ⟨hg, ?_, ?_⟩ ⟨k, pc, tx, cnt, rel, sc, hk⟩⟩ <;>
    simp only <;> unfold leadCta at hl hc <;> omega

/-- **Stage `st`'s second P-ready object of the pair led by `c` is a unit object** of its 8
producers. -/
theorem p2Obj (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (hF : P2Facts L X)
    (htm : TmemFacts L X) (hinit : P2Init L X) {c st : Nat} (hc : leadCta c = c)
    (hst : st < 2) : MbarRing.Unit.Obj X (pReady2Bar L c st) 8 (p2Prod L X c st) 0 where
  pos := by decide
  inj := p2Prod_inj hpre c hst
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (htm.no_inval he).elim
    | @arrive g j pc tx cnt rel sc hid he ha =>
      have hg := event_thread_lt hX he
      obtain ⟨-, -, -, rfl, rfl, rfl, -⟩ := hF.p2_arrive hg hst he
      exact .arrive hid (p2Prod_of hpre hX hF hc hst hg ⟨j, pc, 0, 1, true, sc, he⟩) he ha
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact (hF.p2_tensor hst he hm).elim
    | increment _ he _ => exact (htm.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
    | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
    | commit _ he htg _ => exact (hF.p2_commit hst he htg).elim
    | clc _ he _ _ _ => exact (htm.no_clc he).elim
  init := hinit c st hc hst
  noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he) _
  parity he := by simpa using (hF.p2_poll (event_thread_lt hX he) hst he).2.2.1
  δ_le := Nat.zero_le _

/-- **The handoff** of every stage's second P-ready object of every pair, given the reuse
premise. -/
theorem p2Handoff (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (hF : P2Facts L X)
    (htm : TmemFacts L X) (hinit : P2Init L X) (hR : P2Reach L K A X) : P2Handoff L X := by
  intro c st hc hst
  have hsc : ∀ {a : Fin 8} {h i j pc pc' p : Nat} {acq : Bool} {sc sc' : MbarScope},
      mmaIn L c h →
      X.get (p2Prod L X c st a, i) = some ⟨pc, .arrive (pReady2Bar L c st) 0 1 true sc⟩ →
      X.get (h, j) = some ⟨pc', .wait (pReady2Bar L c st) p true acq sc'⟩ →
      ScopesMeet L sc (p2Prod L X c st a) sc' h := by
    intro a h i j pc pc' p acq sc sc' hh ha hw
    have hga := event_thread_lt hX ha
    obtain ⟨hl, -, -, -, -, -, rfl, -⟩ := hF.p2_arrive hga hst ha
    obtain ⟨-, -, -, hok⟩ := hF.p2_poll hh.1 hst hw
    obtain ⟨-, rfl⟩ := hok rfl
    have hcl : leadCta (ctaOf L (p2Prod L X c st a)) = leadCta (ctaOf L h) := by
      rw [hl, hh.2.1, hc]
    exact ⟨sameCluster_of_pair hpre hga hh.1 hcl, sameCluster_of_pair hpre hh.1 hga hcl.symm⟩
  exact (p2Obj hpre hX hF htm hinit hc hst).handoff hX (hR c st hc hst)
    (fun hh he => ((hF.p2_poll hh.1 hst he).2.2.2 rfl).1) hsc

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
