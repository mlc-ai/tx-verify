-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFCtl
public import Lemmas.Flow.SegQPre
public import Lemmas.Flow.StepsQFP
public import Lemmas.Flow.TypedIntG

@[expose] public section

/-! # Pieces of the strict lane that every role shares

A span that starts at the facts `F'` starts at any facts that imply them (`SegQ.fromFacts`), the
span of a lane under the table `qt` (`SegQ.laneConv`), a step that may use the invariant of its
machine (`Code.StepForQP.ofInv`), and the tactic `lane_ctl` for a stretch that writes registers of
the facts: `segqf_ctlt` with the soundness and plain-segments proofs of a `FloatPlain3` range. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Flow.TyG PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {Q : TState → Prop}

theorem SegQ.fromFacts {a b : Nat} {F F' G : List (Nat × Value)} (hs : ∀ p ∈ F', p ∈ F)
    (h : SegQ K A L g Q a F' b G) : SegQ K A L g Q a F b G :=
  (SegQ.weaken (fun _ hR => holds_of_forall fun p hp => holds_mem hR (hs p hp))).comp h

/-- A span between facts that imply its start and are implied by its end, in the lane's
invariant. -/
theorem SegQ.laneConv {qt : Nat → EnvF} {a b : Nat} {F F' G G' : List (Nat × Value)}
    (R : TState → Prop) (hs : ∀ p ∈ F', p ∈ F) (ht : ∀ p ∈ G, p ∈ G')
    (h : SegQ K A L g (QTF qt) a F' b G') :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) a F b G :=
  SegQ.tauAll R ((SegQ.fromFacts hs h).comp
    (SegQ.weaken (fun _ hR => holds_of_forall fun p hp => holds_mem hR (ht p hp))))

theorem Code.StepForQP.ofInv {C : Code K A L g} {P : TState → Prop} {Wf : Event → Prop}
    {d : C.D} {ev : Event} (h : C.inv d → C.StepForQP Q P Wf d ev) : C.StepForQP Q P Wf d ev :=
  fun ins ha hi hc hq hw hf hp => h hi ins ha hi hc hq hw hf hp

end PTX.Flow

namespace PTX.Flow.TyG

set_option hygiene false in
/-- A strict stretch under `QTF qt` whose written registers are facts: `hp` is the `FloatPlain3`
range of the stretch, `hf` the frame of the rules. -/
macro "lane_ctl " qt:term:max ", " hp:term:max ", " hf:term:max " using " vals:tacticSeq :
    tactic => `(tactic| segqf_ctlt $qt, (absF5_sound $hp), ($hp).plain.plain.segs, $hf using $vals)

end PTX.Flow.TyG
