-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasExpect
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundSecondWarp
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundGateReady
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

theorem warmBiasSiteCount_mono (X : Execution) {t a b : Nat} (k : Fin 6) (h : a ≤ b) :
    warmBiasSiteCount X t a k ≤ warmBiasSiteCount X t b k :=
  countP_take_mono _ (X.tr t) h

private theorem holdsOfMembers {R : Nat → Option Value} {F : List (Nat × Value)}
    (h : ∀ rv ∈ F, R rv.1 = some rv.2) : Holds R F := by
  induction F with
  | nil => trivial
  | cons rv rest ih =>
    cases rv with
    | mk r v =>
      exact ⟨h (r,v) (List.mem_cons_self ..),
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

private theorem holdsFilter {R : Nat → Option Value} {F : List (Nat × Value)}
    (q : Nat × Value → Bool) (h : Holds R F) : Holds R (F.filter q) :=
  holdsOfMembers (fun _ hm => holds_mem h (List.mem_filter.mp hm).1)

private theorem uniqueKey {F : List (Nat × Value)} {k : Nat} {v w : Value}
    (h : (F.map Prod.fst).count k = 1) (hv : (k,v) ∈ F) (hw : (k,w) ∈ F) : v = w := by
  induction F with
  | nil => simp at hv
  | cons rv rest ih =>
    obtain ⟨r,x⟩ := rv
    simp only [List.map_cons,List.count_cons] at h
    by_cases hr : r = k
    · subst hr
      simp only [beq_self_eq_true,ite_true] at h
      have hz : (rest.map Prod.fst).count r = 0 := by omega
      have hNot (y : Value) (hy : (r,y) ∈ rest) : False := by
        have : 0 < (rest.map Prod.fst).count r :=
          List.count_pos_iff.mpr (List.mem_map_of_mem (f := Prod.fst) hy)
        omega
      rcases List.mem_cons.mp hv with hv | hv <;> rcases List.mem_cons.mp hw with hw | hw
      · rw [(Prod.mk.inj hv).2,(Prod.mk.inj hw).2]
      · exact (hNot _ hw).elim
      · exact (hNot _ hv).elim
      · exact (hNot _ hv).elim
    · have hb : (r == k) = false := beq_eq_false_iff_ne.mpr hr
      simp only [hb,Bool.false_eq_true,ite_false,Nat.add_zero] at h
      rcases List.mem_cons.mp hv with hv | hv
      · exact absurd (Prod.mk.inj hv).1.symm hr
      rcases List.mem_cons.mp hw with hw | hw
      · exact absurd (Prod.mk.inj hw).1.symm hr
      exact ih h hv hw

/-- The registers of the V carry other than the two Bias phases. -/
def warmBiasRest (q : Nat × Value) : Bool := q.1 != 7177 && q.1 != 7178

theorem warmRoundVCarry_rest (p : Params) (l : Launch) (g batch round lane : Nat)
    (b b' : Value) :
    (warmRoundVCarry p l g batch round b lane).filter warmBiasRest =
      (warmRoundVCarry p l g batch round b' lane).filter warmBiasRest := by
  simp [warmRoundVCarry,List.filter_append,warmBiasRest]

set_option maxRecDepth 4096 in
private theorem vCarryBiasCount (p : Params) (l : Launch) (g batch round lane : Nat)
    (b : Value) (k : Nat) (hk : k = 7177 ∨ k = 7178) :
    ((warmRoundVCarry p l g batch round b lane).map Prod.fst).count k = 1 := by
  rcases hk with rfl | rfl <;> (set_option maxRecDepth 100000 in rfl)

set_option maxRecDepth 4096 in
private theorem stageOneFrameHolds {p : Params} {l : Launch} {g batch round lane : Nat}
    {R : Nat → Option Value}
    (h : Holds R (warmRoundBiasStageFrame p l g batch round 1 lane)) :
    Holds R (warmRoundValueCarry p l g batch round lane) :=
  h.2.2.2.2

set_option maxRecDepth 4096 in
/-- The two Bias phase flips at the end of warp 14's Bias block and the V barrier operands
bring the warp to the V poll with the next round's Bias phases. -/
theorem warmRoundBiasFlipLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch round lane : Nat} (hw : warpIndex l g = 14) {s : TState}
    (hs : At s 1201 (warmRoundBiasStageFrame p l g batch round 1 lane)) :
    let use := cacheUseOfRound round
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) s u ∧
      At u (recurringEmptyWait 1).pc
        (recurringBarrierFacts l 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1)) ++
          warmRoundVCarry p l g batch round
            (loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1))) lane) := by
  intro use
  let t := warpLane l g lane
  let b := loaderPhaseWord (warmBiasPhase (warpIndex l g) round)
  let b' := loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1))
  let C := warmRoundVCarry p l g batch round b lane
  let R := C.filter warmBiasRest
  have hC : Holds s.regs C := stageOneFrameHolds hs.2.2.2.2
  have hB : b = b32 (round%2) := by simp only [b,hw]; exact warmBiasPhaseWord round
  have hB' : b' = b32 ((round+1)%2) := by simp only [b',hw]; exact warmBiasPhaseWord (round+1)
  have h78 : s.regs 7178 = some b := holds_mem hC (by
    simp [C,warmRoundVCarry])
  have h77 : s.regs 7177 = some b := holds_mem hC (by
    simp [C,warmRoundVCarry])
  have hSeg : Seg kernel [] l t 2 1201 [(7178,b),(7177,b)] 1203 [(7178,b'),(7177,b')] := by
    rw [hB,hB']
    rcases Nat.mod_two_eq_zero_or_one round with h | h
    · have h' : (round+1)%2 = 1 := by omega
      rw [h,h']
      intro a ha
      seg_fp ha using rfl
    · have h' : (round+1)%2 = 0 := by omega
      rw [h,h']
      intro a ha
      seg_fp ha using rfl
  obtain ⟨v,hv,hV⟩ := roundStraightFrame (F := R) (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg
    (hs.mono ((holds_append ..).mpr ⟨⟨h78,h77,trivial⟩,holdsFilter _ hC⟩))
  have hParts := (holds_append ..).mp hV.2.2.2.2
  have hNew : Holds v.regs (warmRoundVCarry p l g batch round b' lane) := by
    apply holdsOfMembers
    intro rv hm
    by_cases hq : warmBiasRest rv = true
    · have hIn : rv ∈ R := by
        change rv ∈ C.filter warmBiasRest
        rw [warmRoundVCarry_rest p l g batch round lane b b']
        exact List.mem_filter.mpr ⟨hm,hq⟩
      exact holds_mem hParts.2 hIn
    · obtain ⟨k,x⟩ := rv
      have hk : k = 7177 ∨ k = 7178 := by
        simp only [warmBiasRest,Bool.and_eq_true,bne_iff_ne,ne_eq,not_and_or,
          not_not] at hq
        exact hq
      have hSelf : (k,b') ∈ warmRoundVCarry p l g batch round b' lane := by
        rcases hk with rfl | rfl <;> simp [warmRoundVCarry]
      have hx := uniqueKey (vCarryBiasCount p l g batch round lane b' k hk) hm hSelf
      rw [hx]
      rcases hk with rfl | rfl
      · exact hParts.1.2.1
      · exact hParts.1.1
  have hWords : Holds v.regs
      [(1139,b32 (kvUseStage (use+1)).val),(2064,loaderPhaseWord (kvEmptyPhase (use+1)))] := by
    have h : Holds v.regs (recurringVTransitionFacts 0 (kvUseStage use) (kvEmptyPhase use)) :=
      ((holds_append ..).mp hNew).1
    rwa [vTransitionWordsOfUse] at h
  have hIn : At v 1203
      (recurringBarrierInput l 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1)) ++
        warmRoundVCarry p l g batch round b' lane) := by
    refine hV.mono ((holds_append ..).mpr ⟨⟨hWords.1,holds_mem hNew ?_,hWords.2.1,
      trivial⟩,hNew⟩)
    simp [warmRoundVCarry,openingWarmFrame,warmStartFrame]
  obtain ⟨u,hu,hU⟩ := roundStraightFrameAll (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (recurringBarrierPrep hp (g := t) 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1))) hIn
  exact ⟨u,(run_rtg hv).trans (run_rtg hu),hU⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
