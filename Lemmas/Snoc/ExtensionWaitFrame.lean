-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Cluster.ClusterBarrierExecution

@[expose] public section

/-! Waiting edges and shuffle validity across an execution extension `X ≤ Y` that
keeps the CTA and cluster barrier histories and adds no shuffle. Endpoints named
by an unchanged history are already present in `X`, so the edges coincide. -/

namespace PTX.Proof.ExtensionWait
open PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X Y : Execution}

/-- CTA resource waits are unchanged when barrier histories and barrier keys are. -/
theorem ctaBarWaits_iff (hX : Consistent L K A mem0 X) (hle : X.le Y)
    (hb : Y.barriers=X.barriers) (hk : ∀i key,CtaBarK L Y i key ↔ CtaBarK L X i key)
    (hka : ∀i key,CtaBarArrivalK L Y i key ↔ CtaBarArrivalK L X i key)
    (e f : EvId) (b b' : Bool) :
    CtaBarWaits L Y e f b b' ↔ CtaBarWaits L X e f b b' := by
  have heget {key : Nat} {i : EvId} (hi : CtaBarK L X i key) : ∃ev,X.get i=some ev := by
    obtain ⟨_,⟨count,pc,he⟩,_⟩ := hi
    exact ⟨_,he⟩
  constructor
  · rintro ⟨_,_,hbody⟩
    have hbody' :
        (b=false ∧ b'=false ∧ ∃(c i j : Nat)(r q : CtaBarrier.Record EvId),
          (X.barriers c)[i]?=some r ∧ (X.barriers c)[j]?=some q ∧ i<j ∧
          e∈r.refs ∧ f∈q.refs) ∨
        (b=false ∧ b'=true ∧ SameCta L e.1 f.1 ∧
          ∃key,CtaBarArrivalK L X e key ∧ CtaBarK L X f key) ∨
        (b=false ∧ b'=true ∧ ∃(key i : Nat)(r : CtaBarrier.Record EvId),
          CtaBarK L X f key ∧ (X.barriers (f.1/L.block))[i]?=some r ∧ e∈r.refs ∧
          CtaBarrier.CompletesAt L.block (X.barriers (f.1/L.block)) i (key%16) (key/16)) := by
      simpa only [hb,hk,hka] using hbody
    have hp : (∃ev,X.get e=some ev) ∧ (∃ev,X.get f=some ev) := by
      rcases hbody' with ⟨_,_,c,i,j,r,q,hr,hq,_,he,hf⟩ |
        ⟨_,_,_,key,he,hf⟩ | ⟨_,_,key,i,r,hf,hr,he,_⟩
      · exact ⟨hX.ctaBar.ref_present (List.mem_of_getElem? hr) he,
          hX.ctaBar.ref_present (List.mem_of_getElem? hq) hf⟩
      · exact ⟨he.present,heget hf⟩
      · exact ⟨hX.ctaBar.ref_present (List.mem_of_getElem? hr) he,heget hf⟩
    exact ⟨hp.1,hp.2,hbody'⟩
  · rintro ⟨⟨ev,he⟩,⟨fv,hf⟩,hbody⟩
    refine ⟨⟨ev,Execution.le_get hle he⟩,⟨fv,Execution.le_get hle hf⟩,?_⟩
    simpa only [hb,hk,hka] using hbody

/-- Cluster waits are unchanged when cluster histories are. -/
theorem clusterWaits_iff (hX : Consistent L K A mem0 X) (hle : X.le Y)
    (hc : Y.clusters=X.clusters) (e f : EvId) (b b' : Bool) :
    ClusterWaits L Y e f b b' ↔ ClusterWaits L X e f b b' := by
  constructor
  · rintro ⟨_,_,hbody⟩
    rw [hc] at hbody
    have hp : (∃ev,X.get e=some ev) ∧ (∃ev,X.get f=some ev) := by
      rcases hbody with ⟨c,i,j,r,q,hr,hq,_,he,hf,_⟩ |
        ⟨_,_,c,r,hr,he,hf⟩ | ⟨_,_,phase,c,he,hf⟩ | ⟨_,_,phase,c,he,hf⟩
      · exact ⟨hX.cluster.ref_present (List.mem_of_getElem? hr) he,
          hX.cluster.ref_present (List.mem_of_getElem? hq) hf⟩
      · exact ⟨hX.cluster.ref_present hr he,hX.cluster.ref_present hr hf⟩
      · obtain ⟨pc,aligned,hget⟩ := hX.cluster.arrival_present he
        exact ⟨⟨_,hget⟩,hX.cluster.wait_present hf⟩
      · obtain ⟨pc,aligned,hget⟩ := hX.cluster.arrival_present he
        exact ⟨⟨_,hget⟩,hX.cluster.wait_present hf⟩
    exact ⟨hp.1,hp.2,hbody⟩
  · rintro ⟨⟨ev,he⟩,⟨fv,hf⟩,hbody⟩
    refine ⟨⟨ev,Execution.le_get hle he⟩,⟨fv,Execution.le_get hle hf⟩,?_⟩
    rwa [hc]

/-- Shuffle validity survives an extension that adds no shuffle event. -/
theorem shflOk (hX : Consistent L K A mem0 X) (hle : X.le Y)
    (hget : ∀{i : EvId} {pc : Nat} {m : ShflMode} {a : Value} {b c : Nat} {r : Value} {o : Bool},
      Y.get i=some ⟨pc,.shfl m a b c r o⟩ ↔ X.get i=some ⟨pc,.shfl m a b c r o⟩)
    (hk : ∀i n,Y.ShflK i n ↔ X.ShflK i n) : ShflOk L Y := by
  intro g i n pc mode a b c recv ok he hky
  obtain ⟨hok,hsrc⟩ : ok = (shflSource mode (laneOf L g) b c).2 ∧
      ((∃ j pc' b' c' r' o', X.ShflK (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) n ∧
        X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
          some ⟨pc', .shfl mode recv b' c' r' o'⟩) ∨
        ShflExited X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) n) :=
    hX.shfl g i n pc mode a b c recv ok (hget.mp he) ((hk _ _).mp hky)
  refine ⟨hok,?_⟩
  rcases hsrc with ⟨j,q,b',c',recv',ok',hkj,hg⟩ | hx
  · exact .inl ⟨j,q,b',c',recv',ok',(hk _ _).mpr hkj,hget.mpr hg⟩
  · exact .inr (Execution.shflExited_mono hle hx)

end
end PTX.Proof.ExtensionWait
