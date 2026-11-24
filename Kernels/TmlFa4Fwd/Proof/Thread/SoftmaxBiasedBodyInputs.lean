-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedVisitBody
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedAffineProgress
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Lemmas.Flow.SplitJoin
import Lemmas.Flow.Widen
import Lemmas.Flow.Regs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction

/-- The packed ABI scale of the Bias body is the actual inverse scale on both halves. -/
theorem biasBodyScale {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    {s : TState} (h : s.regs 7896 = some (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits))) :
    readERealPair l g s (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))) := by
  obtain ⟨_,inv,_,hDecode,_,_⟩ := hp.scales
  have bits := (hp.values (14,p.invScaleBits) (by simp [Params.scalarWords])).1
  have val := valFloat_b32 (by omega) hDecode
  have halves : splitValue 64 (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) =
      (b32 p.invScaleBits,b32 p.invScaleBits) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact bits)
  rw [show abiFloat p.invScaleBits = (inv : ℝ) by simp [abiFloat,hDecode]]
  exact readERealPair_reg h (by rw [halves]; exact val) (by rw [halves]; exact val)

/-- The kept loop registers of a repeated biased visit form the affine input frame. -/
theorem biasBodyPrior {p : Params} {l : Launch} {g visit block floor counter : Nat}
    {warp : Fin 8} (hw : warp.val = warpIndex l g) {maximum : Option ℝ} {sum : ℝ}
    {s : TState} (h : Holds s.regs (biasedBiasFacts p l g visit block maximum sum floor counter)) :
    Holds s.regs (biasedAffineInputFrame p l warp maximum sum ((block+(2^32-1))%2^32) floor
      (visit%2) (b32 (visit%2)) (b32 (visit%2)) (b32 counter)) := by
  apply frameOfFacts
  intro pair hPair
  apply holds_mem h
  simp only [biasedAffineInputFrame,List.mem_cons,List.not_mem_nil,or_false] at hPair
  rw [hw] at hPair
  rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    simp [biasedBiasFacts,biasedHeadKept,openingDenominatorRegisters]

/-- A thread of the given CTA in one of the four softmax warps of a stage. -/
def BiasedStageMember (l : Launch) (cta : Nat) (stage : Fin 2) (g : Nat) : Prop :=
  g < l.threads ∧ g/l.block = cta ∧ warpIndex l g < 8 ∧ warpIndex l g/4 = stage.val

/-- The softmax warp of a thread, as an index below eight. -/
def warpOf (l : Launch) (g : Nat) : Fin 8 := ⟨warpIndex l g % 8,Nat.mod_lt _ (by decide)⟩

theorem warpOf_val {l : Launch} {g : Nat} (h : warpIndex l g < 8) :
    (warpOf l g).val = warpIndex l g := Nat.mod_eq_of_lt h

theorem BiasedStageMember.warp {l : Launch} {cta g : Nat} {stage : Fin 2}
    (h : BiasedStageMember l cta stage g) : (warpOf l g).val = warpIndex l g :=
  warpOf_val h.2.2.1

theorem BiasedStageMember.stage {l : Launch} {cta g : Nat} {stage : Fin 2}
    (h : BiasedStageMember l cta stage g) : stageOf (warpOf l g) = stage :=
  Fin.ext (by change (warpOf l g).val/4 = stage.val; rw [h.warp]; exact h.2.2.2)

/-- `stageBiasedBodiesOfRows` indexed by thread rather than by lane. -/
theorem stageBiasedBodiesOfThreadRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {cta : Nat} (hCta : cta < l.grid)
    (stage : Fin 2) (visit : Nat)
    (block floor counter bars elects : Nat → Nat) (maximum : Nat → Option ℝ) (sum : Nat → ℝ)
    (rows : ∀ g, BiasedStageMember l cta stage g →
      BiasedBiasRow p l X g (warpOf l g) visit (block g) (floor g) (counter g) (bars g)
        (elects g) (maximum g) (sum g)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      Y.MemWrites = X.MemWrites ∧
      ∀ g (hm : BiasedStageMember l cta stage g),
        let r := rows g hm
        ∃ bias : Nat → Option ℝ,
          ∃ after : OpeningTripCursor l Y g (biasBodyStart true)
            (Scores.repeatedBiasFencePack p l g (warpOf l g) ++
              (repeatedBiasPackFrame r.scores.words ++
                biasedBiasFacts p l g visit (block g) (maximum g) (sum g) (floor g)
                  (counter g))),
            after.ending = r.cursor.ending ∧
            after.pos = (if laneOf l g = 0 then r.cursor.pos+67 else r.cursor.pos+66) ∧
            (laneOf l g = 0 → Y.get (g,r.cursor.pos+66) = some ⟨5278,
              .arrive (signalLoc l g stage (biasReleaseSite true)) 0 1 true .cta⟩) ∧
            SoftmaxCounts Y g after.pos (11*visit+4) (bars g) (elects g) visit (visit+1)
              (visit+1) ∧
            ∀ i : Fin 16, BiasUnpacked true i after.ready (fun k =>
              biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))) := by
  have hb : 0 < l.block := by rw [hp.block]; decide
  have member (lane : Nat) (hl : lane < l.block) (hm : lane/32 ∈ biasParticipants stage) :
      BiasedStageMember l cta stage (cta*l.block+lane) := by
    obtain ⟨hc,hr⟩ := NamedBar.lane_cta (c := cta) hb hl
    have hw : warpIndex l (cta*l.block+lane) = lane/32 := by unfold warpIndex; rw [hr]
    have hmem := (biasParticipantIff stage (lane/32)).mp hm
    exact ⟨NamedBar.cta_thread_lt hCta hl,hc,hw ▸ hmem.1,hw ▸ hmem.2⟩
  obtain ⟨Y,hY,hTrace,hObjects,hWrites,out⟩ := stageBiasedBodiesOfRows hp hMax hFootprint hCta
    stage visit (fun lane => warpOf l (cta*l.block+lane))
    (fun lane hl hm => (member lane hl hm).warp)
    (fun lane hl hm => (member lane hl hm).stage)
    (fun lane => block (cta*l.block+lane)) (fun lane => floor (cta*l.block+lane))
    (fun lane => counter (cta*l.block+lane)) (fun lane => bars (cta*l.block+lane))
    (fun lane => elects (cta*l.block+lane)) (fun lane => maximum (cta*l.block+lane))
    (fun lane => sum (cta*l.block+lane))
    (fun lane hl hm => rows _ (member lane hl hm))
  refine ⟨Y,hY,hTrace,hObjects,hWrites,?_⟩
  intro g hm
  have hl : g%l.block < l.block := Nat.mod_lt _ hb
  have hg : cta*l.block+g%l.block = g := by
    rw [← hm.2.1, Nat.mul_comm]; exact Nat.div_add_mod ..
  have hmem : (g%l.block)/32 ∈ biasParticipants stage := by
    apply (biasParticipantIff stage _).mpr
    have hw : warpIndex l g = (g%l.block)/32 := rfl
    exact ⟨hw ▸ hm.2.2.1,hw ▸ hm.2.2.2⟩
  obtain ⟨lane,hl',rfl⟩ : ∃ lane, lane < l.block ∧ g = cta*l.block+lane :=
    ⟨g%l.block,hl,hg.symm⟩
  have hmem' : lane/32 ∈ biasParticipants stage := by
    have := NamedBar.lane_cta (c := cta) hb hl'
    rwa [this.2] at hmem
  exact out lane hl' hmem'

end PTX.Kernels.TmlFa4Fwd.Softmax
