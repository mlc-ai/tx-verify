-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
import Kernels.InklingRelDecode.Gen.StepDispatch
import Lemmas.Flow.SegPieces
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Proof PTX.Flow

noncomputable section

local macro "byte_frame" h:term : tactic => `(tactic| seg_fp $h using rfl)

private abbrev liveFacts (val : Nat → Value) (pc : Nat) := factsFrom (Flow.live pc) val

private theorem compareByte (val : Nat → Value) (y : BitVec 64) {L : Launch} {g : Nat} :
    Seg kernel Assumptions.all L g 1 2341 ((535, .bits 32 y) :: liveFacts val 2340) 2342
      ((5, .pred (decide (3 < (truncBits 32 y).toNat))) ::
        (535, .bits 32 y) :: liveFacts val 2340) := by
  intro t h
  seg_fp h using (simp [PTX.compare]; rfl)

private theorem keepTarget (k : Nat) :
    ∀ r ∈ Flow.live (target k).pc, r ∈ Flow.live 2340 := by
  match k with
  | 0 | 1 | 2 | 3 | _ + 4 => simp only [target, Site.pc]; decide

private theorem byteRoute {L : Launch} {g : Nat} (val : Nat → Value) (y : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 2341 ((535, .bits 32 y) :: liveFacts val 2340)
      (target (truncBits 32 y).toNat).pc (liveFacts val (target (truncBits 32 y).toNat).pc) := by
  let k := (truncBits 32 y).toNat
  have htest := compareByte (L := L) (g := g) val y
  change Seg kernel Assumptions.all L g 1 _ _ _ ((5, .pred (decide (3 < k))) :: _) at htest
  by_cases h : 3 < k
  · rw [decide_eq_true h] at htest
    have hpc : (target k).pc = 2557 := by
      match k, h with
      | _ + 4, _ => rfl
    refine ⟨1 + 1, htest.comp ?_⟩
    rw [hpc]
    intro t ht
    byte_frame ht
  · rw [decide_eq_false h] at htest
    have htgt : [2344, 2422, 2333, 2853][k]? = some (target k).pc := by
      interval_cases k <;> rfl
    let F := (5, Value.pred false) :: (535, Value.bits 32 y) :: liveFacts val 2340
    have hb : Seg kernel Assumptions.all L g 1 2342 F 2343 F := by
      dsimp only [F]
      intro t h
      byte_frame h
    have hj : Seg kernel Assumptions.all L g 1 2343 F (target k).pc F :=
      Seg.brxIdx Flow.code_2343 (List.mem_cons_of_mem _ List.mem_cons_self) rfl htgt
        (fun t _ a ha => by
          simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
            Assumptions.negExact]) (segFree (by decide))
    refine ⟨1 + (1 + 1), htest.comp (hb.comp (hj.weaken_end ?_))⟩
    rintro _ ⟨_, _, hr⟩
    exact holds_factsFrom_mono hr (keepTarget k)

theorem read_step {L : Launch} {g first round : Nat} {regs : Nat → Value} {x : BitVec 64} :
    (code L g regs x first).StepAt ⟨.read, round⟩ := by
  refine ⟨fun _ => ⟨_, Flow.code_2340, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2340)
  obtain ⟨a, bs, rfl, rfl⟩ := Code.fires_accessLoad (by rfl) (by rfl) (by rfl) hf
  let F := liveFacts (valueOf L g x regs) 2340
  have h : At t 2340 F := hat
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [code, next, readTarget, Except.toOption, hv],
      Machine.dead_of_fault (f := f)
      (by simp [afterAccessLoad, hv, bind, Except.bind])⟩
  | ok v =>
    cases hb : v.bitPattern with
    | none =>
      have he : extendLoaded (.zero 32) 8 v = .error .typeMismatch := by
        simp [extendLoaded, hb]; rfl
      refine .inr ⟨by simp [code, next, readTarget, Except.toOption, hv, he],
        Machine.dead_of_fault (f := .typeMismatch) ?_⟩
      change (afterAccessLoad t (.zero 32) 8 [535] bs).fault = _
      simp [afterAccessLoad, hv, he, bind, Except.bind]
    | some bits =>
      let y := truncBits 8 (BitVec.ofNat 64 bits)
      have he : extendLoaded (.zero 32) 8 v = .ok (.bits 32 y) := by
        simp only [extendLoaded, hb]; rfl
      have hn : (code L g regs x first).next ⟨.read, round⟩ ⟨2340, .rd a bs⟩ =
          some (some ⟨target (truncBits 32 y).toNat, round⟩) := by
        simp [code, next, readTarget, Except.toOption, hv, he]
      have ht : At (afterAccessLoad t (.zero 32) 8 [535] bs) 2341
          ((535, .bits 32 y) :: F) := by
        obtain ⟨_, hsub, hacc, _, _⟩ := hat
        have ha : afterAccessLoad t (.zero 32) 8 [535] bs =
            PTX.next (setReg t 535 (.bits 32 y)) := by
          simp [afterAccessLoad, hv, he, bind, Except.bind, hsub, hacc, PTX.next, setRegs, setReg]
        rw [ha]
        apply At.set h
        intro p hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        exact (show ∀ q ∈ Flow.live 2340, q ≠ 535 by decide) r hr
      obtain ⟨n, hseg⟩ := byteRoute (L := L) (g := g) (valueOf L g x regs) y
      obtain ⟨t', run', at'⟩ := hseg _ ht
      refine .inl (.inr ⟨_, t', hn, run_rtg run', at', ?_⟩)
      change target _ = .exitDealloc → _
      generalize (truncBits 32 y).toNat = k
      match k with
      | 0 | 1 | 2 | 3 | _ + 4 => intro hs; cases hs

end
end PTX.Kernels.InklingRelDecode.Proof.Dispatch
