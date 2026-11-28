-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Kernels.InklingRelDecode.Proof.Common.Export.WarpRel
public import Kernels.InklingRelDecode.Proof.Common.ScriptFacts
public import Lemmas.Kernel.Progress.WarpCls
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
public import Kernels.InklingRelDecode.Proof.Lib.Block
import Lemmas.Flow.NotBulk
import Lemmas.Kernel.FrameU
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # A warp's classification from the facts of its states

`warpCls_of` builds the `Sched.WarpCls` of a warp from a state-level fact `F x σ c` (the state `σ`
of lane `x` has made `c` collectives, as far as the role says), the three consequences of it for
the state (`state`), the script's rising slots, the exit and the two release facts. What is the
same for every warp is here: that a collective event is fired from a state at a collective and
that the exit is at pc 2855. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A blocking event leaves a state that is at no collective. -/
theorem Lib.not_coll {g} {e : Event} {σ0 : ((schedule Q L).code g).D}
    (hb : e.pc ∈ Lib.blockPcs) (hpc : e.pc = ((schedule Q L).code g).pc σ0) :
    ¬ CollAt Q L g σ0 := fun ⟨ins, hc, hk⟩ => by
  have := Lib.blockPcs_not_warp e.pc hb
  rw [hpc, hc] at this
  simp [hk] at this

/-- A state is read at a position no later than the lane's trace. -/
theorem clip_state {C : (g : Nat) → Flow.Code kernel Assumptions.all L g} {x k : Nat}
    {σ : (C x).D} (hs : Frame.stateAt C X x k = some (some σ)) :
    ∃ k' ≤ (X.tr x).length, Frame.stateAt C X x k' = some (some σ) ∧
      Sched.collCount X x k' = Sched.collCount X x k := by
  by_cases h : k ≤ (X.tr x).length
  · exact ⟨k, h, hs, rfl⟩
  · have h' : (X.tr x).length ≤ k := by omega
    exact ⟨_, le_rfl, (Frame.stateAt_of_le h').symm.trans hs, by
      simp only [Sched.collCount, List.take_of_length_le h', List.take_length]⟩

theorem collAt_iff_warp {x} {σ : ((schedule Q L).code x).D} :
    CollAt Q L x σ ↔ isWarpAt (((schedule Q L).code x).pc σ) = true := by
  unfold CollAt isWarpAt
  cases h : kernel.code[((schedule Q L).code x).pc σ]? <;> simp

/-- A warp collective event is fired from a state at a warp instruction. -/
theorem coll_isP {x k e} {σ : ((schedule Q L).code x).D} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hs : Frame.stateAt (schedule Q L).code X x k = some (some σ))
    (he : X.get (x, k) = some e) (hc : Sched.isWarpColl e = true) : CollAt Q L x σ := by
  have hu : ∀ f, e.kind ≠ .ub f := fun f hf => by
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    simp [Sched.isWarpColl] at hc
  obtain ⟨t, ins, o, -, -, hins, hf⟩ :=
    Frame.fired_siteU (C := thread Q L) (fun _ hg => thread_sound hp hg) hX he hs hu
  exact ⟨ins, hins, coll_warp_op hf hc⟩

/-- An exit event is fired from a state at pc 2855. -/
theorem exit_state_pc {x k pc} {σ : ((schedule Q L).code x).D} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hs : Frame.stateAt (schedule Q L).code X x k = some (some σ))
    (he : X.get (x, k) = some ⟨pc, .exit⟩) : ((schedule Q L).code x).pc σ = 2855 := by
  obtain ⟨t, ins, o, -, -, hins, hf⟩ :=
    Frame.fired_siteU (C := thread Q L) (fun _ hg => thread_sound hp hg) hX he hs (fun _ => nofun)
  have := Lib.ret_pc' hins hf rfl
  simp only [Lib.retPcs, List.mem_singleton] at this
  exact this

/-- **The classification of a warp** from the facts of its states. -/
theorem warpCls_of {P : Nat → Prop} {F : ∀ x, ((schedule Q L).code x).D → Nat → Prop}
    {cn : Nat → Option Nat} {slot : Nat → Nat} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (state : ∀ {x σ c}, F x σ c →
      (CollAt Q L x σ ↔ cn c = some (((schedule Q L).code x).pc σ)) ∧
      (CollAt Q L x σ → (schedule Q L).time x σ = slot c) ∧
      (¬ CollAt Q L x σ → ∀ n, (cn n).isSome = true → c ≤ n →
        (schedule Q L).time x σ < slot n))
    (count : ∀ {x k σ}, P x → Frame.stateAt (schedule Q L).code X x k = some (some σ) →
      F x σ (Sched.collCount X x k))
    (mono : ∀ {a b}, a < b → (cn b).isSome = true → slot a < slot b)
    (exit : ∀ {x σ c}, F x σ c → ((schedule Q L).code x).pc σ = 2855 →
      ∀ n, (cn n).isSome = true → n < c)
    (released : WarpRel Q L m X P) (dead : WarpDead Q L X P) :
    Sched.WarpCls (schedule Q L) m X P (CollAt Q L) cn slot where
  at_ hP hs := (state (count hP hs)).1
  isP _ hs he hc := coll_isP hp hX hs he hc
  slot_mono := mono
  time_at hP hs hat := (state (count hP hs)).2.1 hat
  time_lt hP hs hn := (state (count hP hs)).2.2 hn
  exit hP hs he := exit (count hP hs) (exit_state_pc hp hX hs he)
  released {x y σ σ'} hx hy hsw hσ hcx hσ' hcy hn hrel :=
    released hx hy hsw hσ hcx hσ' hcy hn (fun k {σ0} _ hs0 hnc => by
      have e : Sched.collCount X x (X.tr x).length = Sched.collCount X y (X.tr y).length := by
        simp only [Sched.collCount, List.take_length]
        exact hn.symm
      have hle : Sched.collCount X y k ≤ Sched.collCount X y (X.tr y).length :=
        (List.take_sublist _ _).countP_le.trans (by simp [Sched.collCount, List.take_length])
      rw [(state (count hx hσ)).2.1 hcx, e]
      exact (state (count hy hs0)).2.2 hnc _ (by rw [(state (count hy hσ')).1.mp hcy]; rfl) hle)
      hrel
  dead := dead

/-- **The classification of a warp** from the script facts of its states: at every state the lane
has the facts of `ScriptFacts` at the collectives it has made, and a state at the exit pc is past
the script. -/
theorem warpCls_script {P : Nat → Prop} {cn : Nat → Option Nat} {slot : Nat → Nat}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (count : ∀ {x k σ}, P x → k ≤ (X.tr x).length →
      Frame.stateAt (schedule Q L).code X x k = some (some σ) →
      ScriptFacts cn slot (Sched.collCount X x k) (((schedule Q L).code x).pc σ)
        ((schedule Q L).time x σ) ∧
      (((schedule Q L).code x).pc σ = 2855 → ∀ n, (cn n).isSome = true →
        n < Sched.collCount X x k))
    (mono : ∀ {a b}, a < b → (cn b).isSome = true → slot a < slot b)
    (released : WarpRel Q L m X P) (dead : WarpDead Q L X P) :
    Sched.WarpCls (schedule Q L) m X P (CollAt Q L) cn slot := by
  refine warpCls_of (F := fun x σ c => ScriptFacts cn slot c (((schedule Q L).code x).pc σ)
    ((schedule Q L).time x σ) ∧ (((schedule Q L).code x).pc σ = 2855 → ∀ n, (cn n).isSome = true →
      n < c)) hp hX ?_ ?_ mono ?_ released dead
  · intro x σ c ⟨⟨a, b, c'⟩, _⟩
    have ca : CollAt Q L x σ ↔ isWarpAt (((schedule Q L).code x).pc σ) = true := collAt_iff_warp
    refine ⟨ca.trans a, fun w => b (ca.mp w), fun w n hn hle => c' ?_ n hn hle⟩
    cases e : isWarpAt (((schedule Q L).code x).pc σ)
    · rfl
    · exact absurd (ca.mpr e) w
  · intro x k σ hx hs
    obtain ⟨k', hk', hs', hc'⟩ := clip_state hs
    have := count hx hk' hs'
    rw [hc'] at this
    exact this
  · intro x σ c ⟨_, h⟩ hpc
    exact h hpc

end PTX.Kernels.InklingRelDecode.Proof
