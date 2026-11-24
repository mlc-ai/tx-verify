-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.EvS
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Start0
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef
import Lemmas.Kernel.FrameU
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Shape
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Fits
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.NoStop
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RefNext
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Sound
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.RefNext

@[expose] public section

/-! # The lanes of the softmax warps are followed

Every lane of a softmax warp `w` (0 to 7) is followed by the thread machine, and every state holds
the reference invariant (`good`), given three named premises:

- `NumAll`: the numeric steps of the softmax fragment (`Softmax.NumSteps`, 51 states), under
  which the role's machine is the data machine (`SmWarp.next_eq`);
- `DataStoreSafe` of every softmax lane (the fragment's store premise; it gives the shape table
  without undefined behaviour, `Softmax.shapeS`);
- `SmSrc`: what the fragment's `Expect` asks of an event at a state holding its reference
  invariant (`Softmax.ExpectD`): 32-bit words at the scheduler's reads and shuffles, the tile
  count's division rules, bias bytes that rebuild, `f32` payloads at the score loads. Their sources
  are the launch words and the scan's collectives (as for the correction warps), the loader's
  copies of the Bias (a protected read) and the kernel's `TcLdDataflow` assumption.

**Reference invariant** (`Ref`). At a startup state the startup's words and counts (`StartAt0`
on warp 0, whose startup makes the elections and initializations, `StartAt` on the others) and
at a role state the startup's three shuffles and, unless an event so far was undefined behaviour,
the fragment's invariant for some counts (the thread's ledger has no softmax classes yet: the
startup's shuffles and warp 0's elections are of the fragment's classes `shfl` and `won`, so the
classes would need the startup's class sets extended, which the hand-offs will do when they read
the counts). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- The startup's words and counts on a lane of warp `w`. -/
def StartW (L : Launch) (w : Nat) (s : Startup.D) (n : Cls → Nat) : Prop :=
  if w = 0 then StartAt0 L s n else StartAt L w s n

/-- No softmax class counted yet. -/
def ZeroS (n : Cls → Nat) : Prop := ∀ c, n (.soft c) = 0

/-- The fragment's counts `c` agree with the thread's ledger on the classes whose counts are
closed forms in the places (`Softmax.Cnt.pointed`). -/
def Linked (n : Cls → Nat) (c : Softmax.Cnt → Nat) : Prop :=
  ∀ c', c'.pointed = true → c c' = n (.soft c')

/-- **The reference invariant of a lane of softmax warp `w`.** The fragment's counts are
existential, linked to the thread's ledger on the pointed classes; the scheduler's values are the
output warp's reference (`SFits`). -/
def Ref (p : Params) (L : Launch) (w g : Nat) :
    (Startup.D ⊕ (Σ i, (frag p L g i).D)) × (Cls → Nat) → Prop
  | (.inl s, n) => StartW L w s n ∧ n .vote = 0 ∧ ZeroS n
  | (.inr ⟨.softmax, d⟩, n) => 3 ≤ n .shfl ∧
      (n .ub = 0 → (∃ c, Control.Ref p L g (d, c) ∧ Linked n c) ∧
        SFits p L g d.scheduler (n .shfl) (n .vote))
  | (.inr ⟨.epilogue, _⟩, _) | (.inr ⟨.mma, _⟩, _) | (.inr ⟨.correction, _⟩, _)
  | (.inr ⟨.loader _, _⟩, _) | (.inr ⟨.stub _, _⟩, _) => False

/-- Lane `g`'s state before its `k`-th event is followed and holds the reference invariant. -/
abbrev Good (p : Params) (L : Launch) (w : Nat) (X : Execution) (g k : Nat) : Prop :=
  Frame.FollowedAt (thread p L) (Ref p L w) X g k

/-- **What the fragment expects of the softmax warps' events** (the named source premise). -/
def SmSrc (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d n c e, X.get (g, k) = some e →
    Frame.stateAt (threadD p L) X g k = some (some ((.inr ⟨.softmax,d⟩,n))) →
    Softmax.Ref p L g (d, c) → ExpectD p L g d e

theorem ref_init : Ref p L w g (thread p L g).init := by
  show Ref p L w g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  refine ⟨?_, rfl, fun _ => rfl⟩
  unfold StartW
  split
  · exact ⟨rfl, rfl, by simp, by simp⟩
  · exact ⟨rfl, rfl, by simp, by simp⟩

theorem enterOf_soft {s : Startup.D} (hw : w < 8) (h3 : s.x3 = BitVec.ofNat 64 w) :
    Startup.enterOf s = { s with site := .enter .softmax } := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at h3
  subst h3
  unfold Startup.enterOf
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by omega
  all_goals (dsimp only; simp (config := { decide := true }))

theorem bump_ge (n : Cls → Nat) (e : Event) (c : Cls) : n c ≤ Code.bump (Proof.cls L g) n e c :=
  Nat.le_add_right _ _

/-- The startup's barrier is no shuffle. -/
theorem bump_shfl_bar {x1 x2 x3 : BitVec 64} {n : Cls → Nat} {e : Event}
    (hE : Startup.Ev L g ⟨.bar, x1, x2, x3⟩ e) : Code.bump (cls L g) n e .shfl = n .shfl := by
  obtain ⟨pc, kind⟩ := e
  simp only [Startup.Ev] at hE
  subst hE
  rfl

/-- The role's first state after the barrier, from a startup state at the barrier with the
shared base and the warp word. -/
theorem enter_ref (hw : Prologue.warpIndex L g = w) (hw8 : w < 8) {x2 : BitVec 64}
    {n : Cls → Nat} (hn3 : n .shfl = 3) (hv : n .vote = 0) (hZ : ZeroS n) :
    Ref p L w g (Code.enter (Startup.code p L g) (frag p L g) (exit L g)
      (Startup.enterOf ⟨.bar, BitVec.ofNat 64 L.sharedBase, x2, BitVec.ofNat 64 w⟩), n) := by
  have hwi : Prologue.warpIndex L g = g % L.block / 32 := rfl
  rw [enterOf_soft hw8 rfl]
  simp only [Code.enter, exit, Gate, roleOf, ← hwi, hw, beq_self_eq_true, Bool.and_self,
    decide_eq_true hw8, ↓reduceIte]
  refine ⟨hn3.ge, fun _ => ⟨⟨fun _ => 0, Control.ref_init, fun c' _ => (hZ c').symm⟩,
    ⟨?_, fun h => by cases h⟩⟩⟩
  show Epilogue.Fits p L g { ({} : V).sc with site := .start } (n .shfl) (n .vote)
  exact ⟨hn3, hv⟩

/-- **The startup steps a lane of softmax warp `w` well**, into the role's first state. -/
theorem start_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) (hw8 : w < 8) {k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Ref p L w g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g (.inl s, n) e := by
  have hJr : ∀ h j e r d n, X.get (h, j) = some e →
      Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)) →
      Ref p L w h (.inr ⟨r, d⟩, n) → 3 ≤ n .shfl := by
    intro h j e r d n _ _ hR
    cases r with
    | softmax => exact hR.1
    | _ => exact hR.elim
  by_cases h0 : w = 0
  · subst h0
    exact start0_step_of (Z := ZeroS) hp hX hg hw (fun _ => ref_init)
      (fun _ _ => by simp only [Ref, StartW, ↓reduceIte])
      (fun _ _ _ h => by simp only [Ref, StartW, ↓reduceIte] at h; exact ⟨h.1, h.2.1⟩) hJr
      (fun _ _ hn hz c => (hn _ (by simp [Start0Cls])).trans (hz c))
      (fun s n e hb hS hv hz hE hn => by
        obtain ⟨site, x1, x2, x3⟩ := s
        simp only at hb
        subst hb
        obtain ⟨h3, rfl, rfl⟩ := startAt0_of_mid (by rfl) hS
        exact enter_ref hw (by omega) (by rw [bump_shfl_bar hE]; exact h3)
          ((hn _ (by simp [Start0Cls])).trans hv)
          fun c => (hn _ (by simp [Start0Cls])).trans (hz c))
      he hσ hR fun j hj => hprev j (.inl hj)
  · exact start_step_of (Z := ZeroS) hp hX hg hw h0 (by omega) (fun _ => ref_init)
      (fun _ _ => by simp only [Ref, StartW, h0, ↓reduceIte])
      (fun _ _ _ h => by simp only [Ref, StartW, h0, ↓reduceIte] at h; exact ⟨h.1, h.2.1⟩) hJr
      (fun _ _ hn hz c => (hn _ (by simp [StartCls])).trans (hz c))
      (fun s n e hb hS hv hz hE hn => by
        obtain ⟨site, x1, x2, x3⟩ := s
        simp only at hb
        subst hb
        simp only [StartAt] at hS
        obtain ⟨h3, -, rfl, rfl⟩ := hS
        exact enter_ref hw hw8 (by rw [bump_shfl_bar hE]; exact h3)
          ((hn _ (by simp [StartCls])).trans hv)
          fun c => (hn _ (by simp [StartCls])).trans (hz c))
      he hσ hR hprev

theorem next_sinj (d : Control.D) (n : Cls → Nat) (e : Event) :
    (thread p L g).next (sinj p L g d n) e = (Control.succ p L g d e).map
      (Option.map fun d' => sinj p L g d' (Code.bump (Proof.cls L g) n e)) := by
  change (((Control.succ p L g d e).map _).map _) = _
  rcases Control.succ p L g d e with _ | _ | d' <;> rfl

/-- A defined softmax event has its protocol shape at the current control site. -/
theorem fired_soft (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {e : Event} {d : Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hu : ∀ f, e.kind ≠ .ub f) :
    EvS p L g d.scheduler e ∧ (control p L g).inv d := by
  obtain ⟨_, _, _, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he hσ hu
  exact ⟨⟨Control.shapeAt hp d hat hi.1 hc hf, hu⟩, hi⟩

theorem role_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {d : Control.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (sinj p L g d n)))
    (hR : Ref p L w g (sinj p L g d n))
    (hexp : (∀ f, e.kind ≠ .ub f) → Control.Expect p L g d e ∧
      SExpect p L g d.scheduler (n .shfl) e) :
    Frame.StepGood (thread p L) (Ref p L w) g (sinj p L g d n) e := by
  obtain ⟨h3, hJ⟩ := hR
  obtain ⟨⟨c, hRef, hL⟩, hF⟩ := hJ (ub_zero hX he hσ)
  change (thread p L g).next (sinj p L g d n) e ≠ some none ∧ _
  rw [next_sinj]
  by_cases ub : ∃ f, e.kind = .ub f
  · obtain ⟨f,hf⟩ := ub
    have hE : Control.Expect p L g d e := by
      rcases d with ⟨s,v,k,acc⟩
      rcases e with ⟨pc,kind⟩
      change kind = .ub f at hf
      subst kind
      cases s <;> simp [Control.Expect, Control.D.scheduler, ExpectD]
      case tiles late => cases late <;> trivial
    have hne := Control.not_stop hRef hE
    rcases hn : Control.succ p L g d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact (hne hn).elim
    · refine ⟨by simp, fun σ h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst σ
      refine ⟨h3.trans (bump_ge _ _ _), fun hz => ?_⟩
      rcases e with ⟨pc,kind⟩
      change kind = .ub f at hf
      subst kind
      simp [Code.bump, Proof.cls] at hz
  · have hu : ∀ f, e.kind ≠ .ub f := fun f h => ub ⟨f,h⟩
    obtain ⟨hE,hSE⟩ := hexp hu
    obtain ⟨⟨hev,_⟩,_,hw⟩ := fired_soft hp hX he hσ hu
    have hne := Control.not_stop hRef hE
    rcases hn : Control.succ p L g d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact (hne hn).elim
    · refine ⟨by simp, fun σ h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst σ
      have rep := Control.represents hp hRef hev hu hn
      refine ⟨h3.trans (bump_ge _ _ _), fun _ => ⟨⟨_,Control.ref_kept hp hRef hev hu hn,
        fun c' hc => ?_⟩, ?_⟩⟩
      · simp only [Code.bump, Proof.cls, hc, hw, decide_true, Bool.and_true, hL c' hc]
      · exact Control.fits_next (Softmax.ctaR_eq hp (Frame.lt_of_get hX he)) rep hF hSE

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
