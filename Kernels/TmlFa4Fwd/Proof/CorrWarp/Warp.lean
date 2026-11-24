-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.EvR
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Pos
public import Kernels.TmlFa4Fwd.Proof.Correction.RefDef
public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Common.ControlFrame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.ControlRead
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape
import Kernels.TmlFa4Fwd.Proof.Correction.Control.RefNext
import Kernels.TmlFa4Fwd.Proof.Correction.Control.NoStop
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Fits
import Kernels.TmlFa4Fwd.Proof.Correction.Steps
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Correction.RefNext

@[expose] public section

/-! # The lanes of the correction warps are followed

Every lane of a correction warp `w` (8 to 11) is followed by the thread machine, and every state
holds the reference invariant (`good`): `Frame.followedOn` restricted to the lanes of warp `w`,
with the order by the warp collectives up to an event (`μ`), as for the output and MMA warps.

**Reference invariant** (`Ref`). At a startup state the startup's words and counts (`StartAt` with
the warp index `w`) and zero correction counts; at a role state, unless an event so far was
undefined behaviour, the Correction lane's invariant (`Correction.Ref`: the ledger's closed forms
on the correction classes of the thread's ledger and the positive row sums) and the reference
values (`CFits`).

**Sources.** The scheduler's reads come from the launch words (the output warp's `expect_word`,
`expect_q` on the reads' addressed shapes `EvR`; the used-K word by `inputReadValue`), the scan's
shuffles and ballot from the lanes of the warp at the same instance (`cshfl_recv`, `cvote_bits`,
with the positions of `Pos.lean`). The statistics reads and the Tensor Memory loads are the
premise `DataSrc`: their sources are the softmax warps' statistics writes (a positive row sum for
a row with a finite maximum) and the kernel's `TcLdDataflow` assumption, which the softmax
fragment and the Tensor Memory protocol will supply. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-! ### The reference invariant -/

/-- The sites whose values the softmax warps or the Tensor Core produce. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Correction.Site.data : Site → Bool
  | .rscale _ | .fsum _ | .fmax _ | .rld _ _ | .fld _ _ => true
  | _ => false

/-- The correction counts before the role's first state. -/
def ZeroK (n : Cls → Nat) : Prop := ∀ c, n (.corr c) = 0

/-- **The reference invariant of a lane of correction warp `w`.** -/
def Ref (p : Params) (L : Launch) (w g : Nat) :
    (Startup.D ⊕ (Σ i, (frag p L g i).D)) × (Cls → Nat) → Prop
  | (.inl s, n) => StartAt L w s n ∧ n .vote = 0 ∧ ZeroK n
  | (.inr ⟨.correction, d⟩, n) =>
      n .ub = 0 → Correction.Ref p L g (d, rc n) ∧ CFits p L g d (n .shfl) (n .vote)
  | (.inr ⟨.epilogue, _⟩, _) | (.inr ⟨.mma, _⟩, _) | (.inr ⟨.loader _, _⟩, _)
  | (.inr ⟨.stub _, _⟩, _) | (.inr ⟨.softmax, _⟩, _) => False

/-- Lane `g`'s state before its `k`-th event is followed and holds the reference invariant. -/
abbrev Good (p : Params) (L : Launch) (w : Nat) (X : Execution) (g k : Nat) : Prop :=
  Frame.FollowedAt (thread p L) (Ref p L w) X g k

/-- **The data-plane premise**: a statistics read or a Tensor Memory load of a correction lane at a
state that holds the Correction lane's invariant returns what that invariant expects (a real
`f32` payload, a nonnegative one at a row-sum read). Its sources are the softmax warps' statistics
writes and the kernel's `TcLdDataflow` assumption. -/
def DataSrc (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d n e, X.get (g, k) = some e →
    Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction,d⟩,n)) →
    Correction.Ref p L g (d, rc n) → d.site.data = true → ExpectD d e

theorem ref_init : Ref p L w g (thread p L g).init := by
  show Ref p L w g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  exact ⟨⟨rfl, rfl, by simp, by simp⟩, rfl, fun _ => rfl⟩

/-! ### Events at the correction warps' states -/

theorem fired_both (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {d : Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (cinj p L g d n)))
    (hu : ∀ f, e.kind ≠ .ub f := by intro f h; cases h) :
    Control.Ev p L g d e ∧ EvR p L g d.scheduler e := by
  obtain ⟨_, _, _, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he hσ hu
  exact ⟨Control.shapeAt hp d hat hi hc hf hu, Control.read_shapeAt hp d hat hi hc hf⟩

theorem next_cinj (d : Control.D) (n : Cls → Nat) (e : Event) :
    (thread p L g).next (cinj p L g d n) e = (Control.succ p L g d e).map
      (Option.map fun d' => cinj p L g d' (Code.bump (Proof.cls L g) n e)) := by
  show ((Control.succ p L g d e).map (Option.map fun d' =>
    (Sum.inr ⟨Role.correction, d'⟩ : (glued p L g).D))).map
        (Option.map fun d' => (d', Code.bump (Proof.cls L g) n e)) = _
  rcases Control.succ p L g d e with _ | _ | d' <;> rfl

/-- A followed state of a correction lane before an event that is no undefined behaviour: a
startup state, or a role state with its reference invariant. -/
theorem good_cases (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L w X g j) :
    (∃ s n, Frame.stateAt (thread p L) X g j = some (some (.inl s, n)) ∧
        StartAt L w s n ∧ n .vote = 0 ∧ ZeroK n) ∨
      (∃ d n, Frame.stateAt (thread p L) X g j = some (some (cinj p L g d n)) ∧ n .ub = 0 ∧
        Correction.Ref p L g (d, rc n) ∧ CFits p L g d (n .shfl) (n .vote)) := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact .inl ⟨s, n, hσ, hR⟩
  · exact hR.elim
  · exact hR.elim
  · have h0 := ub_zero hX he hσ
    exact .inr ⟨d, n, hσ, h0, hR h0⟩
  · exact hR.elim
  · exact hR.elim

/-- The kind of event a correction site fires, as far as the collectives and the return go. -/
private theorem ev_class_data {d : D} {e : Event} (hev : Ev p L g d e) :
    (Execution.isShfl e = true → (epi d.site).shfl = true) ∧
      (isFullVote e = true → d.site.isVote = true) ∧
      (e.kind = .exit → ∃ l, epi d.site = .exit l) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [Epilogue.sh, h, ↓reduceIte] at h1; split at h1 <;> simp_all
  · simp only [Epilogue.vt, h, ↓reduceIte] at h2; unfold Site.isVote; split at h2 <;> simp_all
  · obtain ⟨pc, kind⟩ := e
    simp only at h
    subst h
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp only [Ev] at hev <;> simp_all [epi, Epilogue.Ev, rdOrUb, Site.toE]

theorem ev_class {d : Control.D} {e : Event} (hev : Control.Ev p L g d e) :
    (Execution.isShfl e = true → (epi d.site).shfl = true) ∧
      (isFullVote e = true → d.site.isVote = true) ∧
      (e.kind = .exit → ∃ l, epi d.site = .exit l) := by
  by_cases hs : ∃ st, d.site = .rvote st
  · obtain ⟨st, hs⟩ := hs
    obtain ⟨s,v,k⟩ := d
    change s = _ at hs
    subst s
    obtain ⟨pred,b,h⟩ := hev
    obtain ⟨pc,kind⟩ := e
    change kind = _ at h
    subst kind
    exact ⟨nofun, fun _ => rfl, nofun⟩
  · apply ev_class_data (d := d.scheduler)
    obtain ⟨s,v,k⟩ := d
    cases s with
    | rvote st => exact (hs ⟨_,rfl⟩).elim
    | _ => exact hev

/-- A role state of a correction lane at an event that is a collective past the startup's or a
return: its reference values, its shape and its counts. -/
theorem role_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hG : Good p L w X h j)
    (hk : (Execution.isShfl e = true ∧ 3 ≤ ((X.tr h).take j).countP Execution.isShfl) ∨
      isFullVote e = true ∨ e.kind = .exit) :
    ∃ d n, Frame.stateAt (thread p L) X h j = some (some (cinj p L h d n)) ∧
      Correction.Ref p L h (d, rc n) ∧ CFits p L h d (n .shfl) (n .vote) ∧ Control.Ev p L h d e ∧
      ((X.tr h).take j).countP Execution.isShfl = n .shfl ∧
      ((X.tr h).take j).countP isFullVote = n .vote := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    rcases hk with ⟨h1, -⟩ | h1 | h1 <;> simp [Execution.isShfl, isFullVote, voteClass] at h1
  rcases good_cases hp hX he hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨d, n, hσ, -, hJ, hF⟩
  · exfalso
    obtain ⟨hv, hx, hsh, -⟩ := start_kind hS (start_fired hp hX he hσ).1
    rcases hk with ⟨h1, h2⟩ | h1 | h1
    · have := hsh h1; rw [(counts hσ).1] at h2; omega
    · rw [hv] at h1; cases h1
    · exact hx h1
  · have hu := fun f h => hub e.pc f (congrArg (Event.mk e.pc) h)
    exact ⟨d, n, hσ, hJ, hF, (fired_both hp hX he hσ hu).1, (counts hσ).1, (counts hσ).2⟩

/-! ### The startup and the role's steps -/

theorem enterOf_corr {s : Startup.D} (hw : 8 ≤ w ∧ w ≤ 11) (h3 : s.x3 = BitVec.ofNat 64 w) :
    Startup.enterOf s = { s with site := .enter .correction } := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at h3
  subst h3
  unfold Startup.enterOf
  obtain rfl | rfl | rfl | rfl : w = 8 ∨ w = 9 ∨ w = 10 ∨ w = 11 := by omega
  all_goals (dsimp only; simp (config := { decide := true }))

/-- **The startup steps a lane of correction warp `w` well**, into the role's first state after
the barrier. -/
theorem start_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) (hw8 : 8 ≤ w ∧ w ≤ 11) {k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Ref p L w g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → InWarp L w j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L w) X j) :
    Frame.StepGood (thread p L) (Ref p L w) g (.inl s, n) e :=
  start_step_of (Z := ZeroK) hp hX hg hw (by omega) (by omega) (fun _ => ref_init)
    (fun _ _ => rfl) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun h j e r d n he hσ hR => by
      rcases r with _ | _ | _ | _ | r | _
      on_goal 6 => exact hR.elim
      · exact hR.elim
      · exact hR.elim
      · obtain ⟨rv, -, -, hFE, -⟩ := (hR (ub_zero hX he hσ)).2
        exact Epilogue.fits_three hFE
      · exact hR.elim
      · exact hR.elim)
    (fun _ _ hn hZ c => (hn _ (by simp [StartCls])).trans (hZ c))
    (fun s n e hb hS hv hZ hE hn => by
      have hZ' : ZeroK (Code.bump (Proof.cls L g) n e) := fun c =>
        (hn _ (by simp [StartCls])).trans (hZ c)
      have hv' : Code.bump (Proof.cls L g) n e .vote = 0 :=
        (hn _ (by simp [StartCls])).trans hv
      obtain ⟨site, x1, x2, x3⟩ := s
      simp only at hb
      subst hb
      simp only [StartAt] at hS
      simp only [Startup.Ev] at hE
      obtain ⟨h3, h4, rfl, rfl⟩ := hS
      have hwi : Prologue.warpIndex L g = g % L.block / 32 := rfl
      rw [enterOf_corr hw8 rfl]
      simp only [Code.enter, exit, Gate, roleOf, ← hwi, hw, beq_self_eq_true, Bool.and_self,
        ↓reduceIte]
      intro hub
      refine ⟨?_, ?_⟩
      · have : rc (Code.bump (Proof.cls L g) n e) = fun _ => 0 := funext hZ'
        show Correction.Ref p L g (D.mk' .setmax {}, rc (Code.bump (Proof.cls L g) n e))
        rw [this]
        exact Correction.ref_init
      · obtain ⟨pc, kind⟩ := e
        simp only at hE
        subst hE
        refine ⟨0, Nat.zero_le _, ?_, ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
        · simp only [RvAt, Control.D.scheduler, D.mk', show inRound (Site.pc .setmax) = false from
            rfl,
            show tailR Site.setmax = false from rfl, show Site.setmax.late = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
        · simp [Code.bump, Proof.cls, Execution.isShfl, h3]
        · simpa using hv')
    he hσ hR hprev

/-- Every expectation of the Correction lane holds for an undefined-behaviour event. -/
theorem expectD_ub {d : D} {e : Event} (hub : ∃ f, e.kind = .ub f) : ExpectD d e := by
  obtain ⟨f, hf⟩ := hub
  obtain ⟨pc, kind⟩ := e
  simp only at hf
  subst hf
  unfold ExpectD
  split <;> simp

/-- **A role state steps well on an event that returns what the references say**: the
Correction lane's invariant and the reference values continue (`ref_next`, `cfits_next`); after
an undefined-behaviour event the invariant's guard is false. -/
theorem role_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Control.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (cinj p L g d n)))
    (hR : Ref p L w g (cinj p L g d n))
    (hexp : (∀ f, e.kind ≠ .ub f) → CExpect p L g d (n .shfl) e ∧ Control.Expect d e) :
    Frame.StepGood (thread p L) (Ref p L w) g (cinj p L g d n) e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
  have hRef : Control.Ref p L g (d,rc n) := hJ.counts
  show (thread p L g).next (cinj p L g d n) e ≠ some none ∧ _
  rw [next_cinj]
  by_cases hub : ∃ f, e.kind = .ub f
  · have hne : Control.succ p L g d e ≠ some none := by
      apply Control.not_stop hRef
      have h := expectD_ub (d := d.scheduler) hub
      obtain ⟨s,v,k⟩ := d
      cases s <;> first | exact h | exact True.intro
    rcases hn : Control.succ p L g d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd hn hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro h1
      obtain ⟨f, hf⟩ := hub
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      simp [Code.bump, Proof.cls] at h1
  · have hub' : ∀ f, e.kind ≠ .ub f := fun f h => hub ⟨f, h⟩
    obtain ⟨hCE, hED⟩ := hexp hub'
    have hev := (fired_both hp hX he hσ hub').1
    have hne := Control.not_stop hRef hED
    rcases hn : Control.succ p L g d e with _ | _ | d'
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd hn hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro _
      refine ⟨Control.scheduler_ref (Control.ref_kept hRef hev hub' hn), ?_⟩
      have := Control.fits_next (ctaR_eq hp hg) (Control.represents hRef hev hub' hn) hF hCE
      have h1 : Code.bump (Proof.cls L g) n e .shfl = n .shfl + Epilogue.sh e := rfl
      have h2 : Code.bump (Proof.cls L g) n e .vote = n .vote + Epilogue.vt e := rfl
      rw [h1, h2]
      exact this

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
