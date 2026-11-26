-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StartEv
public import Lemmas.Kernel.Followed

@[expose] public section

/-! # The following, step by step: the steps' premises from the trace

The induction of `Common/FollowProof.lean` (`Frame.followedOn` along `Frame.lexOrder` of the warp
collectives up to an event) gives at an event `(g, k)` its state `σ` with `JF` and that no event
of a launched thread before it in that order is bad (`Prev`). This file feeds the startup's and the
head's good steps (`startup_good`, `head_good`) from it:

* the event's shape and pc: at a startup state from the strict glue (`startup_ev`), at a head
  state (no undefined behaviour) from the site the event fired at (`Frame.fired_siteU`) and the
  shape table (`shapeOk`);
* the shuffles' words: `startup_recv` and `head_recv` take the lanes of the warp followed up to the
  event (`Frame.GoodUpTo`), which `Prev` gives through `Frame.upTo_of_lt` (`upTo_prev`).

The read-back at pc 92 needs nothing: the startup follows every value it returns
(`Startup.afterLd`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {X : Execution}

/-- No event of a launched thread before `i` in the induction's order is bad. -/
def Prev (P : Params) (L : Launch) (X : Execution) (i : EvId) : Prop :=
  ∀ j, Frame.lexOrder (Frame.collUpTo X) j i → j.1 < L.threads →
    ¬ Frame.Bad (thread P L) (JF P L) X j

/-- **The lanes of the warp are followed up to a collective** with the role table's invariant. -/
theorem upTo_prev {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hc : Frame.isColl e = true) (hprev : Prev P L X (g, k)) :
    Frame.GoodUpTo (thread P L) (table P L).J X (g % L.block / 32)
      (((X.tr g).take k).countP Frame.isColl) := by
  intro h j hh hj
  obtain ⟨h1, h2⟩ := Frame.upTo_of_lt (C := thread P L) (J := JF P L) (fun _ => jf_init) he hc
    (fun i hi hw => hprev i (.inl hi) hw.1) h j hh hj
  exact ⟨h1, fun d hd => (h2 d hd).1⟩

/-- A shuffle is a warp collective. -/
theorem isColl_shfl {pc : Nat} {md : ShflMode} {a : Value} {b c : Nat} {r : Value} {ok : Bool} :
    Frame.isColl ⟨pc, .shfl md a b c r ok⟩ = true := by
  simp [Frame.isColl, Execution.isShfl]

/-- **A startup step is good**, fed from the trace. -/
theorem startup_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {d : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (thread P L) X g k = some (some (.inl d, n)))
    (hJ : JF P L g (.inl d, n)) (hprev : Prev P L X (g, k)) :
    Frame.StepGood (thread P L) (JF P L) g (.inl d, n) e := by
  obtain ⟨hJ1, hz⟩ := hJ
  obtain ⟨hev, hpc, hx⟩ := startup_ev hp hX he hσ
  have hx' : Startup.exitOf d = none := by simpa [startupEnter] using hx
  refine startup_good hp hJ1 hz hev (hpc ▸ startup_pc_le hx) (fun a r ok hk => ?_)
  obtain ⟨j, hj⟩ := (Startup.ev_coll hev hx').2 _ _ _ _ _ _ hk
  have hW := hJ1.2.1
  unfold Startup.RefW at hW
  rw [hj] at hW
  obtain ⟨hsh, -⟩ := hW
  have hc : Frame.cnt X Execution.isShfl g k = j.val := by
    rw [← hsh]
    exact (state_count hσ .shfl).symm
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  rw [hsh]
  exact startup_recv hp hX he hc (upTo_prev he isColl_shfl hprev)

/-- The head's sites at its states: the `setmaxnreg` and the shuffle. -/
theorem head_pc {s : Wg1.Site} (hx : wg1Enter P L g s = none) :
    Wg1.Site.pc P L g s = 1842 ∨ Wg1.Site.pc P L g s = 1843 := by
  cases s <;> simp [wg1Enter, Wg1.exitOf, Wg1.Site.pc] at hx ⊢

/-- **A head step is good**, fed from the trace. -/
theorem head_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {s : Wg1.Site} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg1, .inl s⟩, n)))
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inl s⟩, n)) (hprev : Prev P L X (g, k)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inl s⟩, n) e := by
  have hsite : (∀ f, e.kind ≠ .ub f) →
      Wg1.Ev L g s e ∧ (e.pc = 1842 ∨ e.pc = 1843) ∧ wg1Enter P L g s = none := by
    intro hu
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
      Frame.fired_siteU (fun _ _ => thread_sound hp) hX he hσ hu
    have hev := (shapeOk hp (fun _ => True)).shape g trivial _ t ins e o hJ.1 hat hi hc hf
    have hx := Code.gatedExit_none.mp hi.2
    rw [EventFrame.fires_source_pc hf]
    exact ⟨hev, head_pc hx, hx⟩
  refine head_good hp hJ (fun hu => ⟨(hsite hu).1, (hsite hu).2.1⟩) fun a r ok hk => ?_
  obtain ⟨hev, -, hx⟩ := hsite fun f h => by rw [hk] at h; cases h
  obtain ⟨⟨-, hR, -, hwg⟩, -⟩ := hJ
  change Wg1.HRef L g s (n .shfl) at hR
  have hs : s = .hsh := by
    cases s <;> simp only [Wg1.Ev] at hev <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some,
      reduceCtorEq] at hx
    · obtain ⟨inst, hk'⟩ := hev
      rw [hk] at hk'
      cases hk'
    · rfl
  subst hs
  obtain ⟨hsh, -⟩ := hR
  have hc : Frame.cnt X Execution.isShfl g k = 2 := by
    rw [← hsh]
    exact (state_count hσ .shfl).symm
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  exact head_recv hp hX he hc hwg (upTo_prev he isColl_shfl hprev)

/-- No undefined behaviour while the bumped count of the class `.ub` is zero. -/
theorem not_ub_of_bump {n : Cls → Nat} {e : Event} (h0 : Code.bump cls n e .ub = 0) :
    ∀ f, e.kind ≠ .ub f := fun f hf => by
  simp [Code.bump, cls, hf] at h0

/-- An event that is no undefined behaviour, at a state with the table's invariant, has the
table's shape. -/
theorem ev_of_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread P L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hJ : (table P L).J g σ)
    (hu : ∀ f, e.kind ≠ .ub f) : (table P L).Ev g σ e := by
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (fun _ _ => thread_sound hp) hX he hσ hu
  exact (shapeOk hp (fun _ => True)).shape g trivial _ t ins e o hJ hat hi hc hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
