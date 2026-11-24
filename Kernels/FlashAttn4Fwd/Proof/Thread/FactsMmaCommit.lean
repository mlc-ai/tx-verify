-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Lemmas.Flow.EventCont

@[expose] public section

/-! # The MMA warp's commits

Every Tensor Core commit fires at a commit site of the MMA role (`mma_commitRun`), on the
leader CTA (`Mma.Inv.i`): `tcgen05.commit` with mask 3 over the pair from the thread's CTA, on
the site's barrier `cBar` of the thread's CTA, one of the S-full, KV-empty, Q-empty and O-full
barriers (`commit_state`). Its targets are that barrier in both CTAs of the pair
(`commit_target_loc`), so no commit names a handshake, P-ready, second P-ready, credit, staged or
free barrier.

The commit's count follows the run invariant: the S-full and O-full commits of item `i` are the
`n i …` and `i`-th (`Counts.sFull`, `Counts.oFull`), of an item that passed the loop test
(`Mma.Inv.i`); the commit to `qEmpty 0` is commit site 7 at `995`, and the next commit of the
thread is commit site 8, to `qEmpty 1`, of the same item (`Counts.commits`, all commits). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The state of a commit -/

/-- **A commit fires at a commit site of the MMA role on the leader CTA.** -/
theorem commit_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) :
    warpOf L g = 12 ∧ ∃ (d : Mma.D) (c : Fin 12), Mma.Counts L g d ((X.tr g).take k) ∧
      Mma.Inv L g d ∧ d.site = .commit c ∧ sp = Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c)) ∧
      Mma.rank L g = 0 ∧ pc = d.site.pc := by
  have hg := event_thread_lt hX he
  obtain ⟨hw, d, t, ins, o, hJ, hi, h, hc, hf⟩ := mma_commitRun hpre hX ht he
  obtain ⟨c, hs, rfl⟩ := Mma.commit_site hpre hg h hc hf rfl
  exact ⟨hw, d, c, hJ, hi, hs, rfl, (hi.i (by rw [hs]; trivial)).2, fires_pc hf⟩

/-- The targets of a commit are its barrier in the CTAs of the pair. -/
theorem commit_target_loc {d : Mma.D} {g : Nat} {c : Fin 12} {r : Fin 16} {m : Loc}
    (ht : TcCommit.target (Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c))) r = some m) :
    m = (Mma.cBar L d c).loc L (g / L.block / 2 * 2 + r.val) := by
  simp only [TcCommit.target, Mma.cSpec] at ht
  obtain ⟨-, ht⟩ := Option.ite_none_right_eq_some.mp ht
  rw [← Option.some.inj ht]
  rfl

/-- The barrier of a commit site is an S-full, KV-empty, Q-empty or O-full barrier. -/
theorem cBar_cases (d : Mma.D) (c : Fin 12) :
    (Mma.cBar L d c).isEmpty = true ∨ ∃ st, Mma.cBar L d c = .sFull st ∨
      Mma.cBar L d c = .oFull st := by
  fin_cases c <;> simp [Mma.cBar, FBar.isEmpty]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **No commit names a barrier other than an S-full, ring empty or O-full one.** -/
theorem commit_not {i : EvId} {pc c : Nat} {sp : TcCommit.Spec} {r : Fin 16} {b : FBar}
    (hb : b.isEmpty = false ∧ ∀ st, b ≠ .sFull st ∧ b ≠ .oFull st)
    (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) : TcCommit.target sp r ≠ some (b.loc L c) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨-, d, cc, -, -, -, rfl, -, -⟩ := commit_state hpre hX ht he
  intro htg
  obtain ⟨rfl, -⟩ := FBar.loc_inj (commit_target_loc htg).symm
  rcases cBar_cases (L := L) d cc with h | ⟨st, h | h⟩
  · rw [hb.1] at h
    cases h
  · exact (hb.2 st).1 h
  · exact (hb.2 st).2 h

/-! ### The commit fields -/

/-- **The field `TcFacts.commit_spec`.** -/
theorem TcFacts_commit_spec {g k pc : Nat} {sp : TcCommit.Spec} (_ : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) :
    warpOf L g = 12 ∧ ctaOf L g % 2 = 0 ∧ ∃ b : FBar, b ≠ .dealloc ∧
      sp = ⟨.two, b.loc L (ctaOf L g), 3, ctaOf L g, 2⟩ := by
  obtain ⟨hw, d, c, -, -, -, rfl, hr, -⟩ := commit_state hpre hX ht he
  simp only [Mma.rank] at hr
  refine ⟨hw, hr, Mma.cBar L d c, ?_, ?_⟩
  · fin_cases c <;> simp [Mma.cBar]
  · simp only [Mma.cSpec, Mma.bar, ctaOf]
    congr 1
    omega

/-- **The field `ExitFacts.commit_target`.** -/
theorem ExitFacts_commit_target {g k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16} {m : Loc}
    (_ : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some m) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ (b.isEmpty ∨ ∃ st, b = .sFull st ∨ b = .oFull st) := by
  obtain ⟨-, d, c, -, -, -, rfl, -, -⟩ := commit_state hpre hX ht he
  exact ⟨_, _, commit_target_loc htg, cBar_cases d c⟩

/-- **The field `TmemFacts.hs_commit`.** -/
theorem TmemFacts_hs_commit {i : EvId} {pc cta : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (FBar.loc L cta .dealloc) :=
  commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he

/-- **The field `PReadyFacts.p_commit`.** -/
theorem PReadyFacts_p_commit {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hst : st < 2) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (pReadyBar L c st) := by
  rw [show pReadyBar L c st = pReadyBar L c (⟨st, hst⟩ : Fin 2) from rfl, pReadyBar_eq]
  exact commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he

/-- **The field `P2Facts.p2_commit`.** -/
theorem P2Facts_p2_commit {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hst : st < 2) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (pReady2Bar L c st) := by
  rw [show pReady2Bar L c st = pReady2Bar L c (⟨st, hst⟩ : Fin 2) from rfl, pReady2Bar_eq]
  exact commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he

/-- **The field `StatsFacts.credit_commit`.** -/
theorem StatsFacts_credit_commit {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hst : st < 2) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (statsBar L c st) := by
  rw [show statsBar L c st = statsBar L c (⟨st, hst⟩ : Fin 2) from rfl, statsBar_eq]
  exact commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he

/-- **The field `OutputFacts.stage_commit`.** -/
theorem OutputFacts_stage_commit {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hst : st < 2) (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (stagedBar L c st) ∧
      TcCommit.target sp rank ≠ some (freeBar L c st) := by
  rw [show stagedBar L c st = stagedBar L c (⟨st, hst⟩ : Fin 2) from rfl, stagedBar_eq,
    show freeBar L c st = freeBar L c (⟨st, hst⟩ : Fin 2) from rfl, freeBar_eq]
  exact ⟨commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he,
    commit_not hpre hX ht ⟨rfl, fun _ => ⟨nofun, nofun⟩⟩ he⟩

/-- **The field `SFullFacts.s_commit`.** -/
theorem SFullFacts_s_commit {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (hg : g < L.threads) (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (sFullBar L c st)) :
    warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
      sp.mbar = sFullBar L (ctaOf L g) st :=
  Mma.sFull_commit hpre hX (mma_commitRun hpre hX ht) hg hst he htg

/-- **The field `OFullFacts.o_commit`.** -/
theorem OFullFacts_o_commit {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (hg : g < L.threads) (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (oFullBar L c st)) :
    warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
      sp.mbar = oFullBar L (ctaOf L g) st :=
  Mma.oFull_commit hpre hX (mma_commitRun hpre hX ht) hg hst he htg

end
end PTX.Kernels.FlashAttn4Fwd.Proof
