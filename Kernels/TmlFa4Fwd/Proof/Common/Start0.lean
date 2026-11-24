-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Snoc.ControlFrame
import Lemmas.Kernel.FrameU
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The startup of a lane of warp 0

Warp 0's startup is the other warps' up to the third shuffle; the shuffled warp index is 0, so the
dispatch goes to the sixteen elections, after each of which the elected lane initializes two or
three mbarriers, and then to the fence and the CTA barrier. The number of events before the fence
depends on the lane (how many elections it won), so `StartAt`, which fixes the count of all
events at the fence and the barrier, does not describe it.

* `StartAt0 L s n`: before the third shuffle as `StartAt L 0`; at an election, an
  initialization, the fence and the barrier, the three shuffles, the shared base and the warp
  index 0 as the recorded words. Elections and initializations return nothing the machine
  checks: an election goes to both outcomes.
* `start0_next`: a startup step of a lane of warp 0 keeps `StartAt0` up to the barrier, where it
  enters the role of `x3` (`enterOf`); `start0_step_of` is the step obligation for any reference
  invariant whose startup states are `StartAt0` (the softmax warps' lanes of warp 0), with the
  shuffles' values from `start_recv_of`.
* `Start0Ref`, `start0_good`, `start0_state`: every lane of warp 0 is followed through its
  startup, and before its first event on the CTA barrier its state is a startup state. These are
  what lane T4's `Warp0Lag` reads. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The startup sites after the third shuffle and before the dispatch's entries. -/
def Startup.Site.mid : Startup.Site → Bool
  | .sh _ | .enter _ => false
  | _ => true

/-- The startup's words and counts on a lane of warp 0. -/
def StartAt0 (L : Launch) (s : Startup.D) (n : Cls → Nat) : Prop :=
  match s.site with
  | .sh j => n .shfl = j.val ∧ n .all = j.val ∧
      (0 < j.val → s.x1 = BitVec.ofNat 64 L.sharedBase) ∧ (j.val = 2 → s.x2 = BitVec.ofNat 64 0)
  | .enter _ => False
  | _ => n .shfl = 3 ∧ s.x1 = BitVec.ofNat 64 L.sharedBase ∧ s.x3 = BitVec.ofNat 64 0

theorem startAt0_mid {s : Startup.D} {n : Cls → Nat} (hm : s.site.mid = true)
    (h : n .shfl = 3 ∧ s.x1 = BitVec.ofNat 64 L.sharedBase ∧ s.x3 = BitVec.ofNat 64 0) :
    StartAt0 L s n := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp_all [StartAt0, Startup.Site.mid]

theorem startAt0_of_mid {s : Startup.D} {n : Cls → Nat} (hm : s.site.mid = true)
    (h : StartAt0 L s n) :
    n .shfl = 3 ∧ s.x1 = BitVec.ofNat 64 L.sharedBase ∧ s.x3 = BitVec.ofNat 64 0 := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp_all [StartAt0, Startup.Site.mid]

/-- Before the third shuffle a lane of warp 0 is at `StartAt L 0`. -/
theorem startAt0_sh {s : Startup.D} {n : Cls → Nat} (h : StartAt0 L s n) (h3 : n .shfl < 3) :
    StartAt L 0 s n := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt0] at h <;> try omega
  case sh j => exact h

theorem startAt0_pc {s : Startup.D} {n : Cls → Nat} (h : StartAt0 L s n) : s.site.pc ≤ 173 := by
  obtain ⟨site, x1, x2, x3⟩ := s
  show site.pc ≤ 173
  cases site <;> simp only [StartAt0] at h
  case sh j => fin_cases j <;> decide
  case elect j => fin_cases j <;> decide
  case init j => fin_cases j <;> decide
  all_goals decide

/-- The classes a startup event of warp 0 counts: shuffles, all events, the barrier among the MMA
warp's named-barrier arrivals, full-mask elections won and lost, and undefined behaviour (which
the output warp's store class also counts). -/
def Start0Cls (c : Cls) : Prop :=
  c = .shfl ∨ c = .all ∨ c = .ub ∨ c = .store ∨ c = .mma .bar ∨ c = .mma .won ∨ c = .mma .lost ∨
    ∃ pc, c = .load (.won pc)

theorem isShfl_kind {pc : Nat} {k : Kind} (h : Execution.isShfl ⟨pc, k⟩ = true) :
    ∃ md a b c r o, k = .shfl md a b c r o := by
  cases k <;> simp [Execution.isShfl] at h
  exact ⟨_, _, _, _, _, _, rfl⟩

/-- **The startup's events on a lane of warp 0**: shuffles before the third, elections,
initializations, the fence and the barrier, or undefined behaviour; none is a ballot or a
return, and each counts only in `Start0Cls`. -/
theorem start0_kind {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt0 L s n)
    (hE : Startup.Ev L g s e) :
    isFullVote e = false ∧ e.kind ≠ .exit ∧ (Execution.isShfl e = true → n .shfl < 3) ∧
      ∀ c, cls L g c e = true → Start0Cls c := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  have hc : ∀ k : Kind, (k = .fenceMbarInit ∨ k = .bar 0 none .sync ∨
      (∃ a b c r o, k = .shfl .idx a b c r o) ∨ (∃ i ld, k = .elect (2 ^ 32 - 1) i ld) ∨
      (∃ l c, k = .mbInit l c) ∨ ∃ f, k = .ub f) →
      isFullVote ⟨pc, k⟩ = false ∧ k ≠ .exit ∧ ∀ c, cls L g c ⟨pc, k⟩ = true → Start0Cls c := by
    rintro k (rfl | rfl | ⟨a, b, c, r, o, rfl⟩ | ⟨i, ld, rfl⟩ | ⟨l, c, rfl⟩ | ⟨f, rfl⟩) <;>
      refine ⟨rfl, by simp, fun c h => ?_⟩ <;>
      cases c <;> simp [cls, Epilogue.isStore, Epilogue.isCommit, Epilogue.isWait,
        Epilogue.isArrive, okPoll, arrivesOn, sourceWaitSuccess, sourceArrive, isFullVote,
        voteClass, Start0Cls] at h ⊢ <;>
      (rename_i c; cases c <;> try simp [Mma.cls, Correction.cls, Loader.cls, corr_nb_ne',
        Softmax.cls, Softmax.Cnt.pointed] at h ⊢)
    all_goals first
      | exact absurd h.1 (soft_nb_ne' h.2)
      | (obtain ⟨h1, -⟩ := h; split at h1 <;> omega)
  have hns : ∀ k : Kind, (∀ md a b c r o, k ≠ .shfl md a b c r o) →
      (Execution.isShfl ⟨pc, k⟩ = true → n .shfl < 3) := fun k hk h => by
    obtain ⟨md, a, b, c, r, o, rfl⟩ := isShfl_kind h
    exact absurd rfl (hk md a b c r o)
  cases site <;> simp only [StartAt0] at hS
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨r, o, rfl⟩ := hE <;>
      obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))) <;>
      exact ⟨h1, h2, fun _ => by simp_all, h3⟩
  case fence =>
    simp only [Startup.Ev] at hE
    obtain ⟨h1, h2, h3⟩ := hc _ (.inl hE)
    exact ⟨h1, h2, hns _ (by intros; rw [hE]; simp), h3⟩
  case bar =>
    simp only [Startup.Ev] at hE
    obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inl hE))
    exact ⟨h1, h2, hns _ (by intros; rw [hE]; simp), h3⟩
  case elect j =>
    simp only [Startup.Ev] at hE
    rcases hE with ⟨i, ld, -, hk⟩ | ⟨f, hk⟩ <;> subst hk
    · obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
      exact ⟨h1, h2, hns _ (by intros; simp), h3⟩
    · obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr (.inr (.inr (.inr ⟨_, rfl⟩)))))
      exact ⟨h1, h2, hns _ (by intros; simp), h3⟩
  case init j =>
    simp only [Startup.Ev] at hE
    rcases hE with ⟨l, c, hk⟩ | ⟨f, hk⟩ <;> subst hk
    · obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))))
      exact ⟨h1, h2, hns _ (by intros; simp), h3⟩
    · obtain ⟨h1, h2, h3⟩ := hc _ (.inr (.inr (.inr (.inr (.inr ⟨_, rfl⟩)))))
      exact ⟨h1, h2, hns _ (by intros; simp), h3⟩

theorem start0_bump {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt0 L s n)
    (hE : Startup.Ev L g s e) (c : Cls) (hc : ¬ Start0Cls c) :
    Code.bump (cls L g) n e c = n c := by
  have := (start0_kind hS hE).2.2.2 c
  by_cases h : cls L g c e = true
  · exact absurd (this h) hc
  · simp [Code.bump, h]

/-- The sites the startup reaches after an election or an initialization are inside it. -/
theorem mid_firstInit (j : Fin 16) : (Startup.firstInit j).mid = true := by
  fin_cases j <;> rfl

theorem mid_afterBlock (d : Startup.D) (j : Fin 16) : (Startup.afterBlock d j).site.mid = true := by
  unfold Startup.afterBlock
  split_ifs <;> fin_cases j <;> rfl

theorem mid_initSucc (n : Fin 34) : (Startup.initSucc n).mid = true := by
  fin_cases n <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The startup steps a lane of warp 0 well before the barrier**: given that its shuffles
return the shared base and the warp index 0, the step is to a startup state that keeps
`StartAt0`. At the barrier the step enters the role of the warp index (`enterOf`). -/
theorem start0_next (hp : Pre p L m) (hw : Prologue.warpIndex L g = 0) {s : Startup.D}
    {n : Cls → Nat} {e : Event} (hS : StartAt0 L s n) (hE : Startup.Ev L g s e)
    (hr : ∀ j : Fin 3, s.site = .sh j → ∀ pc a b c r ok, e = ⟨pc, .shfl .idx a b c r ok⟩ →
      r = b32 (if j.val = 0 then L.sharedBase else 0)) :
    (thread p L g).next (.inl s, n) e ≠ some none ∧ ∀ σ', (thread p L g).next (.inl s, n) e =
      some (some σ') →
      (∃ s', σ'.1 = .inl s' ∧ StartAt0 L s' σ'.2) ∨
        (s.site = .bar ∧
          σ'.1 = Code.enter (Startup.code p L g) (frag p L g) (exit L g)
            (Startup.enterOf s)) := by
  have hall : Code.bump (cls L g) n e .all = n .all + 1 := by simp [Code.bump, cls]
  have hk := start0_kind hS hE
  obtain ⟨site, x1, x2, x3⟩ := s
  -- a step to a site inside the startup keeps the words and the shuffle count
  have hmid : ∀ s' : Startup.D, s'.site.mid = true → s'.x1 = x1 → s'.x3 = x3 →
      ¬ Execution.isShfl e = true → site.mid = true →
      StartAt0 L ⟨site, x1, x2, x3⟩ n → StartAt0 L s' (Code.bump (cls L g) n e) := by
    intro s' hm h1 h3 hsh hm0 h
    obtain ⟨hs, hx1, hx3⟩ := startAt0_of_mid hm0 h
    refine startAt0_mid hm ⟨?_, h1.trans hx1, h3.trans hx3⟩
    simp only [Code.bump, cls]
    simp only [Bool.not_eq_true] at hsh
    simp [hsh, hs]
  have henter : ∀ s' : Startup.D, s'.site.mid = true →
      Code.enter (Startup.code p L g) (frag p L g) (exit L g) s' = .inl s' := by
    intro s' hm
    obtain ⟨site', _, _, _⟩ := s'
    cases site' <;> simp_all [Code.enter, exit, Startup.Site.mid]
  cases site
  case sh j =>
    have hS' := startAt0_sh hS (by simp only [StartAt0] at hS; omega)
    obtain ⟨r, ok, hk'⟩ := start_sent hp hw hS' rfl hE
    obtain ⟨pc, kind⟩ := e
    simp only at hk'
    subst hk'
    have hr' := hr j rfl _ _ _ _ _ _ rfl
    simp only [StartAt0] at hS
    refine ⟨by simp [Startup.succ, hr', Startup.word32, b32], fun σ' h => .inl ?_⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, hr', Startup.word32, b32,
      Option.map_some, Option.some.injEq] at h
    subst h
    fin_cases j <;> simp only [Fin.isValue] at hS ⊢
    · exact ⟨_, rfl, by simp [Code.bump, cls, Execution.isShfl, hS.1],
        by simp [Code.bump, cls, hS.2.1], fun _ => rfl, by simp⟩
    · exact ⟨_, rfl, by simp [Code.bump, cls, Execution.isShfl, hS.1],
        by simp [Code.bump, cls, hS.2.1], fun _ => hS.2.2.1 (by decide), by simp⟩
    · have hne : Epilogue.scmpi .ne .b (BitVec.ofNat 64 0) 0 = false := by decide
      simp only [show ((2 : ℕ) = 0) ↔ False by decide, hne, Bool.false_eq_true, ↓reduceIte,
        Code.enter, exit]
      refine ⟨_, rfl, ?_⟩
      exact startAt0_mid rfl ⟨by simp [Code.bump, cls, Execution.isShfl, hS.1],
        hS.2.2.1 (by decide), rfl⟩
  case enter => simp only [StartAt0] at hS
  case bar =>
    refine ⟨by simp [Startup.succ], fun σ' h => .inr ⟨rfl, ?_⟩⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, Option.map_some,
      Option.some.injEq] at h
    subst h
    rfl
  case fence =>
    have hsh : ¬ Execution.isShfl e = true := fun h => by
      have := hk.2.2.1 h; simp only [StartAt0] at hS; omega
    refine ⟨by simp [Startup.succ], fun σ' h => .inl ?_⟩
    simp only [glued, Code.glue, Startup.code, Startup.succ, Option.map_some,
      Option.some.injEq] at h
    subst h
    rw [henter _ rfl]
    exact ⟨_, rfl, hmid _ rfl rfl rfl hsh rfl hS⟩
  case elect j =>
    have hsh : ¬ Execution.isShfl e = true := fun h => by
      have := hk.2.2.1 h; simp only [StartAt0] at hS; omega
    simp only [Startup.Ev] at hE
    rcases hE with ⟨i, ld, -, hk'⟩ | ⟨f, hk'⟩ <;> obtain ⟨pc, kind⟩ := e <;> simp only at hk' <;>
      subst hk'
    · refine ⟨by simp [Startup.succ], fun σ' h => .inl ?_⟩
      simp only [glued, Code.glue, Startup.code, Startup.succ, Option.map_some,
        Option.some.injEq] at h
      subst h
      split_ifs
      · rw [henter _ (mid_firstInit j)]
        exact ⟨_, rfl, hmid _ (mid_firstInit j) rfl rfl hsh rfl hS⟩
      · rw [henter _ (mid_afterBlock _ j)]
        refine ⟨_, rfl, hmid _ (mid_afterBlock _ j) ?_ ?_ hsh rfl hS⟩ <;>
          simp only [Startup.afterBlock] <;> split_ifs <;> rfl
    · refine ⟨by simp [Startup.succ], fun σ' h => ?_⟩
      simp [glued, Code.glue, Startup.code, Startup.succ] at h
  case init j =>
    have hsh : ¬ Execution.isShfl e = true := fun h => by
      have := hk.2.2.1 h; simp only [StartAt0] at hS; omega
    refine ⟨?_, fun σ' h => .inl ?_⟩
    · simp only [glued, Code.glue, Startup.code, Startup.succ]
      split <;> simp
    simp only [glued, Code.glue, Startup.code, Startup.succ] at h
    split at h
    · rename_i jj hjj
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [henter _ (mid_afterBlock _ jj)]
      refine ⟨_, rfl, hmid _ (mid_afterBlock _ jj) ?_ ?_ hsh rfl hS⟩ <;>
        simp only [Startup.afterBlock] <;> split_ifs <;> rfl
    · simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hm := mid_initSucc j
      rw [henter _ hm]
      exact ⟨_, rfl, hmid _ hm rfl rfl hsh rfl hS⟩

theorem startAt0_site {s : Startup.D} {n : Cls → Nat} {j : Fin 3} (h : StartAt0 L s n)
    (hs : s.site = .sh j) : StartAt L 0 s n := by
  refine startAt0_sh h ?_
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs
  subst hs
  simp only [StartAt0] at h
  omega

/-- **The startup steps a lane of warp 0 well**, for a reference invariant `J` whose startup
states are `StartAt0` with no ballot and the role's counts `Z`: up to the barrier the startup's
words and counts continue (the shuffles' values from `start_recv_of`), and after it the role's
facts `henter` hold. Only the lanes' events with fewer collectives up to them are used. -/
theorem start0_step_of {J : (g : Nat) → (thread p L g).D → Prop} {Z : (Cls → Nat) → Prop}
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 0)
    (hinit : ∀ g, J g (thread p L g).init)
    (hJs : ∀ s n, J g (.inl s, n) = (StartAt0 L s n ∧ n .vote = 0 ∧ Z n))
    (hJs' : ∀ h s n, J h (.inl s, n) → StartAt0 L s n ∧ n .vote = 0)
    (hJr : ∀ h j e r d n, X.get (h, j) = some e →
      Frame.stateAt (thread p L) X h j = some (some (.inr ⟨r, d⟩, n)) →
      J h (.inr ⟨r, d⟩, n) → 3 ≤ n .shfl)
    (hZ : ∀ n e, (∀ c, ¬ Start0Cls c → Code.bump (cls L g) n e c = n c) → Z n →
      Z (Code.bump (cls L g) n e))
    (henter : ∀ s n e, s.site = .bar → StartAt0 L s n → n .vote = 0 → Z n →
      Startup.Ev L g s e → (∀ c, ¬ Start0Cls c → Code.bump (cls L g) n e c = n c) →
      J g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) (Startup.enterOf s),
        Code.bump (cls L g) n e))
    {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hR : J g (.inl s, n))
    (hprev : ∀ j, μ X j < μ X (g, k) → InWarp L 0 j.1 → ¬ Frame.Bad (thread p L) J X j) :
    Frame.StepGood (thread p L) J g (.inl s, n) e := by
  have hE := (start_fired hp hX he hσ).1
  rw [hJs] at hR
  obtain ⟨hS, hv, hz⟩ := hR
  have hn := start0_bump hS hE
  have hv' : Code.bump (cls L g) n e .vote = 0 := (hn _ (by simp [Start0Cls])).trans hv
  obtain ⟨hne, hsucc⟩ := start0_next hp hw hS hE
    fun j hs pc a b c r ok hk => by
      have hS0 := startAt0_site hS hs
      obtain ⟨r', ok', hk'⟩ := start_sent hp hw hS0 hs hE
      rw [hk] at hk' he
      simp only [Kind.shfl.injEq] at hk'
      obtain ⟨-, rfl, rfl, rfl, -⟩ := hk'
      exact start_recv_of (S := StartAt0 L)
        (fun _ _ _ _ hS hE => ⟨(start0_kind hS hE).1, (start0_kind hS hE).2.1⟩)
        (fun _ _ h h3 => startAt0_sh h h3) hinit hJs' hJr hp hX hg hw he hσ hS0 hv hs hprev
  refine ⟨hne, fun σ' h => ?_⟩
  obtain ⟨σ1, n1⟩ := σ'
  obtain ⟨-, rfl⟩ := Code.counted_next_some (C := glued p L g) h
  rcases hsucc _ h with ⟨s', hs', hS'⟩ | ⟨hb, hs'⟩
  · simp only at hs' hS'
    subst hs'
    rw [hJs]
    exact ⟨hS', hv', hZ n e hn hz⟩
  · simp only at hs'
    subst hs'
    exact henter s n e hb hS hv hz hE hn

/-! ### Every lane of warp 0 is followed through its startup -/

/-- **The startup's invariant on a lane of warp 0**: `StartAt0` and no ballot at a startup state,
the startup's three shuffles at a role state. -/
def Start0Ref (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inl s, n) => StartAt0 L s n ∧ n .vote = 0
  | (.inr _, n) => 3 ≤ n .shfl

theorem start0Ref_init : Start0Ref p L g (thread p L g).init := by
  show Start0Ref p L g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  exact ⟨⟨rfl, rfl, by simp, by simp⟩, rfl⟩

theorem enterOf_isEnter (d : Startup.D) : ∃ r, (Startup.enterOf d).site = .enter r := by
  unfold Startup.enterOf
  split_ifs <;> exact ⟨_, rfl⟩

/-- A position's collectives so far bound the shuffles of the state before it. -/
theorem shfl_le_mu {h i : Nat} {σ : (glued p L h).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X h i = some (some (σ, n))) : n .shfl ≤ μ X (h, i) := by
  have h1 := countP_take_mono isColl (X.tr h) (show i ≤ i + 1 by omega)
  rw [countColl, (counts hσ).1, (counts hσ).2] at h1
  simp only [μ]
  omega

theorem start0_stepGood (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 0) {k : Nat} {s : Startup.D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Start0Ref p L g (.inl s, n))
    (hprev : ∀ j, μ X j < μ X (g, k) → InWarp L 0 j.1 →
      ¬ Frame.Bad (thread p L) (Start0Ref p L) X j) :
    Frame.StepGood (thread p L) (Start0Ref p L) g (.inl s, n) e :=
  start0_step_of (Z := fun _ => True) hp hX hg hw (fun _ => start0Ref_init)
    (fun s n => by simp [Start0Ref]) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ h => h)
    (fun _ _ _ _ => trivial)
    (fun s n e hb hS _ _ _ hn => by
      obtain ⟨r, hr⟩ := enterOf_isEnter s
      have h3 := (startAt0_of_mid (by rw [hb]; rfl) hS).1
      simp only [Code.enter, exit, hr]
      show 3 ≤ Code.bump (cls L g) n e .shfl
      simp only [Code.bump]
      split_ifs <;> omega)
    he hσ hR hprev

/-- The collectives up to an event at a startup state of warp 0 are at most three. -/
theorem start0_mu {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event}
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hS : StartAt0 L s n) (hv : n .vote = 0) : μ X (g, k) ≤ 3 := by
  have hsk := start0_kind hS (start_fired hp hX he hσ).1
  have h3 : n .shfl ≤ 3 := by
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt0] at hS <;> omega
  simp only [μ]
  rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some,
    List.countP_append, countColl, (counts hσ).1, (counts hσ).2, hv]
  simp only [List.countP_singleton, isColl, hsk.1, Bool.or_false]
  split_ifs with hc
  · have := hsk.2.2.1 hc
    omega
  · omega

/-- No lane of warp 0 is bad at a position with at most two collectives up to it. -/
theorem start0_noBad2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ i e, X.get i = some e → InWarp L 0 i.1 → μ X i ≤ 2 →
      ¬ Frame.Bad (thread p L) (Start0Ref p L) X i := by
  refine Frame.inductive_lex (X := X) (μ X)
    (fun i => InWarp L 0 i.1 → μ X i ≤ 2 → ¬ Frame.Bad (thread p L) (Start0Ref p L) X i) ?_
  rintro ⟨g, k⟩ e he ih ⟨hg, hw⟩ hμ ⟨⟨σ, n⟩, e', he', hσ, hJ, hbad⟩
  simp only at he' hσ hJ hbad
  rw [he] at he'
  obtain rfl := Option.some.inj he'
  rcases σ with s | ⟨r, d⟩
  · refine hbad (start0_stepGood hp hX hg hw he hσ hJ fun j hj hh hB => ?_)
    obtain ⟨_, ej, hej, -⟩ := id hB
    exact ih j ej hej (.inl hj) hh (by simp only at hj; omega) hB
  · have := shfl_le_mu hσ
    have : 3 ≤ n .shfl := hJ
    omega

/-- No lane of warp 0 is bad at a startup state. -/
theorem start0_noBad (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h k : Nat}
    (hh : InWarp L 0 h)
    (hst : ∀ σ, Frame.stateAt (thread p L) X h k = some (some σ) → ∃ s, σ.1 = .inl s) :
    ¬ Frame.Bad (thread p L) (Start0Ref p L) X (h, k) := by
  rintro ⟨⟨σ, n⟩, e, he, hσ, hJ, hbad⟩
  simp only at he hσ hJ hbad
  obtain ⟨s, rfl⟩ := hst _ hσ
  have hμ := start0_mu hp hX he hσ hJ.1 hJ.2
  refine hbad (start0_stepGood hp hX hh.1 hh.2 he hσ hJ fun j hj hj0 hB => ?_)
  obtain ⟨_, ej, hej, -⟩ := id hB
  exact start0_noBad2 hp hX j ej hej hj0 (by omega) hB

/-- A startup step from a site other than the barrier stays in the startup. -/
theorem succ_stays {s s' : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartAt0 L s n)
    (hb : s.site ≠ .bar) (h : Startup.succ L g s e = some (some s')) :
    exit L g s' = none := by
  have hx : ∀ d : Startup.D, d.site.mid = true ∨ (∃ j, d.site = .sh j) → exit L g d = none := by
    rintro ⟨site, x1, x2, x3⟩ hd
    cases site <;> simp_all [exit, Startup.Site.mid]
  apply hx
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt0] at hS
  case bar => exact absurd rfl hb
  case fence =>
    simp only [Startup.succ, Option.some.injEq] at h
    subst h
    exact .inl rfl
  case sh j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Startup.word32] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        fin_cases j
        · exact .inr ⟨1, rfl⟩
        · exact .inr ⟨2, rfl⟩
        · simp only
          split_ifs
          · exact .inl rfl
          · exact .inl rfl
      · simp at h
    · simp at h
  case elect j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split_ifs
      · exact .inl (mid_firstInit j)
      · exact .inl (mid_afterBlock _ j)
    · simp at h
  case init j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl (mid_afterBlock _ _)
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl (mid_initSucc j)

/-- **Before its first event on the CTA barrier, a lane of warp 0 is followed and at a startup
state.** -/
theorem start0_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {h : Nat} (hh : InWarp L 0 h) :
    ∀ k, ((X.tr h).take k).countP (Execution.isBarId 0) = 0 →
      Frame.FollowedAt (thread p L) (Start0Ref p L) X h k ∧
      ∀ σ, Frame.stateAt (thread p L) X h k = some (some σ) → ∃ s, σ.1 = .inl s := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨⟨?_, fun σ h => ?_⟩, fun σ h => ?_⟩ <;> rw [Frame.stateAt_zero] at *
    · simp
    · cases h; exact start0Ref_init
    · cases h; exact ⟨_, rfl⟩
  | succ k ih =>
    intro hc
    have hc' : ((X.tr h).take k).countP (Execution.isBarId 0) = 0 := by
      have := countP_take_mono (Execution.isBarId 0) (X.tr h) (show k ≤ k + 1 by omega)
      omega
    obtain ⟨hF, hI⟩ := ih hc'
    by_cases hk : k < (X.tr h).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr h)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hstep := Frame.stateAt_succ (C := thread p L) he
      have hnb := start0_noBad hp hX hh hI
      cases hσ : Frame.stateAt (thread p L) X h k with
      | none =>
        have h0 : Frame.stateAt (thread p L) X h (k + 1) = none := by rw [hstep, hσ]; rfl
        refine ⟨⟨?_, fun σ h => ?_⟩, fun σ h => ?_⟩ <;> rw [h0] at * <;> simp at *
      | some σ =>
        cases σ with
        | none => exact absurd hσ hF.1
        | some σ =>
          obtain ⟨s, hs⟩ := hI σ hσ
          obtain ⟨σ1, n⟩ := σ
          simp only at hs
          subst hs
          have hJ := hF.2 _ hσ
          have hgood : Frame.StepGood (thread p L) (Start0Ref p L) h (.inl s, n) e := by
            by_contra hb
            exact hnb ⟨_, e, he, hσ, hJ, hb⟩
          have hE := (start_fired hp hX he hσ).1
          have h1 : Frame.stateAt (thread p L) X h (k + 1) = (thread p L h).next (.inl s, n) e := by
            rw [hstep, hσ]
            rfl
          refine ⟨⟨by rw [h1]; exact hgood.1, fun d hd => hgood.2 d (h1 ▸ hd)⟩,
            fun σ' hσ' => ?_⟩
          rw [h1] at hσ'
          by_cases hb : s.site = .bar
          · exfalso
            obtain ⟨site, x1, x2, x3⟩ := s
            simp only at hb
            subst hb
            simp only [Startup.Ev] at hE
            have : 0 < ((X.tr h).take (k + 1)).countP (Execution.isBarId 0) := by
              rw [List.take_add_one, he, Option.toList_some, List.countP_append]
              obtain ⟨pc, kind⟩ := e
              simp only at hE
              subst hE
              simp [Execution.isBarId]
            omega
          · obtain ⟨hg', -⟩ := Code.counted_next_some (C := glued p L h) hσ'
            simp only [glued, Code.glue, Startup.code] at hg'
            cases hsu : Startup.succ L h s e with
            | none => rw [hsu] at hg'; simp at hg'
            | some o =>
              cases o with
              | none => rw [hsu] at hg'; simp at hg'
              | some s' =>
                rw [hsu] at hg'
                simp only [Option.map_some, Option.some.injEq] at hg'
                rw [← hg']
                simp only [Code.enter, succ_stays hJ.1 hb hsu]
                exact ⟨_, rfl⟩
    · have e1 : Frame.stateAt (thread p L) X h (k + 1) = Frame.stateAt (thread p L) X h k := by
        rw [Frame.stateAt_of_le (show (X.tr h).length ≤ k + 1 by omega),
          Frame.stateAt_of_le (show (X.tr h).length ≤ k by omega)]
      refine ⟨⟨?_, fun d hd => ?_⟩, fun σ hσ => ?_⟩ <;> rw [e1] at *
      · exact hF.1
      · exact hF.2 d hd
      · exact hI σ hσ

/-- **A lane of warp 0 with no event on the CTA barrier** has not exited, and every state of its
trace that the machine follows is a startup state with `StartAt0`, at a pc no later than the
barrier's (what lane T4's `Warp0Lag` reads). -/
theorem warp0_before_bar (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {y : Nat} (hy : InWarp L 0 y) (hb : (X.tr y).countP (Execution.isBarId 0) = 0) :
    (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
      ∀ k σ, Frame.stateAt (thread p L) X y k = some (some σ) →
        ∃ s, σ.1 = .inl s ∧ StartAt0 L s σ.2 ∧ σ.2 .vote = 0 ∧ s.site.pc ≤ 173 := by
  have hc : ∀ k, ((X.tr y).take k).countP (Execution.isBarId 0) = 0 := fun k => by
    have := List.Sublist.countP_le (p := Execution.isBarId 0) (List.take_sublist k (X.tr y))
    omega
  have hst : ∀ k σ, Frame.stateAt (thread p L) X y k = some (some σ) →
      ∃ s, σ.1 = .inl s ∧ StartAt0 L s σ.2 ∧ σ.2 .vote = 0 ∧ s.site.pc ≤ 173 := by
    intro k σ hσ
    obtain ⟨hF, hI⟩ := start0_state hp hX hy k (hc k)
    obtain ⟨s, hs⟩ := hI σ hσ
    have hJ := hF.2 σ hσ
    obtain ⟨σ1, n⟩ := σ
    simp only at hs
    subst hs
    exact ⟨s, rfl, hJ.1, hJ.2, startAt0_pc hJ.1⟩
  refine ⟨fun k pc he => ?_, hst⟩
  rcases Frame.firedU (fun g hg => thread_sound hp hg) hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc', f, h⟩
  · cases σ with
    | none => exact (start0_state hp hX hy k (hc k)).1.1 hσ
    | some σ =>
      obtain ⟨s, hs, hS, -, -⟩ := hst k σ hσ
      obtain ⟨σ1, n⟩ := σ
      simp only at hs
      subst hs
      exact (start0_kind hS (start_fired hp hX he hσ).1).2.1 rfl
  · cases h

end
end PTX.Kernels.TmlFa4Fwd.Proof
