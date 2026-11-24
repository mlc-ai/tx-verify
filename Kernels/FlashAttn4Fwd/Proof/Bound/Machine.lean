-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Prologue
public import Kernels.FlashAttn4Fwd.Proof.Bound.Loader
public import Kernels.FlashAttn4Fwd.Proof.Bound.Mma
public import Kernels.FlashAttn4Fwd.Proof.Bound.Store
public import Kernels.FlashAttn4Fwd.Proof.Bound.Softmax
public import Kernels.FlashAttn4Fwd.Proof.Bound.Correction

@[expose] public section

/-! # The rank of a thread's machine

The rank of a thread's state (`rank`): along the prologue `cap L + 256` minus the prologue's
position, then its role's rank (`Bound/{Loader,Mma,Store,Softmax,Correction}.lean`), at most
`cap L` at the role's first state (`roleRank_start`). Every step of the machine lowers the rank by
its count (`rank_step`; the MMA warp's rank needs at least one cluster), and the initial rank is
the uniform bound `N P` (`rank_init`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Bound
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The idle warp's rank: its register reduction, then nothing. -/
def idleRank (s : Idle.D) : Nat :=
  match s.site with
  | .setMaxReg => 1
  | .exit => 0

/-- The rank of a role's state. -/
def roleRank (L : Launch) (g : Nat) : Role → Nat
  | .idle s => idleRank s
  | .loader d => loaderRank L g d
  | .mma d => mmaRank L g d
  | .store d => storeRank L g d
  | .softmax d => softmaxRank L g d
  | .corr d => corrRank L g d

/-- The rank of a thread's state. -/
def rank (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => cap L + 256 - Prologue.ord p.site
  | .inr r => roleRank L g r

theorem idleRank_step {s s' : Idle.D} {e : Event} (h : Idle.next s e = some (some s')) :
    idleRank s' + (if e.counts then 1 else 0) ≤ idleRank s := by
  have hc := counts_le e
  obtain ⟨site⟩ := s
  cases site <;> simp only [Idle.next, Option.some.injEq, reduceCtorEq] at h
  subst h
  simp only [idleRank]
  omega

/-- A role's first state has rank at most `cap L`. -/
theorem roleRank_start {L : Launch} {g : Nat} {k : RoleKind} {r : Role}
    (h : Role.start L g k = some r) : roleRank L g r ≤ cap L := by
  cases k <;> simp only [Role.start, Option.some.injEq] at h <;> subst h
  case idle =>
    simp only [roleRank, idleRank, Idle.start]
    unfold cap
    omega
  case loader =>
    simp only [roleRank]
    exact loaderRank_entry L g rfl
  case mma =>
    simp only [roleRank]
    exact mmaRank_entry L g rfl
  case store =>
    simp only [roleRank]
    exact storeRank_entry L g rfl
  case softmax =>
    simp only [roleRank]
    exact softmaxRank_entry L g rfl
  case corr =>
    simp only [roleRank]
    exact corrRank_entry L g rfl

/-- A role step of the machine: the role's own step, mapped into the thread's states. -/
theorem role_map {α : Type} {f : α → Role} {o : Option (Option α)} {r' : Role}
    (h : o.map (Option.map (Sum.inr ∘ f)) = some (some (Sum.inr r' : ThreadD))) :
    ∃ a, o = some (some a) ∧ f a = r' := by
  rcases o with _ | _ | a
  · cases h
  · cases h
  · simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Sum.inr.injEq] at h
    exact ⟨a, rfl, h⟩

/-- A composed role's step lowers its rank by its count. -/
theorem roleRank_step {L : Launch} {g : Nat} {r r' : Role} {e : Event}
    (hG : 0 < Mma.clusters L) (h : (code L g).next (.inr r) e = some (some (.inr r'))) :
    roleRank L g r' + (if e.counts then 1 else 0) ≤ roleRank L g r := by
  cases r with
  | idle s =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact idleRank_step hn
  | loader d =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact loaderRank_step hn
  | mma d =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact mmaRank_step hG hn
  | store d =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact storeRank_step hn
  | softmax d =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact softmaxRank_step hn
  | corr d =>
    obtain ⟨_, hn, rfl⟩ := role_map h
    exact corrRank_step hn

/-- **Every step of a thread's machine lowers its rank by its count.** -/
theorem rank_step {L : Launch} {g : Nat} {d d' : ThreadD} {e : Event} (hG : 0 < Mma.clusters L)
    (h : (code L g).next d e = some (some d')) :
    rank L g d' + (if e.counts then 1 else 0) ≤ rank L g d := by
  have hc := counts_le e
  rcases d with p | r
  · have hp := Prologue.ord_lt p.site
    simp only [code, Option.map_eq_some_iff] at h
    obtain ⟨o, hn, ho⟩ := h
    rcases o with _ | p' | k
    · cases ho
    · simp only [Option.bind_some, handoff, Option.some.injEq] at ho
      subst ho
      have := Prologue.next_ord hn
      simp only [rank]
      omega
    · simp only [Option.bind_some, handoff, Option.map_eq_some_iff] at ho
      obtain ⟨r, hr, rfl⟩ := ho
      have := roleRank_start hr
      simp only [rank]
      omega
  · rcases d' with p' | r'
    · cases r <;> simp only [code, Option.map_eq_some_iff] at h <;> obtain ⟨o, -, ho⟩ := h <;>
        cases o <;> simp at ho
    · exact roleRank_step hG h

/-- **The initial rank is the uniform bound.** -/
theorem rank_init {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat) :
    rank L g (code L g).init ≤ N P := by
  have := cap_eq hpre
  simp only [rank, Prologue.ord]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Bound
