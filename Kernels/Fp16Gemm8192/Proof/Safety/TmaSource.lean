-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.Tensor
public import Lemmas.Protocol.ObjectSource
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The sources of the records of an mbarrier object

Every record of an object that is not an initialization comes from an arrival, a poll, a tensor
copy, a commit or a cluster launch control request of a role's thread (`noninit_source`). Each names
a ring barrier of some CTA of the thread's cluster, which lives in the leader CTA when it is a
leader-only barrier (`ThreadFacts.ring_event`): the arrivals, copies and commits go where their
tables say, and the polls of such a barrier are by a leader CTA's threads. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The object `m`, used by the thread `g` at its `j`-th event from a role state, is a ring barrier
of a CTA of the thread's cluster, that is in an even CTA when it is a leader-only barrier. -/
def Classified (L : Launch) (X : Execution) (g j : Nat) (m : Loc) : Prop :=
  ∃ (ρ : Prologue.Role) (b : Bar) (cta : Nat), g < L.threads ∧ (∃ ev, X.get (g, j) = some ev) ∧
    Frame.stateAt (code L) X g j = some (some (.inr ρ)) ∧ b.Valid ∧ cta < L.grid ∧
    L.clusterOfCta cta = L.clusterOfCta (g / L.block) ∧ m = b.loc L cta ∧
    (b.leaderOnly = true → cta % 2 = 0)

theorem arriveBy_role {g : Nat} {d : ThreadD} {b : Bar} (h : b.arriveBy L g d) :
    ∃ ρ, d = .inr ρ := by
  obtain ⟨r, s, f⟩ := b
  cases r <;> cases f <;> simp only [Bar.arriveBy] at h <;>
  first
  | (rcases h with ⟨l, rfl⟩ | ⟨⟨mm, rfl⟩, -⟩ | ⟨sd, rfl⟩ | ⟨⟨cs, rfl⟩, -⟩ <;> exact ⟨_, rfl⟩)
  | (obtain ⟨⟨l, rfl⟩, -⟩ := h; exact ⟨_, rfl⟩)
  | (obtain ⟨sd, rfl⟩ := h; exact ⟨_, rfl⟩)

theorem commitBy_role {d : ThreadD} {b : Bar} (h : b.commitBy d) : ∃ ρ, d = .inr ρ := by
  obtain ⟨r, s, f⟩ := b
  cases r <;> cases f <;> simp only [Bar.commitBy] at h <;>
  first
  | (obtain ⟨mm, rfl⟩ := h; exact ⟨_, rfl⟩)
  | (obtain ⟨mm, rfl, -⟩ := h; exact ⟨_, rfl⟩)

theorem pollBy_role {g : Nat} {d : ThreadD} {b : Bar} (h : b.pollBy L g d) : ∃ ρ, d = .inr ρ := by
  obtain ⟨r, s, f⟩ := b
  cases r <;> cases f <;> simp only [Bar.pollBy] at h <;>
  first
  | (obtain ⟨l, rfl⟩ := h; exact ⟨_, rfl⟩)
  | (obtain ⟨mm, rfl, -⟩ := h; exact ⟨_, rfl⟩)
  | (obtain ⟨⟨cs, rfl⟩, -⟩ := h; exact ⟨_, rfl⟩)

theorem leaderOnly_arriveLeader {b : Bar} (h : b.leaderOnly = true) : b.arriveLeader = true := by
  obtain ⟨r, s, f⟩ := b
  cases r <;> cases f <;> simp_all [Bar.leaderOnly, Bar.arriveLeader]

theorem commitBy_not_leaderOnly {d : ThreadD} {b : Bar} (h : b.commitBy d) :
    b.leaderOnly = false := by
  obtain ⟨r, s, f⟩ := b
  cases r <;> cases f <;> simp_all [Bar.commitBy, Bar.leaderOnly]

/-- An arrival names a classified object. -/
theorem arrive_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc tx c : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩) : Classified L X g j m := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  have hre := ht.ring_event hg he hσ
  obtain ⟨b, cta, hb, rfl⟩ := hre.loc m (Or.inl ⟨tx, c, rel, sc, rfl⟩)
  obtain ⟨hby, hcta, -, -⟩ := hre.arrive b cta tx c rel sc rfl hb
  obtain ⟨ρ, rfl⟩ := arriveBy_role hby
  have hgc := cta_lt_grid hpre hg
  refine ⟨ρ, b, cta, hg, ⟨_, he⟩, hσ, hb, ?_, ?_, rfl, fun hlo => ?_⟩
  · unfold Bar.arriveCta at hcta
    split_ifs at hcta <;> omega
  · unfold Bar.arriveCta at hcta
    simp only [clusterOfCta_eq hpre]
    split_ifs at hcta <;> omega
  · have hl := leaderOnly_arriveLeader hlo
    unfold Bar.arriveCta at hcta
    simp only [hl, ↓reduceIte] at hcta
    omega

/-- A poll names a classified object. -/
theorem wait_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .wait m p ok acq sc⟩) : Classified L X g j m := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  have hre := ht.ring_event hg he hσ
  obtain ⟨b, cta, hb, rfl⟩ := hre.loc m (Or.inr (Or.inl ⟨p, ok, acq, sc, rfl⟩))
  obtain ⟨hby, hcta⟩ := hre.wait b cta p ok acq sc rfl hb
  obtain ⟨ρ, rfl⟩ := pollBy_role hby
  have hgc := cta_lt_grid hpre hg
  exact ⟨ρ, b, cta, hg, ⟨_, he⟩, hσ, hb, by omega, by simp only [Launch.clusterOfCta, hcta], rfl,
    hre.wait_leader b cta p ok acq sc rfl hb⟩

/-- A commit's target is a classified object. -/
theorem commit_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g j pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩) (hm : TcCommit.target sp rank = some m) :
    Classified L X g j m := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  have hre := ht.ring_event hg he hσ
  obtain ⟨b, cta, hb, rfl⟩ := hre.loc m (Or.inr (Or.inr ⟨sp, rank, rfl, hm⟩))
  obtain ⟨hby, hev, hr2, hcta, -⟩ := hre.commit sp rank b cta rfl hm hb
  obtain ⟨ρ, rfl⟩ := commitBy_role hby
  have hgc := cta_lt_grid hpre hg
  have hgrid := hpre.grid
  refine ⟨ρ, b, cta, hg, ⟨_, he⟩, hσ, hb, by omega, ?_, rfl, fun hlo => ?_⟩
  · simp only [clusterOfCta_eq hpre]
    omega
  · rw [commitBy_not_leaderOnly hby] at hlo
    cases hlo

/-- A tensor copy's completion barrier is a classified object. -/
theorem tensor_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {address : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i address s) : Classified L X i.1 i.2 s.mbar := by
  obtain ⟨l, b, hσ, hg, hm⟩ := tensor_source hX ht hi
  obtain ⟨pc, he⟩ := hi
  have hgc := cta_lt_grid hpre hg
  have hs := (InputRing.slotOf b).isLt
  refine ⟨.loader l, ⟨.input, (InputRing.slotOf b).val, true⟩, 2 * (i.1 / L.block / 2), hg, ⟨_, he⟩,
    hσ,
    by simp [Bar.Valid, Ring.slots], by omega, ?_, by rw [hm, InputRing.fullLoc_bar],
    fun _ => by omega⟩
  simp only [clusterOfCta_eq hpre]
  omega

/-- A cancellation request's response barrier in a target CTA is a classified object. -/
theorem clc_classified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i : EvId} {sp : Clc.Spec} {tg : List Nat} (hi : X.ClcIssue i sp tg)
    {c : Nat} (hc : c ∈ tg) : Classified L X i.1 i.2 { sp.mbar with cta := c } := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨b, hb, hby, hmb, -, hcl⟩ := (ht.ring_event hg he hσ).clc _ _ rfl
  obtain ⟨rg, sl, f⟩ := b
  simp only [Bar.Valid] at hb
  cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
  obtain rfl : sl = 0 := by omega
  obtain ⟨⟨sd, rfl⟩, -⟩ := hby
  have hcg : c < L.grid := ((hX.clc.2.2.2.1 i sp tg ⟨pc, he⟩).2.2 c).mp hc |>.2.2.2.2.2.2.1
  refine ⟨.sched sd, ⟨.clc, 0, true⟩, c, hg, ⟨_, he⟩, hσ, Nat.one_pos, hcg, ?_, by rw [hmb]; rfl,
    fun h => by simp [Bar.leaderOnly] at h⟩
  simp only [clusterOfCta_eq hpre]
  have := hcl c hc
  omega

/-- **Every record of an object that is not an initialization has a classified source.** -/
theorem noninit_source (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m)
    (hn : ∀ n, r.action ≠ .init n) :
    Classified L X r.id.issuer.1 r.id.issuer.2 m := by
  cases record_source hX.tma.2.2.1 hr with
  | inval _ he _ => exact (no_inval hX ht ⟨_, he⟩).elim
  | init hid he ha => exact absurd ha (hn _)
  | arrive hid he ha =>
    rw [hid]
    exact arrive_classified hpre hX ht he
  | wait hid he ha =>
    rw [hid]
    exact wait_classified hpre hX ht he
  | tensor hid he hm ha =>
    rw [hid]
    subst hm
    exact tensor_classified hpre hX ht ⟨_, he⟩
  | bulk hid he => exact (no_copy hX ht ⟨_, he⟩).elim
  | increment hid he => exact (no_asyncArrive hX ht ⟨_, he⟩).elim
  | arriveOn hid he => exact (no_asyncArrive hX ht ⟨_, he⟩).elim
  | commit hid he ht' ha =>
    rw [hid]
    exact commit_classified hpre hX ht he ht'
  | clc hid he hm htg ha =>
    rw [hid]
    subst hm
    exact clc_classified hpre hX ht ⟨_, he⟩ htg

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
