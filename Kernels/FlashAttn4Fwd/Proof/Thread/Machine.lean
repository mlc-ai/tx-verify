-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Entry
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueShfl
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueFence
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueWarp0
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRank
public import Lemmas.Flow.Compose

@[expose] public section

/-! # A thread of the kernel as a site machine

Every thread runs the prologue and is then followed in its role. The prologue's hand-off names
the role by the warp index (`Prologue.next` at the cluster wait gives a `RoleKind`); the machine
continues in the role's first state (`Role.start`). A role's states, sites, facts, invariant and
successors are those of its own code machine (`Loader.code`, `Mma.code`, `Store.code`,
`Softmax.code`, `Correction.code`, and the idle warp's), which sits inside the thread's
(`Code.Embeds`), so its obligations are the role's (`stepAt`); the store warp's invariant holds
from its first event on.
The machine's obligations (`Flow.Code.Sound`) are the prologue's, the roles' and the entries'
(`Thread/Entry.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A thread's abstract states: the prologue, then its role. -/
abbrev ThreadD := Prologue.D ⊕ Role

/-- The machine state after the prologue's successor: a prologue state, or the role's first
state (`none` if the role is not composed). -/
def handoff (L : Launch) (g : Nat) : Prologue.D ⊕ RoleKind → Option ThreadD
  | .inl p => some (.inl p)
  | .inr k => (Role.start L g k).map .inr

/-- A thread of the kernel as a code machine. Reducible, so that its states are `ThreadD` to
`simp`. -/
@[reducible] def code (L : Launch) (g : Nat) : PTX.Flow.Code kernel asms L g where
  D := ThreadD
  init := .inl ⟨.shfl0⟩
  pc := fun
    | .inl p => p.site.pc
    | .inr (.idle s) => s.site.pc
    | .inr (.loader d) => d.site.pc
    | .inr (.mma d) => d.site.pc
    | .inr (.store d) => d.site.pc
    | .inr (.softmax d) => d.site.pc
    | .inr (.corr d) => d.site.pc
  facts := fun
    | .inl p => Prologue.facts L g p
    | .inr (.idle s) => Idle.facts L g s
    | .inr (.loader d) => Loader.facts L g d
    | .inr (.mma d) => Mma.facts L g d
    | .inr (.store d) => Store.facts L g d
    | .inr (.softmax d) => Softmax.facts L g d
    | .inr (.corr d) => Correction.facts L g d
  sub := fun
    | .inr (.mma d) => d.site.sub
    | .inr (.softmax d) => d.site.sub
    | .inr (.corr d) => d.site.sub
    | _ => 0
  inv := fun
    | .inl p => Prologue.Inv L g p
    | .inr (.idle s) => Idle.Inv L g s
    | .inr (.loader d) => Loader.Inv L g d
    | .inr (.mma d) => Mma.Inv L g d ∧ Mma.BaseOk d
    | .inr (.store d) => d.site = .setMaxReg ∨ Store.Inv L g d
    | .inr (.softmax d) => Softmax.Inv L g d
    | .inr (.corr d) => Correction.Inv L g d
  next := fun d e => match d with
    | .inl p => (Prologue.next L g p e).map (Option.bind · (handoff L g))
    | .inr (.idle s) => (Idle.next s e).map (Option.map (.inr ∘ .idle))
    | .inr (.loader d) => (Loader.next L g d e).map (Option.map (.inr ∘ .loader))
    | .inr (.mma d) => (Mma.next L g d e).map (Option.map (.inr ∘ .mma))
    | .inr (.store d) => (Store.next L g d e).map (Option.map (.inr ∘ .store))
    | .inr (.softmax d) => (Softmax.next L g d e).map (Option.map (.inr ∘ .softmax))
    | .inr (.corr d) => (Correction.next L g d e).map (Option.map (.inr ∘ .corr))

/-- A role state's successor is a state of the same role. -/
theorem code_next_inr {L : Launch} {g : Nat} {r : Role} {e : Event} {d' : ThreadD}
    (h : (code L g).next (.inr r) e = some (some d')) : ∃ r', d' = .inr r' ∧ r'.kind = r.kind := by
  cases r <;> simp only [code, Option.map_eq_some_iff] at h
  all_goals
    obtain ⟨_, -, h⟩ := h
    simp only [Function.comp] at h
    obtain ⟨r', -, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩

/-! ### The roles inside the thread's machine -/

theorem embeds_loader (L : Launch) (g : Nat) :
    Code.Embeds (Loader.code asms L g) (code L g) (.inr ∘ .loader) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

theorem embeds_mma (L : Launch) (g : Nat) (pro : Nat → Value) :
    Code.Embeds (Mma.code asms L g pro) (code L g) (.inr ∘ .mma) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

theorem embeds_softmax (L : Launch) (g : Nat) :
    Code.Embeds (Softmax.code asms L g) (code L g) (.inr ∘ .softmax) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

theorem embeds_corr (L : Launch) (g : Nat) :
    Code.Embeds (Correction.code asms L g) (code L g) (.inr ∘ .corr) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

theorem embeds_store (L : Launch) (g : Nat) :
    Code.Embeds (Store.code asms L g) (code L g) (.inr ∘ .store) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

namespace Prologue

/-- Each prologue site is an unguarded event instruction. -/
theorem site_ok (s : Site) :
    ∃ ins, kernel.code[s.pc]? = some ins ∧ ins.op.isLocal = false ∧ ins.guard = none := by
  cases s with
  | shfl0 => exact ⟨_, Flow.code_shfl_0, rfl, rfl⟩
  | shfl1 => exact ⟨_, Flow.code_shfl_1, rfl, rfl⟩
  | shfl2 => exact ⟨_, Flow.code_shfl_2, rfl, rfl⟩
  | elect12 => exact ⟨_, Flow.code_elect_0, rfl, rfl⟩
  | init320 => exact ⟨_, Flow.code_mbarInit_0, rfl, rfl⟩
  | fence0 => exact ⟨_, Flow.code_fenceMbarInit_0, rfl, rfl⟩
  | elect e =>
    obtain ⟨_, hc, -, -⟩ := code_elect e
    exact ⟨_, hc, rfl, rfl⟩
  | init j =>
    obtain ⟨ins, hc, hg, hadv⟩ := code_init j
    refine ⟨ins, hc, ?_, hg⟩
    revert hadv
    cases ins.op <;> simp [AdvancesOp, Op.isLocal]
  | shfl3 => exact ⟨_, Flow.code_shfl_3, rfl, rfl⟩
  | fence1 => exact ⟨_, Flow.code_fenceMbarInit_1, rfl, rfl⟩
  | clArrive => exact ⟨_, Flow.code_clusterArrive_0, rfl, rfl⟩
  | clWait => exact ⟨_, Flow.code_clusterWait_0, rfl, rfl⟩

/-- Every prologue event steps to its successor. -/
theorem step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  cases s with
  | shfl0 => exact step_shfl0 hpre rfl h hc hf
  | shfl1 => exact step_shfl1 rfl h hc hf
  | shfl2 => exact step_shfl2 hpre rfl h hc hf
  | elect12 => exact step_elect12 hpre rfl hi h hc hf
  | init320 => exact step_init320 hpre rfl h hc hf
  | fence0 => exact step_fence0 hpre rfl h hc hf
  | elect k => exact step_elect hpre k rfl hi h hc hf
  | init j => exact step_init hpre j rfl hi h hc hf
  | shfl3 => exact step_shfl3 hpre rfl h hc hf
  | fence1 => exact step_fence1 rfl h hc hf
  | clArrive => exact step_clArrive rfl h hc hf
  | clWait => exact step_clWait hpre hg rfl h hc hf

end Prologue

/-- The first state of a composed role, from the prologue's facts at the role's entry. -/
theorem good_start {L : Launch} {g : Nat} {r : Role} {t : TState}
    (hr : Role.start L g (RoleKind.ofWarp (warpOf L g)) = some r)
    (h : Prologue.Good L g (.inr (RoleKind.ofWarp (warpOf L g))) t) :
    (code L g).Good (some (.inr r)) t := by
  have hk := Role.start_kind hr
  cases r with
  | idle s =>
    have hk : RoleKind.ofWarp (warpOf L g) = .idle := hk.symm
    have hw : warpOf L g = 15 := RoleKind.ofWarp_idle.mp hk
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.idle.injEq] at hr
    subst hr
    have h' := Idle.entry hw h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, hw⟩
  | loader d =>
    have hk : RoleKind.ofWarp (warpOf L g) = .loader := hk.symm
    have hw : warpOf L g = 14 := RoleKind.ofWarp_loader.mp hk
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.loader.injEq] at hr
    subst hr
    obtain ⟨h', hi⟩ := Loader.entry hw h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, hi⟩
  | mma d =>
    have hk : RoleKind.ofWarp (warpOf L g) = .mma := hk.symm
    have hw : warpOf L g = 12 := RoleKind.ofWarp_mma.mp hk
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.mma.injEq] at hr
    subst hr
    obtain ⟨h', hi⟩ := Mma.entry hw h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, hi, nofun⟩
  | store d =>
    have hk : RoleKind.ofWarp (warpOf L g) = .store := hk.symm
    have hw : warpOf L g = 13 := RoleKind.ofWarp_store.mp hk
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.store.injEq] at hr
    subst hr
    have h' := Store.entry hw h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, .inl rfl⟩
  | corr d =>
    have hk : RoleKind.ofWarp (warpOf L g) = .corr := hk.symm
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.corr.injEq] at hr
    subst hr
    obtain ⟨h', hi⟩ := Correction.entry h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, hi⟩
  | softmax d =>
    have hk : RoleKind.ofWarp (warpOf L g) = .softmax := hk.symm
    have hw : warpOf L g < 8 := RoleKind.ofWarp_softmax.mp hk
    rw [hk] at hr h
    simp only [Role.start, Option.some.injEq, Role.softmax.injEq] at hr
    subst hr
    obtain ⟨h', hi⟩ := Softmax.entry hw h
    exact ⟨⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩, hi⟩

/-- What a step of the thread's machine owes (the continuing case of `Code.StepAt.step`). -/
abbrev ThreadStep (L : Launch) (g : Nat) (d : ThreadD) (e : Event) (u : TState) : Prop :=
  (code L g).next d e = some none ∨ ∃ d' : ThreadD, ∃ t', (code L g).next d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code L g).Good (some d') t'

/-- A prologue step as a step of the thread's machine. -/
theorem of_prologue {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {u : TState}
    (h : Prologue.Step L g p u e) : ThreadStep L g (Sum.inl p) e u := by
  rcases h with hn | ⟨d', t', hn, hr, hgd⟩
  · exact Or.inl (by simp [code, hn])
  · rcases d' with p' | k
    · exact Or.inr ⟨Sum.inl p', t', by simp [code, hn, handoff], hr,
        ⟨⟨hgd.1.1, hgd.1.2.1, hgd.1.2.2.1, hgd.1.2.2.2.1, hgd.1.2.2.2.2⟩, hgd.2⟩⟩
    · have hk : k = RoleKind.ofWarp (warpOf L g) := by
        obtain ⟨s⟩ := p
        cases s <;> simp [Prologue.next] at hn
        all_goals (repeat' split at hn) <;> simp_all
      subst hk
      cases hst : Role.start L g (RoleKind.ofWarp (warpOf L g)) with
      | none => exact Or.inl (by simp [code, hn, handoff, hst])
      | some r =>
        exact Or.inr ⟨Sum.inr r, t', by simp [code, hn, handoff, hst], hr, good_start hst hgd⟩

/-- The idle warp's obligations. -/
theorem stepAt_idle {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (s : Idle.D) : (code L g).StepAt (.inr (.idle s)) where
  site _ := by
    obtain ⟨ins, hc, hl, hgd⟩ := Idle.site_ok s
    exact ⟨ins, hc, hl, by simp [hgd, Code.GuardTrue]⟩
  step := by
    intro t e u ins h hi hc hf
    have hc : kernel.code[s.site.pc]? = some ins := hc
    have hf : Fires s.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
    have hi : Idle.Inv L g s := hi
    have h' : At t s.site.pc (Idle.facts L g s) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    obtain ⟨site⟩ := s
    cases site with
    | setMaxReg =>
      obtain ⟨d', t', hn, hr, ht⟩ := Idle.step_setMaxReg hpre rfl h' hc hf
      exact .inl (.inr ⟨Sum.inr (.idle d'), t', by simp [code, hn], hr,
        ⟨⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi⟩⟩)
    | exit => exact (Idle.exit_no_step rfl hc hf).elim

/-- The store warp's obligations are its code machine's. -/
theorem stepAt_store {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (d : Store.D) : (code L g).StepAt (.inr (.store d)) :=
  (embeds_store L g).stepAt id (Store.stepAt hpre hg d)

set_option maxHeartbeats 1000000 in
/-- Every thread of a launch satisfying the precondition is simulated by its code machine. -/
theorem sound {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) : (code L g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := Prologue.start (g := g) hpre
    exact ⟨t, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩,
      Prologue.inv_of (by simp) (by simp) (by simp) (by simp)⟩
  steps := by
    rintro (p | r)
    · constructor
      · intro _
        obtain ⟨ins, hc, hl, hgd⟩ := Prologue.site_ok p.site
        exact ⟨ins, hc, hl, by simp [hgd, Code.GuardTrue]⟩
      · intro t e u ins h hi hc hf
        have hc : kernel.code[p.site.pc]? = some ins := hc
        have hf : Fires p.site.pc (eventTmpl asms L g t ins.op) e (some u) := hf
        have hi : Prologue.Inv L g p := hi
        have h' : At t p.site.pc (Prologue.facts L g p) :=
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
        exact .inl (of_prologue (Prologue.step hpre hg hi h' hc hf))
    cases r with
    | idle s => exact stepAt_idle hpre s
    | loader d => exact (embeds_loader L g).stepAt id (Loader.stepAt hpre hg d)
    | mma d => exact (embeds_mma L g d.pro).stepAt id (Mma.stepAt hpre hg d.pro d)
    | store d => exact stepAt_store hpre hg d
    | corr d => exact (embeds_corr L g).stepAt id (Correction.stepAt hpre hg d)
    | softmax d => exact (embeds_softmax L g).stepAt id (Softmax.stepAt hpre hg d)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
