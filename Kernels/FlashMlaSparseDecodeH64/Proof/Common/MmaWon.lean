-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Won

@[expose] public section

/-! # The MMA lane won its election

The MMA instance of `Common/SubWon.lean`. A lane of warp 4 that loses the election at pc 1853 is
handed back to warpgroup 1's idle code (`lose_idle`), so a lane with an event of the MMA code after
the election won it (`mma_won`): an earlier event of the lane is the election with the full mask
whose leader is the lane's own index. Nor does it leave the MMA code after the election (`PostR`,
`post_next`): a later state or event of a lane with an event there is the role's (`post_state`,
`post_at`). For the MMA role's exports (`Mma/Export/{Elect,Count,Time}.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **A lane that loses the election enters the idle region.** -/
theorem lose_idle {d : Mma.D} {n : Cls → Nat} (hs : d.site = .elect) {pc mk inst ld : Nat}
    (hld : PTX.laneOf L g ≠ ld) {σ' : (thread P L g).D}
    (hn : (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n))
      ⟨pc, .elect mk inst ld⟩ = some (some σ')) : IdleR σ' := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  subst hs
  simp only [Code.toMachine, Mma.succ, hld, ↓reduceIte, Option.map_some,
    Option.some.injEq] at hn
  subst hn
  cases hok : subOk L g .idle <;>
    simp [Code.backEnter, subBack, Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel,
      hok, IdleR]

/-- An MMA event after pc 1853 is not the election's. -/
private theorem not_elect {d : Mma.D} (hE : Mma.Ev L g d e) (hr : 1853 < e.pc) :
    d.site ≠ .elect := by
  intro h
  have h1 := hE.1
  rw [h] at h1
  simp only [Mma.Site.pc] at h1
  omega

/-- **A lane at an MMA state after the election, with one election counted, won it**: an
earlier event of the lane is the election at pc 1853 with the full mask whose leader is the
lane's index. -/
theorem mma_won_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (h1 : n (.mma .elect) = 1) :
    ∃ j < k, ∃ inst, X.get (g, j) = some ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ := by
  have h2 := state_count hσ (.mma .elect)
  simp only at h2
  rw [h2] at h1
  obtain ⟨f, hf, hcl⟩ := List.countP_pos_iff.mp (by rw [h1]; exact Nat.one_pos)
  obtain ⟨j, hjk, hj⟩ := get_lt_of_mem_take hf
  obtain ⟨pc, kd⟩ := f
  have hk : ∃ mk inst ld, kd = .elect mk inst ld ∧ 1853 ≤ pc ∧ pc ≤ 2160 := by
    cases kd with
    | elect mk inst ld =>
      simp only [cls, Mma.cls, Mma.inRole, Bool.and_eq_true, decide_eq_true_eq] at hcl
      exact ⟨mk, inst, ld, rfl, hcl.1⟩
    | wait l q ok a sc => cases ok <;> simp [cls, Mma.cls, Mma.kindOf] at hcl
    | tc t => cases t <;> simp [cls, Mma.cls, Mma.kindOf] at hcl
    | _ => simp [cls, Mma.cls, Mma.kindOf] at hcl
  obtain ⟨mk, inst, ld, rfl, hpc1, hpc2⟩ := hk
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  have hrj : 1850 ≤ pc ∧ pc < 2162 := ⟨by omega, by omega⟩
  obtain ⟨dj, nj, rfl, -, hEj, hlj, -⟩ := mma_state hJj hij hevj hpcj hrj
  obtain ⟨hsj, rfl, rfl⟩ := Mma.ev_elect hlj hEj
  refine ⟨j, hjk, inst, ?_⟩
  rw [won_of hj hjk hσj hσ (fun h => h) (fun h => by simp [Code.toMachine, Mma.succ, hsj] at h)
    fun hld _ h => lose_idle hsj hld h]
  exact hj

/-- **A lane with an event of the MMA code after the election won it**: an earlier event of the
lane is the election at pc 1853 with the full mask whose leader is the lane's index. -/
theorem mma_won (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) :
    ∃ j < k, ∃ inst, X.get (g, j) = some ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hE, -, -⟩ := mma_state hJ hi hev hpc ⟨by omega, hr.2⟩
  have hu : n (.mma .ub) = 0 := (state_count hσ (.mma .ub)).trans (take_noUb hX he)
  exact mma_won_of hp hX hFw hσ (Mma.elect_one (hR (state_ub hX hσ he) hu) (not_elect hE hr.1))

/-- The MMA states after the election: no hand-back. -/
def PostR : (thread P L g).D → Prop := SubR .mma fun d => Mma.Post d.site

/-- **The thread machine stays in the MMA code after the election.** -/
theorem post_next {σ σ' : (thread P L g).D} (h : PostR σ) {f : Event}
    (hn : (thread P L g).toMachine.next (some σ) f = some (some σ')) : PostR σ' :=
  sub_next (j := .mma) (Q := fun d : Mma.D => Mma.Post d.site) (fun {d a f} hd ha =>
    have hp : Mma.Post a.site := Mma.succ_post (P := P) (L := L) (g := g) (d := d) (f := f) hd ha
    ⟨hp, by simp [subBack, hp.2 _]⟩) h hn

/-- The later state, before any undefined behaviour of the lane. -/
private theorem post_core (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j i : Nat} {e0 : Event}
    (he0 : X.get (g, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr : 1853 < e0.pc ∧ e0.pc < 2162) (hji : j ≤ i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hu : σ.2 .ub = 0) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) ∧
      Mma.Ref L g d (fun c => ((X.tr g).take i).countP (Mma.cls c)) ∧ Mma.Post d.site := by
  obtain ⟨σ0, hσ0, hJ0, hi0, hev0, hpc0⟩ := ev_at hp hX hFw he0 hu0
  obtain ⟨d0, n0, rfl, -, hE0, hl0, -⟩ := mma_state hJ0 hi0 hev0 hpc0 ⟨by omega, hr.2⟩
  have hJ := (follow_iff.mp hFw g (Frame.lt_of_get hX he0) i).2 σ hσ
  obtain ⟨d, n, rfl, hP⟩ :=
    region_stays PostR post_next hσ0 ⟨d0, n0, rfl, not_elect hE0 hr.1, hl0⟩ i hji σ hσ
  obtain ⟨-, ⟨-, -, ⟨hR, -⟩, -⟩, -, -⟩ := hJ
  have hc : ∀ c, n c = ((X.tr g).take i).countP (cls c) := state_count hσ
  have hR := hR hu
  simp only [hc] at hR
  exact ⟨d, n, rfl, hR, hP⟩

/-- **A later state of a lane with an event of the MMA code after the election** is an MMA
state after the election with the reference invariant at the lane's prefix counts (in an
execution without undefined behaviour). -/
theorem post_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {j i : Nat} {e0 : Event}
    (he0 : X.get (g, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr : 1853 < e0.pc ∧ e0.pc < 2162) (hji : j ≤ i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n) ∧
      Mma.Ref L g d (fun c => ((X.tr g).take i).countP (Mma.cls c)) ∧ Mma.Post d.site :=
  post_core hp hX hFw he0 hu0 hr hji hσ ((state_count hσ .ub).trans
    (List.countP_eq_zero.mpr fun f hf hcl => hnu (by
      obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
      obtain ⟨pc, kd⟩ := f
      cases kd <;> simp [cls] at hcl
      exact ⟨(g, j), pc, _, hj⟩)))

/-- **A later event of a lane in the MMA code after the election** is fired from an MMA state
after the election, with the role's reference invariant at the lane's prefix counts. -/
theorem post_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j : Nat} {e0 : Event} (he0 : X.get (g, j) = some e0)
    (hu0 : ∀ f, e0.kind ≠ .ub f) (hr : 1853 < e0.pc ∧ e0.pc < 2162) (hjk : j ≤ k)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d, Mma.Ref L g d (fun c => ((X.tr g).take k).countP (Mma.cls c)) ∧ Mma.Ev L g d e ∧
      Mma.Post d.site := by
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, hP⟩ := post_core hp hX hFw he0 hu0 hr hjk hσ (state_ub hX hσ he)
  exact ⟨d, hR, hev, hP⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
