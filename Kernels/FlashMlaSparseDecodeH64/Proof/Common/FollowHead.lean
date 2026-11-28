-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext

@[expose] public section

/-! # The following, step by step: warpgroup 1's head and its hand-offs

`head_good`: a step of warpgroup 1's head (the `setmaxnreg` at pc 1842, the shuffle at pc 1843)
keeps `JF`: the head's invariant by `Wg1.hrefNext` (its shuffle returned the launch's warp word,
`hrecv`, from `head_recv`), and at an exit the sub-role the gate passes (`subSel_pass`) starts at
its first state with its invariant at zero role counts (`Mma`/`Tma`/`Index` first states). An
undefined behaviour at the `setmaxnreg` moves the head to its shuffle with its invariant (it
counts no shuffle) and voids `fresh`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The MMA warp's first state has its invariant with no event counted. -/
theorem mma_ref0 : Mma.Ref L g Mma.init fun _ => 0 := fun _ =>
  (Mma.core_pro (d := Mma.init) ⟨rfl, nofun, nofun⟩).2 fun c _ => by
    cases c <;> simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.init, Mma.Site.pro, Mma.useAt,
      ringUses, Mma.mmaIn]

theorem next_head (s : Wg1.Site) (n : Cls → Nat) (e : Event) :
    (thread P L g).next (.inr ⟨.inl .wg1, .inl s⟩, n) e =
      (Wg1.succ s e).map (Option.map fun s' =>
        (.inr ⟨.inl .wg1, Code.enter (wg1HeadCode P L g)
          (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
          (Code.gatedExit (wg1Enter P L g) (subSel P L g)) s'⟩, Code.bump cls n e)) := by
  rw [next_frag]
  rcases h : Wg1.succ s e with _ | _ | s' <;>
    simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, wg1HeadCode, Wg1.code, h]

/-- The first state of the sub-role an exit passes to has the invariant. -/
theorem sub_init (hp : Pre P L m) {s : Wg1.Site} {r : SubEntry} {n : Cls → Nat}
    (hR : Wg1.HRef L g s (n .shfl))
    (hx : wg1Enter P L g s = some r) (hz : n .ub = 0 → RoleZero n) (hb : 1 ≤ n .bar0)
    (hwg : wgOf L g = 1) :
    JF P L g (.inr ⟨.inl .wg1, .inr ⟨.inl r, (subFrag P L g r).init⟩⟩, n) := by
  have hsel := subSel_pass (P := P) hR hx
  simp only [subSel] at hsel
  split_ifs at hsel with hok
  cases s <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
    Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> obtain ⟨h3, -⟩ := hR
  · exact ⟨⟨hb, ⟨h3, hok, ⟨fun hu => by rw [(hz hu).1]; exact mma_ref0, Mma.siteOk_init⟩,
      fun _ h => by cases h⟩, by omega, hwg⟩, by simp [fresh, subBack, Mma.init]⟩
  · exact ⟨⟨hb, ⟨h3, hok, ⟨fun hu => by rw [(hz hu).2.1]; exact Tma.ref_init, Tma.siteOk_init⟩,
      fun _ h => by cases h⟩, by omega, hwg⟩, by simp [fresh, subBack, Tma.init]⟩
  · exact ⟨⟨hb, ⟨h3, hok, fun hu => by rw [(hz hu).2.2.1]; exact Index.ref_init hp⟩, by omega,
      hwg⟩, rfl⟩
  · exact ⟨⟨hb, ⟨h3, hok⟩, by omega, hwg⟩, rfl⟩

/-- The counts only grow. -/
theorem bump_ge (n : Cls → Nat) (e : Event) (c : Cls) : n c ≤ Code.bump cls n e c :=
  Nat.le_add_right _ _

/-- **The head steps well**: from a head state with `JF`, on an event that (unless it is undefined
behaviour) has the head's shape at the head's pcs, and whose shuffle returned the launch's warp
word, the machine does not stop and the successor has `JF`. -/
theorem head_good (hp : Pre P L m) {s : Wg1.Site} {n : Cls → Nat} {e : Event}
    (hJ : JF P L g (.inr ⟨.inl .wg1, .inl s⟩, n))
    (hev : (∀ f, e.kind ≠ .ub f) → Wg1.Ev L g s e ∧ (e.pc = 1842 ∨ e.pc = 1843))
    (hrecv : ∀ a r ok, e.kind = .shfl .idx a 0 31 r ok → r = w32 (warpW L g)) :
    Frame.StepGood (thread P L) (JF P L) g (.inr ⟨.inl .wg1, .inl s⟩, n) e := by
  obtain ⟨⟨hb, hR, h2, hwg⟩, hz⟩ := hJ
  change Wg1.HRef L g s (n .shfl) at hR
  change n .ub = 0 → RoleZero n at hz
  have hb' := Nat.le_trans hb (bump_ge n e .bar0)
  have h2' := Nat.le_trans h2 (bump_ge n e .shfl)
  unfold Frame.StepGood
  rw [next_head]
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    have hu1 : Code.bump cls n e .ub = n .ub + 1 := by simp [Code.bump, cls, hf]
    have hs0 : Execution.isShfl e = false := by
      obtain ⟨pc, kd⟩ := e
      simp only at hf
      subst hf
      rfl
    cases s with
    | smr =>
      refine ⟨by simp [Wg1.succ], fun σ' h' => ?_⟩
      simp only [Wg1.succ, Option.map_some, Option.some.injEq] at h'
      subst h'
      rw [Code.enter_none (by simp [Code.gatedExit, wg1Enter, Wg1.exitOf])]
      refine ⟨⟨hb', ?_, h2', hwg⟩, fun h => by omega⟩
      obtain ⟨hsh, hg1⟩ := hR
      exact ⟨by simp [Code.bump, cls, hs0, hsh], hg1⟩
    | hsh => simp [Wg1.succ, hf]
    | _ => simp [Wg1.succ]
  have hu' : ∀ f, e.kind ≠ .ub f := fun f h => hu ⟨f, h⟩
  obtain ⟨hE, hpc⟩ := hev hu'
  have hz' : Code.bump cls n e .ub = 0 → RoleZero (Code.bump cls n e) := fun h0 =>
    (hz (Nat.le_zero.mp (h0 ▸ bump_ge n e .ub))).bump (.inr (by omega))
  rcases hs : Wg1.succ s e with _ | _ | s'
  · simp
  · exfalso
    cases s with
    | smr => simp [Wg1.succ] at hs
    | hsh =>
      obtain ⟨r, ok, hk⟩ := hE
      have hr := hrecv _ r ok hk
      subst hr
      simp only [Wg1.succ, hk, Wg1.dispatch] at hs
      split_ifs at hs <;> cases hs
    | _ => simp [Wg1.succ] at hs
  refine ⟨by simp, fun σ' h' => ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h'
  subst h'
  have hR' : Wg1.HRef L g s' (Code.bump cls n e .shfl) :=
    Wg1.hrefNext hp hR hE hs (fun a r ok hk => hrecv a r ok hk)
  cases hx : wg1Enter P L g s' with
  | none =>
    rw [Code.enter_none (by simp [Code.gatedExit, hx])]
    exact ⟨⟨hb', hR', h2', hwg⟩, hz'⟩
  | some r =>
    have hsel := subSel_pass (P := P) hR' hx
    rw [Code.enter_some (i := .inl r) (by simp [Code.gatedExit, hx, hsel])]
    exact sub_init hp hR' hx hz' hb' hwg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
