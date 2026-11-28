-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollGen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Coll
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollStart
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefNext

@[expose] public section

/-! # The startup's collectives in the pc count

At a startup state the count `ncT` is the startup's own `ncS` (`startup_nc`), and a startup step
keeps it (`startup_nc_step`), also the step that leaves the startup into the warpgroup of the
launch (`ncW_entry`: the entry's first pc is past no collective the barrier's was not). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The pc of a startup state is its site's. -/
theorem pc_startup (d : Startup.D) (n : Cls → Nat) :
    (thread P L x).pc (.inl d, n) = d.site.pc := rfl

/-- **At a startup state the pc count is the startup's.** -/
theorem startup_nc (hp : Pre P L m) {d : Startup.D} {n : Cls → Nat}
    (hW : Startup.RefW L x d (n .shfl)) (hx : Startup.exitOf d = none) :
    ncT P L x (.inl d, n) = Startup.ncS d := by
  have hw := Startup.warpW_ne (g := x) hp
  obtain ⟨site, x1, x2⟩ := d
  unfold ncT
  rw [pc_startup]
  cases site with
  | sh j => fin_cases j <;> simp [Startup.ncS, Startup.Site.pc, ncW_six, ncW_nine]
  | enter q => simp [Startup.exitOf] at hx
  | bar =>
    obtain ⟨-, -, h2⟩ := hW
    simp only at h2
    simp only [Startup.ncS, Startup.notWarp0, Startup.Site.pc, h2, hw, ncW_ninetyseven]
    by_cases h0 : warpOf L x = 0 <;> simp [h0]
  | elect j =>
    obtain ⟨-, -, -, h0⟩ := hW
    rw [h0]
    fin_cases j <;> simp [Startup.ncS, Startup.Site.pc] <;> decide
  | init n =>
    obtain ⟨-, -, h2, h0⟩ := hW
    have hn0 : Startup.notWarp0 x2 = false := by
      simp only at h2; simp [Startup.notWarp0, h2, hw, h0]
    rw [Startup.ncS_other (d := ⟨.init n, x1, x2⟩) (by simp) (by simp)]
    simp only [hn0, Bool.false_eq_true, ite_false, Startup.Site.pc, h0]
    refine ncW_zero_mid ?_ ?_ <;> (fin_cases n <;> decide)
  | _ =>
    all_goals
      obtain ⟨-, -, h2, h0⟩ := hW
      have hn0 : Startup.notWarp0 x2 = false := by
        simp only at h2; simp [Startup.notWarp0, h2, hw, h0]
      rw [Startup.ncS_other (by simp) (by simp)]
      simp only [hn0, Bool.false_eq_true, ite_false, Startup.Site.pc, h0]
      apply ncW_zero_mid <;> decide

theorem frag_init_pc (i : Entry) :
    (frag P L x i).pc (frag P L x i).init = Entry.pc i := by
  cases i <;> rfl

theorem entry_pc_eq (hp : Pre P L m) :
    Entry.pc (entryOfWg L x) = if warpOf L x < 4 then 103 else if warpOf L x < 8 then 1842
      else 2606 := by
  have h3 := wgOf_lt (g := x) hp
  have hw : warpOf L x / 4 = wgOf L x := by simp only [wgOf, warpOf]; omega
  rcases (by omega : wgOf L x = 0 ∨ wgOf L x = 1 ∨ wgOf L x = 2) with h | h | h
  · simp [entryOfWg, h, Entry.pc]
    split_ifs <;> omega
  · simp [entryOfWg, h, Entry.pc]
    split_ifs <;> omega
  · simp [entryOfWg, h, Entry.pc]
    split_ifs <;> omega

/-- The state after a step from a startup state that leaves it is at its warpgroup's entry. -/
theorem enter_pc (hp : Pre P L m) {d d' : Startup.D} {n n' : Cls → Nat}
    (hW : Startup.RefW L x d (n .shfl)) (hb : d.site = .bar) (hd : d' = Startup.enterOf d) :
    (thread P L x).pc (Code.enter (startupCode P L x) (Code.withStubs (frag P L x) Entry.pc)
      (Code.gatedExit (startupEnter P L x) (sel P L x)) d', n') = Entry.pc (entryOfWg L x) := by
  obtain ⟨site, x1, x2⟩ := d
  simp only at hb
  subst hb
  obtain ⟨-, h1, h2⟩ := hW
  simp only at h1 h2
  have hx1 : (Startup.enterOf (⟨.bar, x1, x2⟩ : Startup.D)).x1 = x1 := by
    unfold Startup.enterOf; split_ifs <;> rfl
  have hx2 := Startup.enterOf_x2 (⟨.bar, x1, x2⟩ : Startup.D)
  have hent := enter_wg (P := P) (L := L) (g := x) hp (d := ⟨.bar, x1, x2⟩) h1
  subst hd
  have hsel : sel P L x (entryOfWg L x) (Startup.enterOf (⟨.bar, x1, x2⟩ : Startup.D)) =
      some (entryOfWg L x) := by
    unfold sel
    split_ifs with hh
    · rfl
    · exact absurd ⟨by rw [hx1, h1], by rw [hx2]; exact h2⟩ hh
  simp only [Code.enter, Code.gatedExit, hent, Option.map_some, hsel]
  exact frag_init_pc (P := P) (L := L) (x := x) _

/-- **A startup step keeps the pc count**, also the one into the warpgroup. -/
theorem startup_nc_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) {k : Nat}
    {d : Startup.D} {n : Cls → Nat} {e : Event} {σ' : (thread P L x).D}
    (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (.inl d, n)))
    (hn : (thread P L x).next (.inl d, n) e = some (some σ')) :
    ncT P L x σ' = ncT P L x (.inl d, n) +
      if (thread P L x).pc (.inl d, n) ∈ collPcs then 1 else 0 := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨σ0, hσ0, hJ, hi, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  have hxd : Startup.exitOf d = none := by simpa [Code.gatedExit, startupEnter] using hi.2
  obtain ⟨-, hW, -⟩ := id hJ
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hne
  have hc := coll_iff_pc hX he hne
  rw [next_startup] at hn
  cases hs : Startup.succ L x d e with
  | none => rw [hs] at hn; cases hn
  | some o =>
    cases o with
    | none => rw [hs] at hn; cases hn
    | some d' =>
      rw [hs] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      have hst := Startup.ncS_step hev hne (fun j hj => startup_warp0 hJ hj) hs
      have hcol : (if Sched.isWarpColl e = true then 1 else 0) =
          if (thread P L x).pc (.inl d, n) ∈ collPcs then 1 else 0 := by
        by_cases h : Sched.isWarpColl e = true
        · simp [h, hpc ▸ hc.mp h]
        · have : (thread P L x).pc (.inl d, n) ∉ collPcs := fun h' => h (hc.mpr (hpc ▸ h'))
          simp [h, this]
      by_cases hx' : Startup.exitOf d' = none
      · rw [← hcol, startup_nc hp hW hxd, ← hst]
        have hg : Code.gatedExit (startupEnter P L x) (sel P L x) d' = none :=
          Code.gatedExit_none.mpr (by simpa [startupEnter] using hx')
        simp only [Code.enter, hg]
        have hst1 : Frame.stateAt (thread P L) X x (k + 1) =
            some (some (.inl d', Code.bump cls n e)) := by
          rw [Frame.stateAt_succ (C := thread P L) (show (X.tr x)[k]? = some e from he), hσ]
          show (thread P L x).next _ e = _
          rw [next_startup, hs]
          simp [Code.enter, hg]
        have hJ' := (follow_iff.mp hFw x hx (k + 1)).2 _ hst1
        obtain ⟨-, hW', -⟩ := hJ'
        exact startup_nc hp hW' hx'
      · obtain ⟨hb, hd'⟩ := succ_enter hs hx'
        have h97 : (thread P L x).pc (.inl d, n) = 97 := by rw [pc_startup, hb]; rfl
        have hno : (97 : Nat) ∉ collPcs := by decide
        unfold ncT
        rw [enter_pc hp hW hb hd', entry_pc_eq hp, h97]
        simp only [hno, ite_false, Nat.add_zero]
        exact (ncW_entry _ (warpOf_lt hp)).symm

theorem entryPc_notColl (r : Entry) : Entry.pc r ∉ collPcs := by
  cases r <;> decide

/-- **After a blocking event of the startup** the machine runs on, at no collective. -/
theorem startup_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) {k : Nat}
    {d : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some (.inl d, n)))
    (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next (.inl d, n) e ≠ none ∧ ∀ σ', (thread P L x).next (.inl d, n) e =
      some (some σ') → (thread P L x).pc σ' ∉ collPcs := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  obtain ⟨σ0, hσ0, hJ, hi, hev⟩ := ev_state hp hX hFw he hne
  rw [hσ] at hσ0
  obtain rfl := Option.some.inj (Option.some.inj hσ0)
  obtain ⟨-, hW, -⟩ := id hJ
  obtain ⟨site, x1, x2⟩ := d
  have hev' : Startup.Ev L x ⟨site, x1, x2⟩ e := hev
  have hgate : ∀ d' : Startup.D, Startup.exitOf d' = none → Code.enter (startupCode P L x)
      (Code.withStubs (frag P L x) Entry.pc) (Code.gatedExit (startupEnter P L x) (sel P L x)) d'
        = .inl d' := fun d' hx' => by
    have hg : Code.gatedExit (startupEnter P L x) (sel P L x) d' = none :=
      Code.gatedExit_none.mpr (by simpa [startupEnter] using hx')
    simp only [Code.enter, hg]
  cases site with
  | alloc =>
    refine ⟨by rw [next_startup]; simp [Startup.succ], fun σ' hσ' => ?_⟩
    rw [next_startup] at hσ'
    simp only [Startup.succ] at hσ'
    split_ifs at hσ' <;>
      (simp only [Option.map_some, Option.some.injEq] at hσ'; subst hσ';
       rw [hgate _ (by simp [Startup.exitOf])]; simp only [Startup.Site.pc]; decide)
  | relinq =>
    refine ⟨by rw [next_startup]; simp [Startup.succ], fun σ' hσ' => ?_⟩
    rw [next_startup] at hσ'
    simp only [Startup.succ, Option.map_some, Option.some.injEq] at hσ'
    subst hσ'
    rw [hgate _ (by simp [Startup.exitOf])]; simp only [Startup.Site.pc]; decide
  | bar =>
    refine ⟨by rw [next_startup]; simp [Startup.succ], fun σ' hσ' => ?_⟩
    rw [next_startup] at hσ'
    simp only [Startup.succ, Option.map_some, Option.some.injEq] at hσ'
    subst hσ'
    rw [enter_pc hp hW rfl rfl]
    exact entryPc_notColl _
  | sh j =>
    exfalso
    fin_cases j <;> (obtain ⟨r, ok, hk⟩ := hev'; rw [hk] at hb; simp [Sched.Unblocking] at hb)
  | elect j =>
    exfalso
    obtain ⟨inst, ld, -, hk⟩ := hev'
    rw [hk] at hb; simp [Sched.Unblocking] at hb
  | init n => exfalso; rw [hev'] at hb; simp [Sched.Unblocking] at hb
  | fence => exfalso; rw [hev'] at hb; simp [Sched.Unblocking] at hb
  | allocSt =>
    exfalso
    obtain ⟨col, -, hk⟩ := hev'
    rw [hk] at hb; simp [Sched.Unblocking] at hb
  | ld =>
    exfalso
    rcases hev' with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩ <;> rw [hk] at hb <;> simp [Sched.Unblocking] at hb
  | trap => exfalso; rw [hev'] at hb; simp [Sched.Unblocking] at hb
  | enter q =>
    exfalso
    have := hi.2
    simp [Code.gatedExit, startupEnter, Startup.exitOf] at this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
