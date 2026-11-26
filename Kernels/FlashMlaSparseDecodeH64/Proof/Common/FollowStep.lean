-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Recv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefStepAt
import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The following, step by step: the startup and its hand-offs

The following theorem (`Common/FollowProof.lean`) runs the library's induction
(`Frame.followedOn`) with the role table's invariant and one more fact, `fresh`: before a role
starts, the role classes of the ledger count nothing (`RoleZero`), since every earlier event is
at a pc of the startup (below 103) or of warpgroup 1's head (1842–1852); a sub-role's state is
not a returning one. `JF` is the pair.

This file gives the thread machine's successor at a startup state and at a fragment state
(`next_startup`, `next_frag`), the first states of the warpgroups with their invariants at zero
role counts, and the startup's good step `startup_good`: from a state with the invariant and an
event of its shape whose shuffle returned the launch's word (`hrecv`, `Common/Recv.lean`), the
machine does not stop (the read-back at pc 92 is followed on every value) and the
successor has `JF`: a startup state by `Startup.refNext`, or, after barrier 0, the first state of
the warpgroup the gate passes (`sel_pass`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The extra fact -/

/-- The role classes of the ledger count nothing. -/
def RoleZero (n : Cls → Nat) : Prop :=
  (fun c => n (.mma c)) = (fun _ => 0) ∧ (fun c => n (.tma c)) = (fun _ => 0) ∧
    (fun c => n (.index c)) = (fun _ => 0) ∧ (fun c => n (.dequant c)) = (fun _ => 0) ∧
    (fun c => n (.wg0 c)) = (fun _ => 0)

/-- Before a role starts the role classes count nothing: at the startup, and at warpgroup 1's
head before undefined behaviour; a sub-role's state of the machine does not return to the head
(its return state is the head's, `subBack`). -/
def fresh : (thread P L g).D → Prop
  | (.inl _, n) => RoleZero n
  | (.inr ⟨.inl .wg1, .inl _⟩, n) => n .ub = 0 → RoleZero n
  | (.inr ⟨.inl .wg1, .inr ⟨.inl i, d⟩⟩, _) => subBack P L g i d = none
  | _ => True

/-- **The invariant of the following induction**: the role table's and `fresh`. -/
def JF (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  (table P L).J g σ ∧ fresh σ

/-- An event at a pc of the startup or of warpgroup 1's head counts in no role class. -/
theorem RoleZero.bump {n : Cls → Nat} {e : Event} (h : RoleZero n)
    (hpc : e.pc < 103 ∨ (1842 ≤ e.pc ∧ e.pc ≤ 1852)) : RoleZero (Code.bump cls n e) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have q1 := Mma.cls_of_not_inRole (e := e)
    (by simp only [Mma.inRole, decide_eq_false_iff_not]; omega)
  have q2 := Tma.cls_outside (e := e)
    (by simp only [Tma.inRole, decide_eq_false_iff_not]; omega)
  have q3 := Index.cls_outside (e := e)
    (by simp only [Index.inRole, decide_eq_false_iff_not]; omega)
  have q4 := Dequant.cls_of_not_inRole (e := e)
    (by simp only [Dequant.inRole, decide_eq_false_iff_not]; omega)
  have q5 := Wg0.cls_of_not_inRole (e := e)
    (by simp only [Wg0.inRole, decide_eq_false_iff_not]; omega)
  refine ⟨funext fun c => ?_, funext fun c => ?_, funext fun c => ?_, funext fun c => ?_,
    funext fun c => ?_⟩
  · simp only [Code.bump, cls, q1, congrFun h1 c]; rfl
  · simp only [Code.bump, cls, q2, congrFun h2 c]; rfl
  · simp only [Code.bump, cls, q3, congrFun h3 c]; rfl
  · simp only [Code.bump, cls, q4, congrFun h4 c]; rfl
  · simp only [Code.bump, cls, q5, congrFun h5 c]; rfl

/-! ### The thread machine's successor -/

theorem next_startup (d : Startup.D) (n : Cls → Nat) (e : Event) :
    (thread P L g).next (.inl d, n) e =
      (Startup.succ L g d e).map (Option.map fun d' =>
        (Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
          (Code.gatedExit (startupEnter P L g) (sel P L g)) d', Code.bump cls n e)) := by
  rcases h : Startup.succ L g d e with _ | _ | d' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, startupCode, Startup.code, h]

theorem next_frag (i : Entry) (d : (frag P L g i).D) (n : Cls → Nat) (e : Event) :
    (thread P L g).next (.inr ⟨.inl i, d⟩, n) e =
      ((frag P L g i).next d e).map (Option.map fun d' =>
        (.inr ⟨.inl i, d'⟩, Code.bump cls n e)) := by
  rcases h : (frag P L g i).next d e with _ | _ | d' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, h]

/-- The thread machine's first state is the startup's, with no events counted. -/
theorem thread_init : (thread P L g).init = (.inl (Startup.code L g).init, fun _ => 0) := rfl

/-- **The first state has the invariant.** -/
theorem jf_init : JF P L g (thread P L g).init := by
  rw [thread_init]
  exact ⟨⟨Startup.ref_init.1, Startup.ref_init.2, Startup.refT_init⟩, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The warpgroups' first states -/

theorem wg0_ref0 : Wg0.Ref P L g (Wg0.Control.code P L g (warpW L g)).init (fun _ => 0) := by
  intro _
  simp [Wg0.RefCore, Wg0.RefAt, Wg0.Counts, Wg0.Site.reg, Wg0.acqCnt, Wg0.arrCnt, Wg0.use,
    ringUses, Wg0.ind, Wg0.LaunchOk, Wg0.Site.lens, Wg0.BarOk, Wg0.barTot, Wg0.barOrd,
    Wg0.Site.bidx]

/-- The warpgroup an entry's barrier exit passes to, by the launch's warpgroup. -/
def entryOfWg (L : Launch) (g : Nat) : Entry :=
  if wgOf L g = 1 then .wg1 else if wgOf L g = 2 then .dequant else .wg0

theorem wgOf_lt (hp : Pre P L m) : wgOf L g < 3 := by
  have := tidOf_eq hp g
  have := Nat.mod_lt g (show 0 < 384 by decide)
  unfold wgOf
  omega

/-- The barrier's exit passes to the launch's warpgroup. -/
theorem enter_wg (hp : Pre P L m) {d : Startup.D} (hx1 : d.x1 = wgW L g) :
    startupEnter P L g (Startup.enterOf d) = some (entryOfWg L g) := by
  have h3 := wgOf_lt (g := g) hp
  simp only [startupEnter, Startup.enterOf, hx1, entryOfWg, wgW]
  generalize wgOf L g = w at h3 ⊢
  interval_cases w <;>
    simp (config := { decide := true }) [Startup.exitOf]

/-- **The first state of the launch's warpgroup has the invariant**, after barrier 0 and the
startup's two shuffles, at zero role counts. -/
theorem frag_init (hp : Pre P L m) (n : Cls → Nat) (hz : RoleZero n)
    (hb : 1 ≤ n .bar0) (hs : n .shfl = 2)
    (ht : n .tmem = if PTX.Flow.Arith32.scmpi .ne .b (warpW L g) 0 then 0 else 2) :
    JF P L g (.inr ⟨.inl (entryOfWg L g), (frag P L g (entryOfWg L g)).init⟩, n) := by
  obtain ⟨-, -, -, hd, hw⟩ := id hz
  have h3 := wgOf_lt (g := g) hp
  unfold entryOfWg
  by_cases h1 : wgOf L g = 1
  · rw [ite_eq_left h1]
    exact ⟨⟨hb, ⟨hs, h1⟩, by omega, h1⟩, fun _ => hz⟩
  rw [ite_eq_right h1]
  by_cases h2 : wgOf L g = 2
  · rw [ite_eq_left h2]
    refine ⟨⟨hb, fun _ => ?_, by omega, h2⟩, trivial⟩
    rw [hd]
    exact Dequant.ref_init
  rw [ite_eq_right h2]
  refine ⟨⟨hb, ⟨fun _ => ?_, fun _ => ?_⟩, by omega, by simp only [Entry.wg]; omega⟩, trivial⟩
  · rw [hw]
    exact wg0_ref0
  · simp [Wg0.TmemAt, ht]

/-! ### The startup's step -/

/-- The barrier's exit is an entry state. -/
theorem enterOf_site (d : Startup.D) : ∃ q, (Startup.enterOf d).site = .enter q := by
  unfold Startup.enterOf
  split_ifs <;> exact ⟨_, rfl⟩

theorem word32_some {v : Value} {f : BitVec 64 → Startup.D} {d' : Startup.D}
    (h : Startup.word32 v f = some (some d')) : ∃ x, d' = f x := by
  unfold Startup.word32 at h
  split at h
  · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

theorem afterLd_some {d d' : Startup.D} {v : Value} (h : Startup.afterLd d v = some (some d')) :
    Startup.exitOf d' = none := by
  unfold Startup.afterLd at h
  split at h
  · split_ifs at h <;> (obtain rfl := Option.some.inj (Option.some.inj h); rfl)
  · cases h

/-- Only the barrier's step leaves the startup. -/
theorem succ_enter {d d' : Startup.D} {e : Event} (hs : Startup.succ L g d e = some (some d'))
    (hx : Startup.exitOf d' ≠ none) : d.site = .bar ∧ d' = Startup.enterOf d := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | bar => exact ⟨rfl, (Option.some.inj (Option.some.inj hs)).symm⟩
  | sh j =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · obtain ⟨x, rfl⟩ := word32_some hs
      fin_cases j <;> simp only at hx <;> (try split_ifs at hx) <;> simp [Startup.exitOf] at hx
    · cases hs
  | ld =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · split at hs
      · exact hx (afterLd_some hs)
      · cases hs
    · cases hs
  | elect j =>
    exfalso
    simp only [Startup.succ] at hs
    split at hs
    · fin_cases j <;> simp only at hs <;> (try split_ifs at hs) <;>
        (obtain rfl := Option.some.inj (Option.some.inj hs); simp [Startup.exitOf] at hx)
    · cases hs
  | enter q => simp [Startup.succ] at hs
  | trap => simp [Startup.succ] at hs
  | init k =>
    exfalso
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    simp only [Startup.initSucc] at hx
    split_ifs at hx <;> simp [Startup.exitOf] at hx
  | alloc =>
    exfalso
    simp only [Startup.succ] at hs
    split_ifs at hs <;>
      (obtain rfl := Option.some.inj (Option.some.inj hs); simp [Startup.exitOf] at hx)
  | _ =>
    exfalso
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    simp [Startup.exitOf] at hx

/-- **The startup does not stop** at a state with its invariant, on an event of its shape whose
shuffle returned a word (the read-back is followed on every value: `Startup.afterLd`). -/
theorem startup_live {d : Startup.D} {e : Event} {mi b0 : Nat} (hR : Startup.Ref d mi b0)
    (hev : Startup.Ev L g d e)
    (hrecv : ∀ a r ok, e.kind = .shfl .idx a 0 31 r ok → ∃ x, r = w32 x) :
    Startup.succ L g d e ≠ some none := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> obtain ⟨x, rfl⟩ := hrecv _ r ok hk <;>
      simp [Startup.succ, hk, Startup.word32]
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hev
    fin_cases j <;> simp [Startup.succ, hk]
  | ld =>
    rcases hev with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · simp only [Startup.succ, hk]
      split
      · simp only [Startup.afterLd]
        split
        · split_ifs <;> simp
        · simp
      · simp
    · simp [Startup.succ, hk]
  | enter q => simp [Startup.succ]
  | _ => simp [Startup.succ]

/-- **The startup steps well**: from a state with the invariant and zero role counts, on an event
of its shape at its pc whose shuffle returned the launch's word, the machine does not stop and
the successor has `JF`. -/
theorem startup_good (hp : Pre P L m) {d : Startup.D} {n : Cls → Nat} {e : Event}
    (hJ : startupJ P L g d n) (hz : RoleZero n) (hev : Startup.Ev L g d e) (hpc : e.pc ≤ 97)
    (hrecv : ∀ a r ok, e.kind = .shfl .idx a 0 31 r ok →
      r = w32 (if n .shfl = 0 then wgW L g else warpW L g)) :
    Frame.StepGood (thread P L) (JF P L) g (.inl d, n) e := by
  obtain ⟨hR, hW, hT⟩ := hJ
  have hz' := hz.bump (e := e) (.inl (by omega))
  unfold Frame.StepGood
  rw [next_startup]
  rcases hs : Startup.succ L g d e with _ | _ | d'
  · simp
  · exact absurd hs (startup_live hR hev (fun a r ok hk => ⟨_, hrecv a r ok hk⟩))
  refine ⟨by simp, fun σ' h' => ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h'
  subst h'
  obtain ⟨hR', hW'⟩ := Startup.refNext hp hR hW hev hs hrecv
  have hT' := Startup.refT_next hT hev hs
  have hJ' : startupJ P L g d' (Code.bump cls n e) := ⟨hR', hW', hT'⟩
  cases hx : startupEnter P L g d' with
  | none =>
    rw [Code.enter_none (by simp [Code.gatedExit, hx])]
    exact ⟨hJ', hz'⟩
  | some r =>
    have hsel := sel_pass hJ' hx
    obtain ⟨-, rfl⟩ := succ_enter hs (by
      intro h0
      simp [startupEnter, h0] at hx)
    obtain ⟨q, hq⟩ := enterOf_site d
    have hR2 := hR'
    have hW2 := hW'
    unfold Startup.Ref at hR2
    unfold Startup.RefW at hW2
    rw [hq] at hR2 hW2
    obtain ⟨-, hb⟩ := hR2
    obtain ⟨hsh, hx1, hx2⟩ := hW2
    have hT2 := hT'
    unfold Startup.RefT at hT2
    rw [hq, hx2] at hT2
    have hx1' : d.x1 = wgW L g := by
      rw [← hx1]
      unfold Startup.enterOf
      split_ifs <;> rfl
    have hwg := enter_wg (P := P) hp (d := d) hx1'
    rw [hx, Option.some.injEq] at hwg
    subst hwg
    rw [Code.enter_some (i := .inl (entryOfWg L g)) (by simp [Code.gatedExit, hx, hsel])]
    exact frag_init hp _ hz' (Nat.le_of_eq hb.symm) hsh hT2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
