-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
public import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Glue
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
public import Kernels.TmlFa4Fwd.Proof.Mma.Startup
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Kernels.TmlFa4Fwd.Proof.Softmax.RefCases
public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Lemmas.Flow.NotRegister
public import Lemmas.Kernel.Safety.Schedule
public import Lemmas.Kernel.Source.WarpColl
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # ERR-SETMAXNREG: one request per thread, the warpgroup's

`noRegister`: no `setmaxnreg` request is unsafe, by `noSetMaxNReg_of_first`.

* **Where a request is fired.** Every thread is followed with its role's reference invariant (the
  softmax warps by `SmWarp.good`, warps 8 to 15 by `good_all`), so a request is fired from a
  role's state; the role's shape table admits a request only at its entry site (the
  `setmaxnreg` of the role, `IsEntry`), and the startup fires none.
* **Which request.** The entry site's instruction is the role's `setmaxnreg` (`fires_setMaxReg_op`):
  `inc 184` for the softmax warps (pc 3102), `dec 64` for the correction warps (pc 7746), `dec 80`
  for the MMA, output and loader warps (pcs 1907, 2769, 179). The role is the warp's, so the
  request is `req w` of the warp index `w`, which is constant on a warpgroup (four warps).
* **Only one.** No role's machine moves to its entry site (`next_not_entry`: the softmax and
  correction machines by their listed successors, the output and loader machines by unfolding
  their successor, the MMA warp's startup by its own successor), and a role's state is followed
  by role states of the same role, so before a request the thread's states are the startup's,
  which fire no request: every request is the thread's first. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### No role machine moves to its entry -/

theorem Softmax.setmax_nmem_all : [false, true].all (fun lz => Softmax.allSites.all fun s =>
    !(Softmax.nexts lz s).contains .setmax) = true := by decide +kernel

theorem Softmax.succ_ne_setmax {d d' : Softmax.D} {e : Event}
    (h : Softmax.succ p L g d e = some (some d')) : d'.site ≠ .setmax := by
  by_cases hs : d.site = .setmax
  · obtain ⟨s, v, k, acc⟩ := d
    simp only at hs
    subst hs
    simp only [Softmax.succ, Option.some.injEq] at h
    subst h
    simp
  rcases Softmax.succ_cases h with ⟨h1, -⟩ | ⟨hm, -⟩
  · rw [h1]; exact hs
  · intro h2
    rw [h2] at hm
    have := List.all_eq_true.mp (List.all_eq_true.mp Softmax.setmax_nmem_all (Softmax.lz L g)
      (by cases Softmax.lz L g <;> simp)) d.site (Softmax.mem_allSites _)
    simp [hm] at this

section Corr
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
set_option maxHeartbeats 4000000 in
theorem Correction.succ_ne_setmax {d d' : Correction.D} {e : Event}
    (h : Correction.succ p L g d e = some (some d')) : d'.site ≠ .setmax := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only [succ, word32, real32, scale32, max32, scAt, D.mk', D.ite, afterTotal, loopHead,
    scanExit, passStart, afterTiles, enterRounds, roundEnd, afterVote, afterFinal, afterLse] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; simp; done)
    | (simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h; simp)
         | (subst h; simp))

end Corr

section Epi
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem Epilogue.succ_ne_start {d d' : Epilogue.D} {e : Event}
    (h : Epilogue.succ p L g d e = some (some d')) : d'.site ≠ .start := by
  obtain ⟨pc, kind⟩ := e
  simp only [succ] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; simp; done)
    | (subst h; simp; done)
    | ((try simp only [word32, afterTiles, afterTotal, loopHead, scanExit] at h)
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq, Option.map_some, Option.map_none, reduceCtorEq] at h
            subst h; simp; done)
         | (subst h; simp; done)
         | (simp only [Option.some.injEq] at h; subst h; simp_all; done)
         | (simp only [Option.some.injEq] at h; subst h; simp only [storeNext]; split <;> simp))

end Epi

section Ld
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem Loader.succ_ne_setmax {w : Nat} {d d' : Loader.D} {e : Event}
    (h : Loader.succ p L g w d e = some (some d')) : d'.site ≠ .setmax := by
  obtain ⟨pc, kind⟩ := e
  simp only [succ] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; simp; done)
    | (subst h; simp; done)
    | ((try simp only [word32, afterTiles, afterTotal, loopHead, scanExit, passStart, pgEnter,
          pkStart, afterArrive, groupEnd, teNext, teElected, dwNext] at h)
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq, Option.map_some, Option.map_none, reduceCtorEq] at h
            subst h; simp; done)
         | (subst h; simp; done)
         | (simp only [Option.some.injEq] at h; subst h; simp_all; done)
         | (simp only [Option.some.injEq] at h; subst h
            simp only [D.ite, D.iteS, D.mk', scAt, afterPrime, warmEnd, steadyEnd, afterTail,
              afterWarm, passStart, pgEnter, pkStart, groupEnd, teNext, teElected, dwNext,
              afterTotal, loopHead, scanExit]
            split_ifs <;> simp; done)
         | (simp only [Option.map_some, Option.some.injEq] at h; subst h
            simp only [D.ite, D.mk']; split_ifs <;> simp; done))

end Ld

/-! ### Entries -/

/-- A role's state at its `setmaxnreg`. -/
def IsEntry : (i : Role) → (frag p L g i).D → Prop
  | .epilogue, d => d.site = .start
  | .mma, d => d = .inl .set
  | .correction, d => d.site = .setmax
  | .loader _, d => d.site = .setmax
  | .softmax, d => d.site = .setmax
  | .stub _, _ => True

private theorem corr_no_entry {d d' : Correction.Control.D} {e : Event}
    (h : Correction.Control.succ p L g d e = some (some d')) : d'.site ≠ .setmax := by
  have base (hm : (Correction.succ p L g d.scheduler e).map (Option.map Correction.Control.erase)
      = some (some d')) : d'.site ≠ .setmax := by
    obtain ⟨o, hs, ho⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨v, rfl, hv⟩ := Option.map_eq_some_iff.mp ho
    subst d'
    exact Correction.succ_ne_setmax hs
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rscale st | fsum st | fmax st | rld st c | fld st j =>
    simp only [Correction.Control.succ] at h
    split at h <;> cases h
    all_goals exact nofun
  | fdone st j =>
    fin_cases st <;> fin_cases j
    all_goals first | exact base h | skip
    cases h
    simp only [Correction.afterFinal, Correction.passStart, Correction.D.ite]
    repeat' split
    all_goals exact nofun
  | lse j =>
    fin_cases j
    · cases h
      simp only [Correction.afterLse, Correction.passStart, Correction.D.ite]
      repeat' split
      all_goals exact nofun
    · exact base h
  | _ => exact base h

private theorem soft_no_entry {d d' : Softmax.Control.D} {e : Event}
    (h : Softmax.Control.succ p L g d e = some (some d')) : d'.site ≠ .setmax := by
  have base (hm : (Softmax.succ p L g d.scheduler e).map (Option.map Softmax.Control.erase)
      = some (some d')) : d'.site ≠ .setmax := by
    obtain ⟨o, hs, ho⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨v, rfl, hv⟩ := Option.map_eq_some_iff.mp ho
    subst d'
    exact Softmax.succ_ne_setmax hs
  obtain ⟨s,v,k,acc⟩ := d
  cases s with
  | sld r c =>
    simp only [Softmax.Control.succ] at h
    split at h
    · cases r <;> simp only [Softmax.afterLoads] at h <;> (repeat' split at h)
      all_goals cases h <;> exact nofun
    · cases h
  | bld b c =>
    simp only [Softmax.Control.succ] at h
    repeat' split at h
    all_goals cases h
    all_goals exact nofun
  | _ => exact base h

/-- **No role machine moves to its entry.** -/
theorem next_not_entry {i : Role} {d d' : (frag p L g i).D} {e : Event}
    (h : (frag p L g i).next d e = some (some d')) : ¬ IsEntry i d' := by
  cases i with
  | epilogue => exact Epilogue.succ_ne_start h
  | correction => exact corr_no_entry h
  | loader b => exact Loader.succ_ne_setmax h
  | softmax => exact soft_no_entry h
  | stub r => simp [frag, stop] at h
  | mma =>
    show ¬ d' = .inl .set
    rcases d with s | ⟨⟨⟩, d⟩
    · cases s <;> simp [frag, Mma.M, Mma.G, Code.glue, Mma.S, Code.enter, Mma.Start.exit] at h <;>
        first
          | (subst h; simp; done)
          | (subst h; split <;> simp <;> split <;> simp)
    · simp only [frag, Mma.M, Mma.G, Code.glue] at h
      cases hn : Mma.succ p L g d e with
      | none => simp [hn] at h
      | some o => cases o <;> simp [hn] at h <;> (subst h; simp)

/-- A role state's successor in the thread machine is its role machine's. -/
theorem next_role {i : Role} {d : (frag p L g i).D} {n : Cls → Nat} {e : Event} :
    (thread p L g).next (.inr ⟨i, d⟩, n) e = ((frag p L g i).next d e).map
      (Option.map fun d' => (.inr ⟨i, d'⟩, Code.bump (cls L g) n e)) := by
  show ((((frag p L g i).next d e).map (Option.map fun d' =>
    (Sum.inr ⟨i, d'⟩ : (glued p L g).D))).map
        (Option.map fun d' => (d', Code.bump (cls L g) n e))) = _
  rcases (frag p L g i).next d e with _ | _ | d' <;> rfl

/-- **After a role state, every state is a role state that is no entry.** -/
theorem no_reentry {j : Nat} {i : Role} {d : (frag p L g i).D} {n : Cls → Nat}
    (hj : Frame.stateAt (thread p L) X g j = some (some (.inr ⟨i, d⟩, n))) :
    ∀ k, j < k → k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      ∃ i' d' n', σ = (.inr ⟨i', d'⟩, n') ∧ ¬ IsEntry i' d' := by
  intro k hk hkl
  induction k with
  | zero => omega
  | succ k ih =>
    intro σ hσ
    have hlen : k < (X.tr g).length := by omega
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
      rw [Frame.stateAt_succ he] at hσ
      have hprev : ∃ i0 d0 n0, Frame.stateAt (thread p L) X g k =
          some (some (.inr ⟨i0, d0⟩, n0)) := by
        by_cases hkj : k = j
        · subst hkj; exact ⟨i, d, n, hj⟩
        · cases hk' : Frame.stateAt (thread p L) X g k with
          | none => rw [hk'] at hσ; simp at hσ
          | some o =>
            cases o with
            | none => rw [hk'] at hσ; simp [Machine.after] at hσ; exact absurd hσ (by
                simp [Code.toMachine])
            | some σ0 =>
              obtain ⟨i0, d0, n0, rfl, -⟩ := ih (by omega) (by omega) σ0 hk'
              exact ⟨i0, d0, n0, rfl⟩
      obtain ⟨i0, d0, n0, hk0⟩ := hprev
      rw [hk0] at hσ
      simp only [Option.bind_some] at hσ
      change (thread p L g).next (.inr ⟨i0, d0⟩, n0) e = some (some σ) at hσ
      rw [next_role] at hσ
      cases hn : (frag p L g i0).next d0 e with
      | none => rw [hn] at hσ; simp at hσ
      | some o =>
        cases o with
        | none => rw [hn] at hσ; simp at hσ
        | some d1 =>
          rw [hn] at hσ
          simp only [Option.map_some, Option.some.injEq] at hσ
          exact ⟨i0, d1, _, hσ.symm, next_not_entry hn⟩

/-- A table entry that admits no request. -/
macro "no_req" : tactic => `(tactic| (
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  first
    | rfl
    | (split at hev <;> simp_all <;> done)
    | skip))

set_option maxHeartbeats 4000000 in
/-- **A request is fired at an entry of its role.** -/
theorem req_entry (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {e : Event} {i : Role}
    {d : (frag p L g i).D} {n : Cls → Nat} {inc : Bool} {nn inst : Nat}
    (he : X.get (g, k) = some e) (hk : e.kind = .setMaxReg inc nn inst)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inr ⟨i, d⟩, n))) : IsEntry i d := by
  have hu : ∀ f, e.kind ≠ .ub f := by rw [hk]; intro f h; cases h
  cases i with
  | stub r => trivial
  | epilogue =>
    have hev := (Epilogue.fired hp hX he hσ).1
    show d.site = .start
    unfold Epilogue.Ev at hev
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    split at hev <;> simp_all [Epilogue.Ev, Epilogue.isStore, Correction.rdOrUb,
      Correction.Site.toE, Loader.Site.toE,
      Softmax.Site.toE, Mma.Site.toE, Softmax.rdOrUb, Softmax.tcLdOrUb]
  | correction =>
    have hev := (CorrWarp.fired_both hp hX he hσ hu).1
    show d.site = .setmax
    obtain ⟨site, v, k⟩ := d
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    cases site <;> simp_all [Correction.Control.Ev, Correction.Control.D.scheduler, Correction.Ev,
        Epilogue.Ev, Epilogue.isStore, Correction.rdOrUb,
      Correction.Site.toE, Loader.Site.toE,
      Softmax.Site.toE, Mma.Site.toE, Softmax.rdOrUb, Softmax.tcLdOrUb]
  | loader b =>
    have hev := (LdWarp.lfired hp hX he hσ).1
    show d.site = .setmax
    unfold Loader.Ev at hev
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    split at hev <;> simp_all [Epilogue.Ev, Epilogue.isStore, Correction.rdOrUb,
      Correction.Site.toE, Loader.Site.toE,
      Softmax.Site.toE, Mma.Site.toE, Softmax.rdOrUb, Softmax.tcLdOrUb]
  | softmax =>
    have hev := (SmWarp.fired_soft hp hX he hσ hu).1.1
    change d.scheduler.site = .setmax
    unfold Softmax.Ev at hev
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    split at hev <;> simp_all [Epilogue.Ev, Epilogue.isStore, Correction.rdOrUb,
      Correction.Site.toE, Loader.Site.toE,
      Softmax.Site.toE, Mma.Site.toE, Softmax.rdOrUb, Softmax.tcLdOrUb]
  | mma =>
    show d = .inl .set
    rcases d with s | ⟨⟨⟩, d⟩
    · obtain ⟨t, ins, o, -, hinv, hc, hf⟩ :=
        Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hu
      have hop := fires_setMaxReg_op hf hk
      cases s with
      | set => rfl
      | alloc =>
        change kernel.code[1909]? = some ins at hc
        rw [Flow.code_1909, Option.some.injEq] at hc
        rw [← hc] at hop; cases hop
      | wr =>
        change kernel.code[1909]? = some ins at hc
        rw [Flow.code_1909, Option.some.injEq] at hc
        rw [← hc] at hop; cases hop
      | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
    · have hev := (Mma.mfired hp hX he hσ).1
      unfold Mma.Ev at hev
      obtain ⟨pc, kind⟩ := e
      simp only at hk
      subst hk
      exfalso
      split at hev <;> simp_all [Epilogue.Ev, Epilogue.isStore, Correction.rdOrUb,
      Correction.Site.toE, Loader.Site.toE,
      Softmax.Site.toE, Mma.Site.toE, Softmax.rdOrUb, Softmax.tcLdOrUb]

/-! ### Every thread followed -/

/-- **Every lane is followed with its role's reference invariant.** -/
theorem goodR (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (_hFw : Follow p L X) (hg : g < L.threads)
    (k : Nat) : Frame.FollowedAt (thread p L) (JR p L) X g k := by
  have hw16 := Prologue.warpIndex_lt hp g
  by_cases h8 : Prologue.warpIndex L g < 8
  · obtain ⟨h1, h2⟩ := SmWarp.good hp hX h8 hg rfl k
    exact ⟨h1, fun σ hσ => by simpa [JR_eq, h8] using h2 σ hσ⟩
  · obtain ⟨h1, h2⟩ := good_all hp hX hg (by omega) k
    exact ⟨h1, fun σ hσ => by simpa [JR_eq, h8] using h2 σ hσ⟩

/-- The request of a lane of warp `w`: its warpgroup's. -/
def req (w : Nat) : Bool × Nat :=
  if w < 8 then (true, 184) else if w < 12 then (false, 64) else (false, 80)

set_option maxHeartbeats 4000000 in
/-- The role of a lane's role state is its warp's. -/
theorem role_warp {i : Role} {d : (frag p L g i).D} {n : Cls → Nat}
    (hw16 : Prologue.warpIndex L g < 16) (hJ : JR p L g (.inr ⟨i, d⟩, n)) :
    (i = .softmax ∧ Prologue.warpIndex L g < 8) ∨
      (i = .correction ∧ 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g < 12) ∨
      ((i = .mma ∨ i = .epilogue ∨ ∃ b, i = .loader b) ∧ 12 ≤ Prologue.warpIndex L g) := by
  rw [JR_eq] at hJ; unfold RefAll at hJ
  cases i <;> split_ifs at hJ <;>
    first
      | (simp [SmWarp.Ref, Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ; done)
      | omega
      | (right; right; simp; omega)
      | (right; left; simp; omega)
      | (left; simp; omega)

set_option maxHeartbeats 4000000 in
/-- **A request of a lane is its warpgroup's**, fired at its role's entry. -/
theorem req_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k pc : Nat} {inc : Bool}
    {nn inst : Nat} (he : X.get (g, k) = some ⟨pc, .setMaxReg inc nn inst⟩) :
    (inc, nn) = req (Prologue.warpIndex L g) ∧ ∃ i d n,
      Frame.stateAt (thread p L) X g k = some (some (.inr ⟨i, d⟩, n)) ∧ IsEntry i d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, hσ, hJ⟩ := good_state hp hX he (by intro _ _ h; cases h)
    (goodR hp hX hFw hg k)
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX he hσ
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  have hE := req_entry hp hX he rfl hσ
  refine ⟨?_, i, d, n, hσ, hE⟩
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
  have hop := fires_setMaxReg_op hf rfl
  have hrw := role_warp (Prologue.warpIndex_lt hp g) hJ
  cases i with
  | stub r => exfalso; rw [JR_eq] at hJ; unfold RefAll at hJ; split_ifs at hJ <;>
      simp [SmWarp.Ref, Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
  | softmax =>
    change kernel.code[d.site.pc]? = some ins at hc
    simp only [IsEntry] at hE
    rw [hE] at hc
    change kernel.code[3102]? = some ins at hc
    rw [Flow.code_3102, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases hrw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> simp at h1 <;>
      (unfold req; split_ifs <;> first | rfl | omega)
  | correction =>
    change kernel.code[d.site.pc]? = some ins at hc
    simp only [IsEntry] at hE
    rw [hE] at hc
    change kernel.code[7746]? = some ins at hc
    rw [Flow.code_7746, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases hrw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> simp at h1 <;>
      (unfold req; split_ifs <;> first | rfl | omega)
  | epilogue =>
    change kernel.code[d.site.pc]? = some ins at hc
    simp only [IsEntry] at hE
    rw [hE] at hc
    change kernel.code[2769]? = some ins at hc
    rw [Flow.code_2769, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases hrw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> simp at h1 <;>
      (unfold req; split_ifs <;> first | rfl | omega)
  | loader b =>
    change kernel.code[d.site.pc]? = some ins at hc
    simp only [IsEntry] at hE
    rw [hE] at hc
    change kernel.code[179]? = some ins at hc
    rw [Flow.code_179, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases hrw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> simp at h1 <;>
      (unfold req; split_ifs <;> first | rfl | omega)
  | mma =>
    simp only [IsEntry] at hE
    subst hE
    change kernel.code[1907]? = some ins at hc
    rw [Flow.code_1907, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rcases hrw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> simp at h1 <;>
      (unfold req; split_ifs <;> first | rfl | omega)

/-- **ERR-SETMAXNREG**: every request is its thread's first and its warpgroup's. -/
theorem noRegister (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    ¬ SetMaxNReg.UnsafeAt Assumptions.all L X := by
  refine Frame.noSetMaxNReg_of_first ⟨by rw [hp.block]; decide, by rw [hp.block]⟩
    (fun g => req (Prologue.warpIndex L g))
    (fun g k pc inc n inst he => (req_at hp hX hFw he).1)
    (fun g h hs => ?_) (fun ⟨g, k⟩ pc inc n inst hr => ?_)
  · obtain ⟨-, hgrp⟩ := hs
    simp only [Prologue.warpIndex] at hgrp ⊢
    unfold req
    split_ifs <;> first | rfl | omega
  · obtain ⟨-, i, d, n0, hσ, hE⟩ := req_at hp hX hFw hr
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hr).1
    simp only [SetMaxNReg.ordinal]
    rw [List.countP_eq_zero]
    intro x hx hreq
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
    simp only [List.length_take] at hj
    have hjx : X.get (g, j) = some x := by
      show (X.tr g)[j]? = some x
      rw [← hxj, List.getElem_take]
      exact List.getElem?_eq_getElem (by omega)
    obtain ⟨pcx, kx⟩ := x
    cases kx <;> simp [SetMaxNReg.isRequest] at hreq
    obtain ⟨-, i', d', n', hσ', -⟩ := req_at hp hX hFw hjx
    obtain ⟨i'', d'', n'', heq, hne⟩ := no_reentry hσ' k (by omega) (by omega) _ hσ
    simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
    obtain ⟨⟨rfl, hd⟩, -⟩ := heq
    exact hne hE

end
end PTX.Kernels.TmlFa4Fwd.Proof
