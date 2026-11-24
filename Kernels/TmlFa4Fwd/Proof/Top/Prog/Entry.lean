-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Register
public import Lemmas.Flow.NotClc
public import Lemmas.Kernel.Progress.Reg
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Kernels.TmlFa4Fwd.Flow.Code.Part048
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.View
import Lemmas.Flow.GlueStep
import Lemmas.Flow.NotRegister
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A role's entry and its register request

Every register request is its thread's first event of its role, at its warp's entry pc (`regMatch`),
and every exit follows one (`regExit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- The code has no cluster-barrier operation. -/
theorem kernel_noCluster : kernel.code.all (fun ins => !Flow.clusterOp ins.op) = true := by
  decide +kernel

/-! ### The register requests of a warp match -/

/-- The pc of the request of warp `w`'s role. -/
def entryPc (w : Nat) : Nat :=
  if w < 8 then 3102 else if w < 12 then 7746 else if w = 12 then 1907
  else if w = 13 then 2769 else 179

set_option maxHeartbeats 4000000 in
/-- **A request is at its warp's role's entry pc.** -/
theorem req_pc (hp : Pre p L m) {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {inc : Bool} {nn inst : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc nn inst⟩) :
    pc = entryPc (Prologue.warpIndex L g) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, i, d, n, hσ, hE⟩ := req_at hp hX (launchFollow hp hX) he
  have hJ := (goodR' hp hX hg k).2 _ hσ
  obtain ⟨t, ins, o, -, -, -, hf⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ
      (by intro f h; cases h)
  have hpc := EventFrame.fires_source_pc hf
  simp only at hpc
  have hw16 := Prologue.warpIndex_lt hp g
  cases i with
  | stub r => exact (JR.not_stub hJ).elim
  | softmax =>
    have hw := (JR.softmax hJ).1
    simp only [IsEntry] at hE
    change pc = d.site.pc at hpc
    rw [hpc, hE]; unfold entryPc; simp only [hw, ↓reduceIte]; rfl
  | correction =>
    obtain ⟨h1, h2, -⟩ := JR.correction hJ hw16
    simp only [IsEntry] at hE
    change pc = d.site.pc at hpc
    rw [hpc, hE]; unfold entryPc
    split_ifs <;> first | rfl | omega
  | epilogue =>
    have hw := (JR.epilogue hJ).1
    simp only [IsEntry] at hE
    change pc = d.site.pc at hpc
    rw [hpc, hE]; unfold entryPc; rw [hw]; rfl
  | loader b =>
    have hw := (JR.loader hJ).1
    simp only [IsEntry] at hE
    change pc = d.site.pc at hpc
    rw [hpc, hE]; unfold entryPc
    rcases hw with hw | hw <;> rw [hw] <;> rfl
  | mma =>
    have hw := (JR.mma hJ).1
    simp only [IsEntry] at hE
    subst hE
    change pc = 1907 at hpc
    rw [hpc]; unfold entryPc; rw [hw]; rfl

/-- **A request is its thread's first.** -/
theorem req_ord (hp : Pre p L m) {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {inc : Bool} {nn inst : Nat}
    (hr : X.get (g, k) = some ⟨pc, .setMaxReg inc nn inst⟩) :
    SetMaxNReg.ordinal X (g, k) = 0 := by
  obtain ⟨-, i, d, n0, hσ, hE⟩ := req_at hp hX (launchFollow hp hX) hr
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
  obtain ⟨-, i', d', n', hσ', -⟩ := req_at hp hX (launchFollow hp hX) hjx
  obtain ⟨i'', d'', n'', heq, hne⟩ := no_reentry hσ' k (by omega) (by omega) _ hσ
  simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
  obtain ⟨⟨rfl, hd⟩, -⟩ := heq
  exact hne hE

/-- **Two register requests of one warp match.** -/
theorem regMatch (hp : Pre p L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : Sched.RegMatch L X := by
  rintro ⟨g, k⟩ ⟨h, j⟩ pc pc' n n' inst inst' inc inc' - - hw he hf
  have hwi : Prologue.warpIndex L g = Prologue.warpIndex L h := hw.2
  have h1 := (req_at hp hX (launchFollow hp hX) he).1
  have h2 := (req_at hp hX (launchFollow hp hX) hf).1
  rw [hwi, ← h2] at h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hp1 := req_pc hp hX he
  have hp2 := req_pc hp hX hf
  rw [hwi, ← hp2] at hp1
  subst hp1
  exact ⟨hw, by rw [req_ord hp hX he, req_ord hp hX hf], pc, inc, n, inst, inst', he, hf⟩

/-! ### Every exit follows a request -/

set_option maxHeartbeats 4000000 in
/-- **An entry state fires a register request.** -/
theorem entry_fires (hp : Pre p L m) {X : Execution} (hX : Consistent L kernel Assumptions.all m X)
    {g k : Nat} {i : Role} {d : (frag p L g i).D} {n : Cls → Nat} {e : Event}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inr ⟨i, d⟩, n))) (hE : IsEntry i d)
    (hJ : JR p L g (.inr ⟨i, d⟩, n)) (he : X.get (g, k) = some e)
    (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ inc nn inst, e.kind = .setMaxReg inc nn inst := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hu
  cases i with
  | stub r => exact (JR.not_stub hJ).elim
  | softmax =>
    simp only [IsEntry] at hE
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hE] at hc
    change kernel.code[3102]? = some ins at hc
    rw [Flow.code_3102, Option.some.injEq] at hc
    subst hc
    obtain ⟨inst, rfl⟩ := Flow.fires_of_setMaxReg_op (by decide) hf
    exact ⟨_, _, _, rfl⟩
  | correction =>
    simp only [IsEntry] at hE
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hE] at hc
    change kernel.code[7746]? = some ins at hc
    rw [Flow.code_7746, Option.some.injEq] at hc
    subst hc
    obtain ⟨inst, rfl⟩ := Flow.fires_of_setMaxReg_op (by decide) hf
    exact ⟨_, _, _, rfl⟩
  | epilogue =>
    simp only [IsEntry] at hE
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hE] at hc
    change kernel.code[2769]? = some ins at hc
    rw [Flow.code_2769, Option.some.injEq] at hc
    subst hc
    obtain ⟨inst, rfl⟩ := Flow.fires_of_setMaxReg_op (by decide) hf
    exact ⟨_, _, _, rfl⟩
  | loader b =>
    simp only [IsEntry] at hE
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hE] at hc
    change kernel.code[179]? = some ins at hc
    rw [Flow.code_179, Option.some.injEq] at hc
    subst hc
    obtain ⟨inst, rfl⟩ := Flow.fires_of_setMaxReg_op (by decide) hf
    exact ⟨_, _, _, rfl⟩
  | mma =>
    simp only [IsEntry] at hE
    subst hE
    change kernel.code[1907]? = some ins at hc
    rw [Flow.code_1907, Option.some.injEq] at hc
    subst hc
    obtain ⟨inst, rfl⟩ := Flow.fires_of_setMaxReg_op (by decide) hf
    exact ⟨_, _, _, rfl⟩

/-- **A role state follows the first state of its role**: an earlier or equal state is a role's
first state. -/
theorem first_role {X : Execution} {g : Nat} :
    ∀ k (r : Σ i, (frag p L g i).D) (n : Cls → Nat),
      Frame.stateAt (thread p L) X g k = some (some (.inr r, n)) →
      ∃ j ≤ k, ∃ i n', Frame.stateAt (thread p L) X g j =
        some (some (.inr ⟨i, (frag p L g i).init⟩, n')) := by
  intro k
  induction k with
  | zero =>
    intro r n h
    rw [Frame.stateAt_zero] at h
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at h
  | succ k ih =>
    intro r n h
    by_cases hk : k < (X.tr g).length
    · have hS := h
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [Frame.stateAt_succ he] at h
      cases h0 : Frame.stateAt (thread p L) X g k with
      | none => rw [h0] at h; simp at h
      | some o =>
        cases o with
        | none => rw [h0] at h; simp [Code.toMachine] at h
        | some σ0 =>
          obtain ⟨s0, n0⟩ := σ0
          rcases s0 with s | r0
          · rw [h0] at h
            change (thread p L g).next (.inl s, n0) e = some (some (.inr r, n)) at h
            obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
            obtain ⟨s', -, hen⟩ := Code.glue_inl_some h1
            unfold Code.enter at hen
            split at hen
            · rename_i i _
              simp only [Sum.inr.injEq] at hen
              subst hen
              exact ⟨k + 1, le_rfl, i, n, hS⟩
            · cases hen
          · obtain ⟨j, hj, i, n', hj'⟩ := ih r0 n0 h0
            exact ⟨j, by omega, i, n', hj'⟩
    · rw [Frame.stateAt_of_le (by omega)] at h
      obtain ⟨j, hj, i, n', hj'⟩ := ih r n (by rw [Frame.stateAt_of_le (by omega)]; exact h)
      exact ⟨j, by omega, i, n', hj'⟩

/-- **Every exit follows a register request.** -/
theorem regExit (hp : Pre p L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : Sched.RegExit L X := by
  intro h k pc hh he
  obtain ⟨σ, hσ, hJ⟩ := good_state hp hX he (by intro _ _ h; cases h) (goodR' hp hX hh k)
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | r
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
  obtain ⟨j, hjk, i, n', hj⟩ := first_role k r n hσ
  have hE : IsEntry i (frag p L h i).init := by cases i <;> first | rfl | trivial
  have hJ' := (goodR' hp hX hh j).2 _ hj
  rcases Nat.lt_or_eq_of_le hjk with hlt | rfl
  · have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨e, hej⟩ : ∃ e, X.get (h, j) = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega : j < (X.tr h).length)⟩
    obtain ⟨inc, nn, inst, hk⟩ := entry_fires hp hX hj hE hJ' hej
      (Frame.noUbBefore_of_get hX he _ hlt _ hej)
    simp only [SetMaxNReg.ordinal]
    refine List.countP_pos_iff.mpr ⟨e, ?_, ?_⟩
    · have : (X.tr h)[j]? = some e := hej
      rw [List.mem_iff_getElem?]
      exact ⟨j, by rw [List.getElem?_take_of_lt hlt]; exact this⟩
    · obtain ⟨pce, ke⟩ := e
      simp only at hk
      subst hk
      rfl
  · rw [hσ] at hj
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at hj
    obtain ⟨rfl, -⟩ := hj
    obtain ⟨inc, nn, inst, hk⟩ := entry_fires hp hX hσ hE hJ he (fun _ => nofun)
    cases hk

end PTX.Kernels.TmlFa4Fwd.Proof.Top
