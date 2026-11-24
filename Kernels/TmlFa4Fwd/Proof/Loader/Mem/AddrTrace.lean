-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Addr
public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Recv

@[expose] public section

/-! # The loader warps' row-address words along the trace

Every role state of a lane of a loader warp keeps the row-address pattern (`AOk`, `ld_aok`), by
induction on the order by the warp collectives with the trace position as the tie-break
(`Frame.inductive_lex`), stated for the state after each event: the role's first state records no
word; a step keeps the pattern (`Loader.succ_aok`), since an address load at sub-step 0 returns a
multiple of 16 (`lw_low`) and a row shuffle receives one from its source lane (`recv_low`), whose
state before its shuffle is the state after an event with fewer collectives up to it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- An event of a thread followed at every position is not bad. -/
theorem not_bad_of_good {J : ∀ g, (thread p L g).D → Prop}
    (hall : ∀ k, Frame.FollowedAt (thread p L) J X g k) (j : Nat) :
    ¬ Frame.Bad (thread p L) J X (g, j) := by
  rintro ⟨d, e, he, hσ, -, hbad⟩
  apply hbad
  have h := hall (j + 1)
  unfold Frame.FollowedAt at h
  rw [Frame.stateAt_succ (show (X.tr g)[j]? = some e from he), hσ] at h
  exact ⟨h.1, fun d' hd' => h.2 d' hd'⟩

/-- The row-address pattern of a state of the thread machine: that of a loader state. -/
def AOkT (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inr ⟨.loader _, d⟩, _) => AOk d.v
  | _ => True

theorem aokT_enter (s : Startup.D) (n : Cls → Nat) :
    AOkT p L g (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s, n) := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> first | trivial | exact ⟨rfl, rfl⟩
  · trivial

set_option maxHeartbeats 4000000 in
/-- **Every state after an event of a lane of loader warp `w` keeps the row-address pattern.** -/
theorem aok_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw14 : w = 14 ∨ w = 15) :
    ∀ i e, X.get i = some e → InWarp L w i.1 → ∀ σ,
      Frame.stateAt (thread p L) X i.1 (i.2 + 1) = some (some σ) → AOkT p L i.1 σ := by
  have hReads := cuQReadsFromLaunch hp hX
  refine Frame.inductive_lex (μ X) (fun i => InWarp L w i.1 → ∀ σ,
      Frame.stateAt (thread p L) X i.1 (i.2 + 1) = some (some σ) → AOkT p L i.1 σ) ?_
  rintro ⟨g, k⟩ e he IH ⟨hg, hw⟩ σ hσ
  simp only at hσ he IH ⊢
  have hall : ∀ k, Good p L w X g k := good hp hX hw14 hg hw
  -- the state before the event
  have hpre : ∀ σ0, Frame.stateAt (thread p L) X g k = some (some σ0) → AOkT p L g σ0 := by
    intro σ0 hσ0
    cases k with
    | zero =>
      rw [Frame.stateAt_zero] at hσ0
      cases hσ0
      trivial
    | succ k' =>
      have hk : k' + 1 < (X.tr g).length :=
        (List.getElem?_eq_some_iff.mp (show (X.tr g)[k' + 1]? = some e from he)).1
      obtain ⟨e', he'⟩ : ∃ e', X.get (g, k') = some e' :=
        ⟨_, List.getElem?_eq_getElem (show k' < (X.tr g).length by omega)⟩
      exact IH (g, k') e' he' (lex_lt (Nat.lt_succ_self _)) ⟨hg, hw⟩ σ0 hσ0
  have hstep := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
  rw [hσ] at hstep
  cases hσ0 : Frame.stateAt (thread p L) X g k with
  | none => rw [hσ0] at hstep; simp at hstep
  | some o =>
    cases o with
    | none => rw [hσ0] at hstep; simp [Code.toMachine] at hstep
    | some σ0 =>
      rw [hσ0] at hstep
      have hn : (thread p L g).next σ0 e = some (some σ) := hstep.symm
      have hI := hpre σ0 hσ0
      have hJ := (hall k).2 σ0 hσ0
      obtain ⟨σ1, n0⟩ := σ0
      rcases σ1 with s | ⟨i, d⟩
      · obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
        obtain ⟨σ', n'⟩ := σ
        obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
        exact aokT_enter s' n'
      cases i with
      | loader b =>
        rw [next_linj] at hn
        cases hs : succ p L g (wOf b) d e with
        | none => simp [Loader.F, code, hs] at hn
        | some o' =>
          cases o' with
          | none => simp [Loader.F, code, hs] at hn
          | some d' =>
            simp only [Loader.F, code, hs, Option.map_some, Option.some.injEq] at hn
            subst hn
            have hub0 : n0 .ub = 0 := ub_zero hX he hσ0
            obtain ⟨hbw, hR⟩ := hJ
            obtain ⟨hJl, hF⟩ := hR hub0
            subst hbw
            have hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L (wOf b)) X (g, j) :=
              fun j _ => not_bad_of_good hall j
            refine succ_aok hI (fun per v hh a bs x hs' hk0 hk hx => ?_)
              (fun per v i md a bb c x o hs' hk => ?_) hs
            · exact lw_low hp hX he hσ0 hJl hnb hs' hk0 hk hx
            · obtain ⟨pc, kind⟩ := e
              simp only at hk
              subst hk
              have hcoll : isColl ⟨pc, .shfl md a bb c (.bits 32 x) o⟩ = true := rfl
              have hup := upTo_of_prev (fun _ => ref_init) he hcoll
                (fun j _ hjw => not_bad_of_good (good hp hX hw14 hjw.1 hjw.2) j.2)
              rw [countColl ((X.tr g).take k), (counts hσ0).1, (counts hσ0).2] at hup
              refine recv_low hp hX hg hw he hσ0 hF hup hs' (fun h j b' d' n' hjw hjl hjc hjs => ?_)
                x rfl
              -- the source's state is the state after an event with fewer collectives
              cases j with
              | zero =>
                rw [Frame.stateAt_zero] at hjs
                cases hjs
              | succ j' =>
                obtain ⟨e', he'⟩ : ∃ e', X.get (h, j') = some e' :=
                  ⟨_, List.getElem?_eq_getElem (show j' < (X.tr h).length by omega)⟩
                have hμ : μ X (h, j') < μ X (g, k) := by
                  have h1 : μ X (h, j') = ((X.tr h).take (j' + 1)).countP isColl := rfl
                  have h2 : μ X (g, k) = ((X.tr g).take k).countP isColl + 1 := by
                    simp only [μ]
                    rw [List.take_add_one, List.countP_append]
                    simp [show (X.tr g)[k]? = _ from he, hcoll]
                  rw [countColl ((X.tr g).take k), (counts hσ0).1, (counts hσ0).2] at h2
                  omega
                exact IH (h, j') e' he' (.inl hμ) hjw _ hjs
      | _ => exact absurd hJ (by simp [Ref])

/-- **A role state of a lane of a loader warp before an event keeps the row-address pattern.** -/
theorem ld_aok (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw14 : w = 14 ∨ w = 15) (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) {b : Bool} {d : D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n))) : AOk d.v := by
  cases k with
  | zero =>
    rw [Frame.stateAt_zero] at hσ
    cases hσ
  | succ k' =>
    have hk : k' + 1 < (X.tr g).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr g)[k' + 1]? = some e from he)).1
    obtain ⟨e', he'⟩ : ∃ e', X.get (g, k') = some e' :=
      ⟨_, List.getElem?_eq_getElem (show k' < (X.tr g).length by omega)⟩
    exact aok_step hp hX hw14 (g, k') e' he' ⟨hg, hw⟩ _ hσ

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
