-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Tmem.Ta
public import Lemmas.Flow.Glue
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Mma.Places
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp

@[expose] public section

/-! # What a lane of the MMA warp has done before each of its states

A lane of warp 12 reaches its allocation prefix with no warp-collective `tcgen05` event before
it (the startup and the `setmaxnreg` fire none); the address store's state follows the lane's
allocation on lane 0 only; every state of the role follows the allocation; and a state of the role
past the read of the allocation word holds the word an earlier read at the `ldAlloc` site returned
(`mma_trace`, by induction along the trace, as `mma_count`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The allocation event of lane `g` at position `k`, with no warp-collective `tcgen05` event
before it. -/
def AllocAt (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  X.get (g, k) = some ⟨1909, .tc (.resource .one (some ⟨.shared, g / L.block, L.sharedBase + 312⟩)
    (.alloc 512))⟩ ∧ ((X.tr g).take k).countP isTcColl = 0

/-- Lane 0's address store after its allocation at position `k`. -/
def StoreAt (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  laneOf L g = 0 → ∃ bs, X.get (g, k + 1) = some ⟨1909, .wr
    { loc := ⟨.shared, g / L.block, L.sharedBase + 312⟩, size := 4 } bs⟩

/-- Lane `g` read the word `w` at position `j`, from a state at the `ldAlloc` site. -/
def ReadAt (p : Params) (L : Launch) (X : Execution) (g j : Nat) (w : Value) : Prop :=
  (∃ v n, Frame.stateAt (thread p L) X g j = some (some (Mma.minj p L g ⟨.ldAlloc, v⟩ n))) ∧
    ∃ pc a bs, X.get (g, j) = some ⟨pc, .rd a bs⟩ ∧ rebuild 3 bs = .ok w

/-- **What a lane of warp 12 has done before its state at position `k`.** -/
def MTrace (p : Params) (L : Launch) (X : Execution) (g k : Nat) : (thread p L g).D → Prop
  | (.inl _, _) => ((X.tr g).take k).countP isTcColl = 0
  | (.inr ⟨.mma, .inl s⟩, _) => match s with
    | .set | .alloc => ((X.tr g).take k).countP isTcColl = 0
    | .wr => laneOf L g = 0 ∧ ∃ k', k = k' + 1 ∧ AllocAt L X g k'
    | .enter => True
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => (∃ k' < k, AllocAt L X g k' ∧ StoreAt L X g k') ∧
      (Mma.past d.site = true → ∃ j < k, ReadAt p L X g j d.v.ta)
  | _ => True

/-- The startup fires no warp-collective `tcgen05` event. -/
theorem start_notc {s : Startup.D} {e : Event} (hev : Startup.Ev L g s e)
    (hx : exit L g s = none) : isTcColl e = false := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk⟩ := hev <;>
      (try simp only at hk) <;> subst hk <;> rfl
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, _, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk <;> rfl
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨l', c, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk <;> rfl
  | fence => simp only [Startup.Ev] at hev; subst hev; rfl
  | bar => simp only [Startup.Ev] at hev; subst hev; rfl
  | enter r => simp [exit] at hx

/-- A role's first state, entered with no warp-collective `tcgen05` event before it. -/
theorem mtrace_enter {k : Nat} (h0 : ((X.tr g).take k).countP isTcColl = 0) (s : Startup.D)
    (n : Cls → Nat) :
    MTrace p L X g k (Code.enter (Startup.code p L g) (frag p L g) (exit L g) s, n) := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> first | trivial | exact h0
  · exact h0

theorem countP_snoc {es : List Event} {e : Event} :
    (es ++ [e]).countP isTcColl = es.countP isTcColl + (if isTcColl e then 1 else 0) := by
  simp only [List.countP_append, List.countP_singleton]

set_option maxHeartbeats 8000000 in
/-- **What a lane of warp 12 has done before each of its states.** -/
theorem mma_trace (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (h12 : Prologue.warpIndex L g = 12) :
    ∀ k, k ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      MTrace p L X g k σ := by
  have hReads := cuQReadsFromLaunch hp hX
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero] at hσ
    cases hσ
    exact mtrace_enter (p := p) (L := L) (X := X) (g := g) (k := 0)
      (by simp only [List.take_zero, List.countP_nil]) (Startup.code p L g).init (fun _ => 0)
  | succ k ih =>
    intro hk σ hσ
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    have hstep := Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = some e from he)
    rw [hσ] at hstep
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some]
    cases hσ0 : Frame.stateAt (thread p L) X g k with
    | none => rw [hσ0] at hstep; simp at hstep
    | some o =>
      cases o with
      | none => rw [hσ0] at hstep; simp [Code.toMachine] at hstep
      | some σ0 =>
        rw [hσ0] at hstep
        have hn : (thread p L g).next σ0 e = some (some σ) := hstep.symm
        have hI := ih (by omega) σ0 hσ0
        have hJ := (Mma.good hp hX hReads hg h12 k).2 σ0 hσ0
        obtain ⟨σ1, n0⟩ := σ0
        obtain ⟨σ', n'⟩ := σ
        obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) hn
        rcases σ1 with s | ⟨i, d⟩
        · have hE := start_fired hp hX he hσ0
          obtain ⟨s', -, rfl⟩ := Code.glue_inl_some h1
          refine mtrace_enter ?_ s' n'
          rw [htake, countP_snoc, start_notc hE.1 hE.2.1]
          exact hI
        cases i with
        | mma =>
          rcases d with s0 | ⟨⟨⟩, d⟩
          · obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
              strict_fired_site hp hX he hσ0 rfl
            have hpc := Flow.fires_pc hf
            have hk3 := Mma.pre_kind hp hat hc hf
            simp only [glued, Code.glue, frag, Mma.M, Mma.G, Mma.S] at h1
            cases s0 with
            | set =>
              obtain ⟨inst, hki⟩ := hk3.1 rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              show ((X.tr g).take (k + 1)).countP isTcColl = 0
              rw [htake, countP_snoc]
              obtain ⟨pc, kind⟩ := e
              simp only at hki
              subst hki
              exact hI
            | alloc =>
              have hki := hk3.2.1 rfl
              have hall : AllocAt L X g k := by
                refine ⟨?_, hI⟩
                rw [he]
                obtain ⟨pc, kind⟩ := e
                simp only at hki hpc
                subst hki hpc
                rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              by_cases hl : laneOf L g = 0
              · simp only [hl, ↓reduceIte, Code.enter, Mma.Start.exit]
                exact ⟨hl, k, rfl, hall⟩
              · simp only [hl, ↓reduceIte, Code.enter, Mma.Start.exit]
                exact ⟨⟨k, by omega, hall, fun h => absurd h hl⟩, fun h => by simp [Mma.past] at h⟩
            | wr =>
              obtain ⟨col, hki⟩ := hk3.2.2 rfl
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              obtain ⟨-, k', hk', hall⟩ := hI
              subst hk'
              simp only [Code.enter, Mma.Start.exit]
              refine ⟨⟨k', by omega, hall,
                fun _ => ⟨(Value.bits 32 (BitVec.ofNat 64 col)).toBytes, ?_⟩⟩,
                fun h => by simp [Mma.past] at h⟩
              rw [he]
              obtain ⟨pc, kind⟩ := e
              simp only at hki hpc
              subst hki hpc
              rfl
            | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
          · simp only [glued, Code.glue, frag, Mma.M, Mma.G] at h1
            cases hs : Mma.succ p L g d e with
            | none => simp [Mma.code, hs] at h1
            | some o' =>
              cases o' with
              | none => simp [Mma.code, hs] at h1
              | some d' =>
                simp only [Mma.code, hs, Option.map_some, Option.some.injEq] at h1
                subst h1
                obtain ⟨⟨k', hk', hall, hst⟩, hrd⟩ := hI
                refine ⟨⟨k', by omega, hall, hst⟩, fun hpd => ?_⟩
                by_cases hpast : Mma.past d.site = true
                · obtain ⟨j, hj, hr⟩ := hrd hpast
                  obtain ⟨hta, -⟩ := Mma.succ_ta hpast hs
                  exact ⟨j, by omega, by rw [hta]; exact hr⟩
                · obtain ⟨site, v⟩ := d
                  cases site <;> simp only [Mma.past, Bool.not_eq_true', not_true_eq_false] at hpast
                  · simp only [Mma.succ, Option.some.injEq] at hs
                    subst hs
                    simp [Mma.past] at hpd
                  · simp only [Mma.succ] at hs
                    obtain ⟨pc, kind⟩ := e
                    cases kind <;> try (cases hs; done)
                    rename_i a bs
                    cases hb : rebuild 3 bs with
                    | error _ => simp [hb] at hs
                    | ok w =>
                      simp only [hb, Option.some.injEq] at hs
                      subst hs
                      exact ⟨k, by omega, ⟨v, n0, hσ0⟩, pc, a, bs, he, hb⟩
        | _ =>
          exfalso
          simp [Mma.Ref] at hJ

end
end PTX.Kernels.TmlFa4Fwd.Proof
