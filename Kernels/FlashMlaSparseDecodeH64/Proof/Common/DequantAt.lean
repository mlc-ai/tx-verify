-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Class

@[expose] public section

/-! # A warpgroup-2 lane's states

For warpgroup 2's time exports (`Dequant/Export/Time.lean`, which import this file privately):
under `Follow`, a state of a lane of warps 8–11 at any prefix of its trace is a startup state
before time `100` (the glue never rests at a startup state that hands over, `glue_gate`) or a
warpgroup-2 state with the role's reference invariant (`deq_state`); the state behind an `exit`
of such a lane is warpgroup 2's exit, with the reference invariant at the prefix counts and the
CTA's block count (`deq_exit_at`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem enter_inl {K : Kernel} {A : List Assumption} {C : Code K A L g} {ι : Type}
    {R : ι → Code K A L g} {ex : C.D → Option ι} {d0 d : C.D}
    (h : Code.enter C R ex d0 = .inl d) : ex d = none := by
  unfold Code.enter at h
  split at h
  · cases h
  · rename_i hx
    cases h
    exact hx

/-- **The glue rests at a startup state only before its hand-over.** -/
theorem glue_gate {i : Nat} {d : Startup.D} {n : Cls → Nat}
    (h : Frame.stateAt (thread P L) X g i = some (some (.inl d, n))) :
    startupEnter P L g d = none := by
  induction i generalizing d n with
  | zero =>
    rw [Frame.stateAt_zero, Option.some.injEq, Option.some.injEq] at h
    have h1 : Code.enter (startupCode P L g) (Code.withStubs (frag P L g) Entry.pc)
        (Code.gatedExit (startupEnter P L g) (sel P L g)) (startupCode P L g).init = .inl d :=
      congrArg Prod.fst h
    exact Code.gatedExit_none.mp (enter_inl h1)
  | succ i ih =>
    cases hf : (X.tr g)[i]? with
    | none =>
      have hl : (X.tr g).length ≤ i := List.getElem?_eq_none_iff.mp hf
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at h
      exact ih h
    | some f =>
      rw [Frame.stateAt_succ hf] at h
      cases hs : Frame.stateAt (thread P L) X g i with
      | none => rw [hs] at h; cases h
      | some o =>
        rw [hs] at h
        cases o with
        | none => simp [Code.toMachine] at h
        | some σ =>
          obtain ⟨s, n0⟩ := σ
          rcases s with d0 | ⟨j, d0⟩
          · simp only [Option.bind_some, Code.toMachine, Code.glue,
              Option.map_eq_some_iff] at h
            obtain ⟨a, ha', b, hb, hab⟩ := h
            subst hb
            obtain ⟨a', -, ha2⟩ := ha'
            obtain ⟨d1, -, rfl⟩ := Option.map_eq_some_iff.mp ha2
            exact Code.gatedExit_none.mp (enter_inl (Prod.mk.inj hab).1)
          · simp only [Option.bind_some, Code.toMachine, Code.glue,
              Option.map_eq_some_iff] at h
            obtain ⟨a, ha', b, hb, hab⟩ := h
            subst hb
            obtain ⟨a', -, ha2⟩ := ha'
            obtain ⟨d1, -, rfl⟩ := Option.map_eq_some_iff.mp ha2
            cases (Prod.mk.inj hab).1

/-- **A state of a lane of warps 8–11**: a startup state before time `100`, or a warpgroup-2
state with the role's reference invariant at its counts. -/
theorem deq_state (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) (hg : g < L.threads)
    {i : Nat} {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    time P L g σ < 100 ∨ ∃ d n, σ = (.inr ⟨.inl .dequant, d⟩, n) ∧
      (n .ub = 0 → Dequant.Ref L g d (fun c => n (.dequant c))) := by
  have hJ := (follow_iff.mp hFw g hg i).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · left
    have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    exact Startup.time_lt hx
  · cases e with
    | dequant =>
      obtain ⟨-, hR, -, -⟩ := hJ
      exact .inr ⟨d, n, rfl, hR⟩
    | wg0 | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

/-- **The state behind an `exit` of a lane of warps 8–11** is warpgroup 2's exit, with the
reference invariant at the prefix counts and the CTA's block count. -/
theorem deq_exit_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ d : Dequant.Control.D,
      Dequant.Ref L g d (fun c => ((X.tr g).take k).countP (Dequant.cls c)) ∧
      d.site = .exit ∧ Dequant.rounds d.l0 d.l1 = blocksOf P L (g / L.block) := by
  have h103 := startup_exit hp hX hFw he
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun _ h => by cases h)
  have h := state_role hJ hi
  rw [← hpc] at h
  simp only at h
  cases h with
  | dequant d n hR _ hpc' hr =>
    rcases hr with hr | ⟨hs, -⟩
    · have := Dequant.ev_class hp (e := ⟨pc, .exit⟩) hev (fun _ h => by cases h) hr.2
      simp [Dequant.PcClass] at this
    · refine ⟨d, ?_, hs, deq_rounds hp hX hσ (by rw [hs]; rfl)⟩
      have hc : (fun c => n (.dequant c)) =
          fun c => ((X.tr g).take k).countP (Dequant.cls c) :=
        funext fun c => state_count hσ (.dequant c)
      rw [← hc]
      exact hR (state_ub hX hσ he)
  | startup _ _ _ _ _ _ hr => omega
  | head _ _ _ _ _ _ hw' => omega
  | idle _ _ _ hw' => simp only [warp] at hw; simp only [warpOf, tidOf] at hw'; omega
  | index _ _ _ hw' => omega
  | mma _ _ _ _ _ hw' => omega
  | tma _ _ _ _ _ hw' => omega
  | wg0 _ _ _ hw' => omega

/-- **Warpgroup 2's machine moves on at its arrivals.** -/
theorem deq_arr_next {d : Dequant.Control.D} {n : Cls → Nat} {f : Event}
    (hs : d.site = .arrD ∨ d.site = .arrF) :
    (thread P L g).toMachine.next (some (.inr ⟨.inl .dequant, d⟩, n)) f ≠ none := by
  rcases hs with hs | hs <;>
    simp [Code.toMachine, Code.glue, Code.withStubs, frag, dequantCode, Dequant.Control.succ, hs]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
