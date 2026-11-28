-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won

@[expose] public section

/-! # The TMA lane won its election

The TMA instance of `Common/SubWon.lean`. A lane of warp 5 that loses the election at pc 2165 is
handed back to warpgroup 1's idle code (`tma_lose_idle`), so a lane with an event of the TMA code
after the election won it (`tma_won`): an earlier event of the lane is the election with the full
mask whose leader is the lane's own index. Nor does it leave the TMA code after the election
(`tmaPostR`, `tma_post_next`): a later state or event of a lane with an event there is the role's
(`tma_post_state`, `tma_post_at`). For the TMA role's exports (`Tma/Export/*.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **A lane that loses the TMA election enters the idle region.** -/
theorem tma_lose_idle {d : Tma.D} {n : Cls → Nat} (hs : d.site = .elect) {pc mk inst ld : Nat}
    (hld : PTX.laneOf L g ≠ ld) {σ' : (thread P L g).D}
    (hn : (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n))
      ⟨pc, .elect mk inst ld⟩ = some (some σ')) : IdleR σ' := by
  simp only [Code.toMachine, Code.glue] at hn
  simp at hn
  obtain ⟨a, ha, rfl⟩ := hn
  rw [Tma.succ_lose hs hld ha]
  cases hok : subOk L g .idle <;>
    simp [Code.backEnter, subBack, Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel,
      hok, IdleR]

/-- A TMA event after pc 2165 is not the election's. -/
private theorem tma_not_elect {d : Tma.D} (hE : Tma.Ev L g d e) (hr : 2165 < e.pc) :
    d.site ≠ .elect := by
  intro h
  have h1 := hE.1
  rw [h] at h1
  simp only [Tma.Site.pc] at h1
  omega

/-- An event of the TMA ledger's election class is an election at a pc of the TMA code. -/
private theorem tma_cls_elect {f : Event} (hcl : Tma.cls .elect f = true) :
    ∃ mk inst ld, f.kind = .elect mk inst ld ∧ 2165 ≤ f.pc ∧ f.pc ≤ 2330 := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | elect mk inst ld =>
    simp only [Tma.cls, Tma.inRole, Bool.and_eq_true, decide_eq_true_eq] at hcl
    exact ⟨mk, inst, ld, rfl, hcl.1⟩
  | wait l q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf] at hcl
  | _ => simp [Tma.cls, Tma.kindOf] at hcl

/-- **A lane at a TMA state after the election won it** (the state's ledger holds one
election): an earlier event of the lane is the election with the lane's index as leader. -/
theorem tma_won_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {d : Tma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hR : Tma.RefCore L g d (fun c => n (.tma c))) (hne : d.site ≠ .elect) :
    ∃ j < k, ∃ inst, X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ := by
  have h1 := Tma.elect_one hR hne
  have h2 := state_count hσ (.tma .elect)
  simp only at h2
  rw [h2] at h1
  obtain ⟨f, hf, hcl⟩ := List.countP_pos_iff.mp (by rw [h1]; exact Nat.one_pos)
  obtain ⟨j, hjk, hj⟩ := get_lt_of_mem_take hf
  obtain ⟨mk, inst, ld, hkd, hpc1, hpc2⟩ := tma_cls_elect hcl
  obtain ⟨pc, kd⟩ := f
  simp only at hkd hpc1 hpc2
  subst hkd
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  have hrj : 2162 ≤ pc ∧ pc < 2332 := ⟨by omega, by omega⟩
  obtain ⟨dj, nj, rfl, -, -, hEj, hlj, -⟩ := tma_state hJj hij hevj hpcj hrj
  obtain ⟨hsj, rfl, rfl⟩ := Tma.ev_elect hlj hEj
  refine ⟨j, hjk, inst, ?_⟩
  rw [won_of hj hjk hσj hσ (fun h => h)
    (fun h => by simp [Code.toMachine, Tma.succ, Tma.electNext, hsj] at h)
    fun hld _ h => tma_lose_idle hsj hld h]
  exact hj

/-- **A lane with an event of the TMA code after the election won it**: an earlier event of the
lane is the election at pc 2165 with the full mask whose leader is the lane's index. -/
theorem tma_won (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 2165 < e.pc ∧ e.pc < 2332) :
    ∃ j < k, ∃ inst, X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, -, hE, -, -⟩ := tma_state hJ hi hev hpc ⟨by omega, hr.2⟩
  have hu : n (.tma .ub) = 0 := (state_count hσ (.tma .ub)).trans (lane5_take_noUb hX he)
  exact tma_won_at hp hX hFw hσ (hR (state_ub hX hσ he) hu) (tma_not_elect hE hr.1)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
