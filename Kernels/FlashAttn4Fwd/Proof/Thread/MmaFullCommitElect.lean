-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsGen

@[expose] public section

/-! # The MMA warp's elections use the full member mask

Every election site of the MMA warp (`elM`, `elC`) is an `elect.sync` with the immediate member
mask `-1` (`elect_ops`). So the event of an election site whose outcome is the thread's lane is
an election with the member mask `0xffffffff` that returned the thread's lane
(`elect_lead_event`). The run invariant records such an election before every site of the
elected lane (`Counts.elected`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

/-- The election sites. -/
def electSites : List Site := (List.finRange 8).map .elM ++ (List.finRange 12).map .elC

theorem mem_electSites {s : Site} (h : s.isElect = true) : s ∈ electSites := by
  cases s <;> simp_all [Site.isElect, electSites]

/-- An `elect.sync` with a destination predicate and the immediate member mask `-1`. -/
def fullElect : Op → Bool
  | .warp ⟨.elect, _, [_, some _], [], some (.imm m)⟩ => m == -1
  | _ => false

/-- Every election site is an `elect.sync` with the immediate member mask `-1`. -/
theorem elect_ops : ∀ s ∈ electSites,
    ((kernel.code[s.pc]?).map fun ins => fullElect ins.op) = some true := by
  decide +kernel

/-- **An election that returned the thread's lane** at an election site is an election with
the full member mask. -/
theorem elect_lead_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hs : d.site.isElect = true) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) (ho : outcome L g e = true) :
    ∃ inst, e.kind = .elect 4294967295 inst (laneOf L g) := by
  have h := elect_ops _ (mem_electSites hs)
  rw [hc] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨gd, op⟩ := ins
  simp only at h hf
  unfold fullElect at h
  split at h
  · rename_i ty dst p m
    obtain rfl : m = -1 := by simpa using h
    rcases fires_elect_mask (bits := truncBits 32 (BitVec.ofInt 64 (-1))) rfl hf with
      ⟨inst, leader, rfl⟩ | ⟨f, rfl⟩
    · simp only [outcome, waitOk, electLead, Bool.false_or, decide_eq_true_eq] at ho
      exact ⟨inst, by rw [ho]; rfl⟩
    · simp [outcome, waitOk, electLead] at ho
  · cases h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
