-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompBase
public import Kernels.InklingRelDecode.Proof.Thread.EvDProSites

@[expose] public section

/-!
# Where the prologue's and the softmax region's machines follow the thread

`ProA.next` and `Sm.next` return `some none` (the machine stops following the thread) only at a
few sites: a value the machine does not follow was loaded or received there. Every other site's
successor is a state or `none` (a fault). `ProA.leave_of` and `DComp.sm_next_follows` state this
per site; the layers above use it to show that every other followed state is `Discharged` or a
base-word stop (`Interface.discharged_or_stop`).

* The prologue (`ProA.mayLeave`): the three request-word loads, the six block-table loads, the
  64 query loads (a loaded value that is not one 32-bit word, or not one 16-bit value) and the
  last `barrier.sync 1` (`bar18`, whose successor `DComp.proNext` gives). The three broadcasts of
  the warp index (`psh0` to `psh2`) record every received word; the election after each is `none`
  (a fault) for a word without bits.
* The softmax region (`DComp.smMayLeave`): the 128 bias loads. The shuffle of the row maximum
  (`shfl5`) follows every received word (an instruction of the score stage's second half that
  faults is `none`). The S tile's wait (`waitLd`) follows every S word (an instruction of the score
  stage's first half that faults is `none`). The broadcast of the warp index (`shfl4`) records the
  lane bits of every received word (a word without bits, or bits the Tensor Memory accesses do
  not accept, is `none`: the shift faults or the S load is undefined behaviour). The S
  load (`ldS`) follows every loaded word (a word that is not four bytes is `none`: the pack that
  reads it throws), the O load and wait (`ldO`, `waitLdO`) every loaded word (a product that
  faults is `none`), and the shuffle of the half sums (`shfl6`) every received word (an `add`
  that faults is `none`). At the loop's test (`bar0`, `bar21`, `arrive`) the region's own successor
  is `some none` exactly where the composed machine hands over to the bridge (`DComp.leaves`), so
  the composed successor there is a state or `none`.

The proof of `ProA.leave_of` evaluates `ProA.next` site by site (`cases` on the site, then on the
event's kind), which stays within the default heartbeats; unfolding `ProA.next` as one term does
not.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The prologue's sites at which `next` may return `some none`. -/
def mayLeave (s : Site) : Bool :=
  s == .ldCu0 || s == .ldCu1 || s == .ldSk || s == .bar18 || s ∈ ldqSites || s ∈ lbSites

/-- **`next` returns `some none` only at a `mayLeave` site.** -/
theorem leave_of {L : Launch} {g : Nat} {d : D} {e : Event} (h : next L g d e = some none) :
    mayLeave d.site = true := by
  obtain ⟨s, dt⟩ := d
  obtain ⟨pc, k⟩ := e
  cases s <;> dsimp only
  all_goals first
    | decide
    | (exfalso; cases k <;> cases h)
    | (exfalso; cases k <;> simp only [next] at h <;> first
        | (split_ifs at h <;> cases h)
        | cases h)

theorem next_follows {L : Launch} {g : Nat} {d : D} {e : Event} (h : mayLeave d.site = false) :
    next L g d e ≠ some none := by
  intro hn
  rw [leave_of hn] at h
  cases h

end
end PTX.Kernels.InklingRelDecode.Proof.ProA

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {L : Launch} {g : Nat} {Q : Params}

/-- **The prologue's composed successor follows the thread** at every site that is not
`ProA.mayLeave`. -/
theorem pro_next_follows {d : ProA.D} {e : Event} (h : ProA.mayLeave d.site = false) :
    next L g Q (.pro d) e ≠ some none := by
  have hb : d.site ≠ ProA.Site.bar18 := by
    intro hb
    rw [hb] at h
    cases h
  show proNext L g Q d e ≠ some none
  unfold proNext
  simp only [hb, ↓reduceIte]
  intro h'
  apply ProA.next_follows (L := L) (g := g) (e := e) h
  cases hh : ProA.next L g d e with
  | none => simp [hh] at h'
  | some o =>
    cases o with
    | none => rfl
    | some a => simp [hh] at h'

/-- The softmax region's sites at which the composed successor may be `some none`. -/
def smMayLeave : Sm.Site → Bool
  | .pre _ | .nxt _ => true
  | _ => false

theorem exitNext_ne {d : Sm.D} : exitNext L g d ≠ some none := by
  unfold exitNext
  split <;> simp

/-- **The softmax region's composed successor follows the thread** at every site that is not
`smMayLeave`. -/
theorem sm_next_follows {d : Sm.D} {e : Event} (h : smMayLeave d.site = false) :
    next L g Q (.sm d) e ≠ some none := by
  show smNext L g d e ≠ some none
  unfold smNext
  split
  · exact exitNext_ne
  · rename_i hl
    intro hn
    obtain ⟨pc, k⟩ := e
    cases hs : d.site <;> simp only [hs, smMayLeave, Bool.true_eq_false] at h <;>
      simp only [Sm.next, hs, leaves, Sm.afterArrive, Sm.afterSetup, Sm.toBar20] at hn hl <;>
      (repeat' split at hn) <;> simp_all [isArrive]

/-- **A successor in the common start comes from the common start, before its broadcast.** -/
theorem dstart_tgt {s : St} {d' : DStart.D} {e : Event}
    (h : next L g Q s e = some (some (.dstart d'))) :
    ∃ d, s = .dstart d ∧ d.site ≠ .shfl ∧ d.site ≠ .toProA := by
  obtain ⟨pc, k⟩ := e
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    refine ⟨_, rfl, ?_, ?_⟩ <;> intro hs <;> simp only at hs <;> subst hs <;>
      simp only [next, dstartNext, DStart.next] at h <;> (repeat' split at h) <;> simp_all
  | pro d =>
    simp only [next, proNext] at h
    split at h
    · split at h <;> simp_all
    · cases h' : ProA.next L g d ⟨pc, k⟩ with
      | none => simp [h'] at h
      | some o => cases o <;> simp [h'] at h
  | sm d =>
    simp only [next, smNext] at h
    split at h
    · unfold exitNext at h
      split at h <;> simp_all
    · cases h' : Sm.next L g d ⟨pc, k⟩ with
      | none => simp [h'] at h
      | some o => cases o <;> simp [h'] at h
  | epi d =>
    simp only [next] at h
    cases h' : Epi.next d ⟨pc, k⟩ with
    | none => simp [h'] at h
    | some o => cases o <;> simp [h'] at h

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
