-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.PollSynced
public import Lemmas.Kernel.Frame
public import Lemmas.Order.ElectOrdinal
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Lemmas.Flow.PollMeet
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The lanes of the MMA warp meet through their elections

Every `elect.sync` of the code has the immediate mask `-1` (`kernel_electFull`), so every election
event has the full mask (`elect_full`) and the elections of one instance in a warp have one
ordinal (`elect_ordinal`). A lane of warp 12 at a counted state with the count conjuncts of round
`r` at place `q` (`Mma.RefQ`) has made exactly `electAll q r` elections (`mma_elections`: its won
and lost elections), which grows by eight per round (`electAll_succ`). So of two lanes of the warp,
the one with fewer elections before an event that is no election has that event before the
other's later position in the dependency order (`mma_meet`, `Flow.meet_elect`), and two
lanes at one place with the same number of elections are in the same round (`mma_round_eq`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (RefQ electAll pq)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An `elect.sync` with the immediate mask `-1`. -/
def electFullOp : Op → Bool
  | .warp ⟨.elect, _, _, _, some (.imm (-1))⟩ => true
  | .warp ⟨.elect, _, _, _, _⟩ => false
  | _ => true

theorem kernel_electFull : kernel.code.all (fun ins => electFullOp ins.op) = true := by
  decide +kernel

/-- **Every election of the kernel has the full mask.** -/
theorem elect_full (hX : Consistent L kernel Assumptions.all m X) {e : EvId}
    {pc mask inst l : Nat} (h : X.Elect e pc mask inst l) : mask = 4294967295 := by
  obtain ⟨g, k⟩ := e
  have hget : X.get (g, k) = some ⟨pc, .elect mask inst l⟩ := h
  have hg := Frame.lt_of_get hX hget
  obtain ⟨ins, ty, d, pr, mk, hc, hop, t, bits, hb, hbm⟩ :=
    elect_mask (hX.thr g hg) (List.mem_of_getElem? hget) (e := ⟨pc, .elect mask inst l⟩) rfl
  have hall := List.all_eq_true.mp kernel_electFull ins (List.mem_of_getElem? hc)
  rw [hop] at hall
  have hmk : mk = .imm (-1) := by
    revert hall
    cases mk with
    | imm v =>
      intro hall
      by_cases hv : v = -1
      · rw [hv]
      · simp [electFullOp, hv] at hall
    | _ => simp [electFullOp]
  subst hmk
  simp only [readBits] at hb
  cases hb
  rw [← hbm]
  rfl

theorem elect_ordinal (hX : Consistent L kernel Assumptions.all m X) : ElectOrdinal L X :=
  electOrdinal hX (ElectMutual.of_full (fun h => elect_full hX h))

/-- With full masks, an election is won or lost, not both. -/
theorem elect_split1 (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) :
    (if isElectEv e then 1 else 0) =
      (if Mma.cls L g .won e then 1 else 0) + (if Mma.cls L g .lost e then 1 else 0) := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | elect mask inst ld =>
    have hm := elect_full hX (show X.Elect (g, k) pc mask inst ld from he)
    subst hm
    by_cases hl : ld = laneOf L g <;> simp [isElectEv, Mma.cls, hl]
  | _ => simp [isElectEv, Mma.cls]

/-- **A lane's elections are its won and lost ones.** -/
theorem elect_split (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k, elections X g k = ((X.tr g).take k).countP (Mma.cls L g .won) +
      ((X.tr g).take k).countP (Mma.cls L g .lost) := by
  intro k
  unfold elections
  induction k with
  | zero => simp
  | succ k ih =>
    rcases hk : (X.tr g)[k]? with _ | e
    · have hle : (X.tr g).length ≤ k := by
        by_contra h; rw [List.getElem?_eq_getElem (by omega)] at hk; cases hk
      rw [List.take_of_length_le hle] at ih
      rw [List.take_of_length_le (by omega)]
      exact ih
    · rw [List.take_add_one, hk, Option.toList_some, List.countP_append, List.countP_append,
        List.countP_append, ih]
      have := elect_split1 (g := g) hX (show X.get (g, k) = some e from hk)
      simp only [List.countP_singleton]
      omega

/-- **The elections of a lane of warp 12** at a counted state: `electAll` of its place and round. -/
theorem mma_elections (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {d : Mma.D}
    {n : Cls → Nat} {r : Nat} {w : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) :
    elections X g k = electAll d.site.ord r := by
  have c1 := count hσ (.mma .won)
  have c2 := count hσ (.mma .lost)
  simp only [cls] at c1 c2
  rw [elect_split hX k, c1, c2]
  have h1 := hQ.won
  have h2 := hQ.lost
  simp only [Mma.rc] at h1 h2
  rw [h1, h2]
  cases w <;> simp

theorem pq_succ (x q r : Nat) : pq x q (r + 1) = pq x q r + if 20 ≤ x ∧ x < 60 then 1 else 0 := by
  unfold pq
  split_ifs <;> omega

/-- **Eight elections per round.** -/
theorem electAll_succ (q r : Nat) : electAll q (r + 1) = electAll q r + 8 := by
  simp only [electAll, pq_succ]
  norm_num
  omega

theorem electAll_mono (q : Nat) {r r' : Nat} (h : r < r') : electAll q r < electAll q r' := by
  induction r' with
  | zero => omega
  | succ r' ih =>
    rw [electAll_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · have := ih h'; omega
    · subst h'; omega

/-- **Two lanes at one place with the same elections are in the same round.** -/
theorem mma_round_eq {q r r' : Nat} (h : electAll q r = electAll q r') : r = r' := by
  rcases Nat.lt_trichotomy r r' with h1 | h1 | h1
  · have := electAll_mono q h1; omega
  · exact h1
  · have := electAll_mono q h1; omega

/-- **Two lanes of warp 12 meet through their elections**: the lane with fewer elections before
an event that is no election has, after that event, a position before the other lane's in the
dependency order (`PollBefore`). -/
theorem mma_meet (hX : Consistent L kernel Assumptions.all m X) {h k k' : Nat} {d d' : Mma.D}
    {n n' : Cls → Nat} {r r' : Nat} {w w' : Bool} {e : Event} (hw : SameWarp L g h)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w)
    (hσ' : Frame.stateAt (thread p L) X h k' = some (some (Mma.minj p L h d' n')))
    (hQ' : RefQ p L h d'.site.ord d'.v (Mma.rc n') r' w')
    (he : X.get (g, k) = some e) (hne : isElectEv e = false) (hk' : k' < (X.tr h).length)
    (hlt : electAll d.site.ord r < electAll d'.site.ord r') :
    PollBefore L kernel X (g, k) (h, k') :=
  Flow.meet_elect hX (elect_ordinal hX) hw he hne (mma_elections hX hσ hQ)
    (by rw [mma_elections hX hσ' hQ']; omega) hk' (fun h => elect_full hX h)

end
end PTX.Kernels.TmlFa4Fwd.Proof
