-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's copy arrivals on the ring slots' full barriers

Standalone fact (following does not read it). A lane's copy arrivals on the full barrier of ring
slot `j` (offset `32 + 8 j`) are the occurrences of slot `j` among its published packets: its
commits less the one whose arrival is pending (between a packet's commit and its arrival). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The edge check: a commit makes an arrival pending, the arrival publishes the packet, and no
other edge changes the pending arrival. -/
def arrChk (_ : Bool) (s s' : Site) : Bool :=
  match tag s s' with
  | .commit => (inPkt s').2 == (inPkt s).2 + 1
  | .pub => (inPkt s).2 == 1 && (inPkt s').2 == 0
  | _ => (inPkt s').2 == (inPkt s).2

theorem arr_edges : Edges arrChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def ArrRing (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ j : Fin 3, dn.2 (.asyncArrive (bl L g (32 + 8 * j.val))) =
    ringCnt (dn.2 .commit - (inPkt dn.1.site).2) j.val

variable {p : Params} {L : Launch} {g w : Nat}

theorem arr_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hJ : Ref p L g w dn)
    (hm : Move L g w dn e d') (h : ArrRing L g dn) :
    ArrRing L g (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  have hc1 : (inPkt d.site).2 ≤ n .commit := by
    have h0 := hJ.commit
    simp only at h0
    omega
  intro j
  have hj := j.isLt
  simp only [bump_tag hm]
  have hc : arrChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · simp [arrChk, h', tag_self]
    · exact arr_edges.ok h'
  have h0 := h j
  simp only at h0
  rw [h0]
  unfold arrChk at hc
  revert hc
  cases tag d.site d'.site <;>
    simp only [Tag.cnt, beq_iff_eq, Bool.and_eq_true, reduceCtorEq, Option.some.injEq,
      Cnt.asyncArrive.injEq, bl, Loc.mk.injEq, true_and, ↓reduceIte, Nat.add_zero] <;> intro hc
  case commit => rw [hc]; congr 1; omega
  case pub =>
    obtain ⟨h1, h2⟩ := hc
    rw [h1] at hc1
    rw [h1, h2]
    rw [show n .commit - 0 = n .commit - 1 + 1 by omega, ringCnt_succ]
    by_cases hx : (n .commit - 1) % 3 = j.val
    · simp only [hx, ↓reduceIte]
    · simp only [hx, ↓reduceIte]
      split <;> omega
  all_goals rw [hc]

/-- **The copy arrivals on the ring slots' full barriers** at every state of a loader lane. -/
theorem arr_ring {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : ArrRing L g (d, LdWarp.lcn n) :=
  LdWarp.fact_at (I := fun _ => ArrRing L g) (fun _ j => by simp [ringCnt])
    (fun _ _ _ _ _ hJ hm h => arr_step hJ hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
