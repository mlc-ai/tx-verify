-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's successful polls of the ring slots' empty barriers

Standalone fact (following does not read it). A lane's successful polls of the empty barrier of
ring slot `j` (offset `56 + 8 j`) are the occurrences of slot `j` among its first
`c + acqOff s` packets, where `c` is its commits and `acqOff s` the slots the state at site `s`
has acquired beyond them: one inside a packet after its slot wait, `j` at the drain's poll `j`, all
three after the drain's polls. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The slots a state has acquired beyond its commits. -/
def acqOff : Site → Nat
  | .ptP _ _ _ | .ptR _ _ _ | .ptS _ _ _ | .lw _ _ _ | .xl _ _ _ | .xh _ _ _ | .cp _ _ _ _
  | .commit _ _ => 1
  | .dw j => j.val
  | .dq | .de | .da | .exit => 3
  | _ => 0

/-- The edge check: a commit moves one slot from `acqOff` to the commits, a ring poll acquires the
slot after `c + acqOff s`, and no other edge changes `acqOff` or polls a ring barrier. -/
def acqChk (_ : Bool) (s s' : Site) : Bool :=
  match tag s s' with
  | .commit => acqOff s' + 1 == acqOff s
  | .acqRing δ => δ == acqOff s && acqOff s' == acqOff s + 1
  | .acq o => !(o == 56 || o == 64 || o == 72) && acqOff s' == acqOff s
  | _ => acqOff s' == acqOff s

theorem acq_edges : Edges acqChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def AcqRing (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ j : Fin 3,
    dn.2 (.acquire (bl L g (56 + 8 * j.val))) = ringCnt (dn.2 .commit + acqOff dn.1.site) j.val

variable {L : Launch} {g w : Nat}

theorem acq_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g w dn e d')
    (h : AcqRing L g dn) : AcqRing L g (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  intro j
  have hj := j.isLt
  simp only [bump_tag hm]
  have hc : acqChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · simp [acqChk, h', tag_self]
    · exact acq_edges.ok h'
  have h0 := h j
  simp only at h0
  rw [h0]
  unfold acqChk at hc
  revert hc
  cases tag d.site d'.site <;>
    simp only [Tag.cnt, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_false_iff, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, bl,
      Loc.mk.injEq, true_and, ↓reduceIte, Nat.add_zero] <;> intro hc
  case commit => rw [show n .commit + 1 + acqOff d'.site = n .commit + acqOff d.site by omega]
  case acqRing δ =>
    obtain ⟨rfl, h2⟩ := hc
    rw [h2, ← Nat.add_assoc (n .commit), ringCnt_succ]
    by_cases hx : (n .commit + acqOff d.site) % 3 = j.val
    · simp only [hx, ↓reduceIte]
    · simp only [hx, ↓reduceIte]
      split <;> omega
  case acq o =>
    obtain ⟨h1, h4⟩ := hc
    rw [h4]
    split <;> omega
  all_goals rw [hc]

/-- **The successful polls of the ring slots' empty barriers** at every state of a loader lane. -/
theorem acq_ring {p : Params} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : AcqRing L g (d, LdWarp.lcn n) :=
  LdWarp.fact_at (I := fun _ => AcqRing L g) (fun _ j => by simp [ringCnt]; rfl)
    (fun _ _ _ _ _ _ hm h => acq_step hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
