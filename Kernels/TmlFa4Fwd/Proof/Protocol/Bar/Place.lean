-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The source position of a lane's barrier events

A lane's `k`-th barrier event is at the position `barPc` gives: the startup's barrier, the role's
first rendezvous, and afterwards the place of the ordinal in the tile (`corrPc`, `softPc`, whose
places are those of the operand schedules `corrB`, `softB`), or the role's last barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The position of a correction lane's `k`-th barrier event. -/
def corrPc (T : Option Nat) (k : Nat) : Nat :=
  if k = 0 then 173 else if k = 1 then 7747 else
  match T with
  | none => 9204
  | some R => if k ≤ 3 then 7985 + 3 * (k - 2) else if k ≤ 3 + 2 * R then 8006 + 219 * (k % 2)
      else if k ≤ 5 + 2 * R then 8465 + 296 * (k % 2) else 9204

/-- The position of a softmax lane's `k`-th barrier event. -/
def softPc (T : Option (Nat × Nat)) (k : Nat) : Nat :=
  if k = 0 then 173 else if k = 1 then 3103 else
  match T with
  | none => 7741
  | some (B, P) => if k = 2 then 3583 else if k = 3 then 4397 else if k ≤ 3 + 2 * B then
      (if k % 2 = 0 then 5271 else 5683) else if k ≤ 3 + 2 * B + P then 6891
      else if k = 4 + 2 * B + P then 7616 else 7741

/-- The position of an MMA lane's `k`-th barrier event. -/
def mmaPc (k : Nat) : Nat := if k = 0 then 173 else if k = 1 then 1910 else 2764

/-- The position of a lane's `k`-th barrier event. -/
def barPc (p : Params) (L : Launch) (g k : Nat) : Nat :=
  if Prologue.warpIndex L g < 8 then softPc (tileS p L g) k
  else if Prologue.warpIndex L g < 12 then corrPc (tileC p L g) k
  else mmaPc k

/-- A barrier event after a thread's first has a thread count. -/
theorem schedB_some {k : Nat} (hk : k ≠ 0) : (schedB p L g k).2.1 ≠ none := by
  simp only [schedB, softB, corrB, hk]
  split_ifs <;> (try split) <;> (try split_ifs) <;> simp_all

theorem barPc_zero : barPc p L g 0 = 173 := by
  simp only [barPc, softPc, corrPc, mmaPc, ↓reduceIte, ite_self]

/-- Two lanes of one warp have one schedule of positions. -/
theorem barPc_warp (hp : Pre p L m) {h : Nat} (hs : SameWarp L g h) :
    barPc p L g = barPc p L h := by
  obtain ⟨⟨hg, hh, hc⟩, hw⟩ := hs
  have hW : Prologue.warpIndex L g = Prologue.warpIndex L h := hw
  funext k
  simp only [barPc, hW, tileS_warp (p := p) hc hw, tileC_cta hp hg hh hc]

/-- The startup's barrier event is at position 173. -/
theorem start_bar_pc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k pc id : Nat}
    {cnt : Option Nat} {mode : BarMode} {s : Startup.D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hJ : JR p L g (.inl s, n))
    (hev : Startup.Ev L g s ⟨pc, .bar id cnt mode⟩) : pc = 173 := by
  have hpc : pc = (thread p L g).pc (.inl s, n) :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case bar => exact hpc
  case enter r => exact absurd rfl (jr_start_site hJ r)
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
  all_goals simp only [Startup.Ev] at hev
  all_goals first
    | (cases hev; done)
    | (rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk)

/-- A startup state's barrier event is the first. -/
theorem start_bar_ord (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) :
    ((X.tr g).take k).countP Execution.isBar = 0 := by
  rw [← cls_bar (L := L) (g := g), count hσ]
  exact bar_count hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ

end
end PTX.Kernels.TmlFa4Fwd.Proof
