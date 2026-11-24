-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Lib.CollKind
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Lemmas.Kernel.Progress.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp collectives of the MMA warp: its shuffles, ballots and elections -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The MMA warp's sites whose event is a warp collective. -/
def Mma.Site.wcoll : Mma.Site → Bool
  | .bcast | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .sh _ | .eq _ | .ep _
  | .ce _ => true
  | _ => false

/-- **The kind of an MMA event.** -/
theorem mma_ev_kind {d : Mma.D} {e : Event} (hev : Mma.Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f) : CollKind e.kind d.site.wcoll := by
  obtain ⟨s, v⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  case word k | down k | total k | vote k | pre k | tiles k =>
    exact epi_kind hev (by simp [Mma.Site.toE]) hub
  case up k j => exact epi_kind hev (by simp [Mma.Site.toE]) hub
  case bar1 | bar2 => rw [hev]; exact .bar _ _ _
  case bcast | sh => obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  case ldAlloc =>
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .rd _ _
    · exact absurd h (hub f)
  case q0 | q1 | uk =>
    rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .rd _ _
    · exact absurd h (hub f)
  case wt | mw =>
    rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .wait _ _ _ _ _
    · exact absurd h (hub f)
  case eq | ep | ce =>
    rcases hev with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · rw [h]; exact .elect _ _ _
    · exact absurd h (hub f)
  case qk | pv =>
    rcases hev with ⟨_, _, _, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .tc _
    · exact absurd h (hub f)
  case cm =>
    rcases hev with ⟨_, h, -⟩ | ⟨f, h⟩
    · rw [h]; exact .tc _
    · exact absurd h (hub f)
  case relinq | dealloc =>
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .tc _
    · exact absurd h (hub f)
  case exit => rw [hev]; exact .exit

/-- The collectives a thread state of the MMA warp has made. -/
def mmaCnt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Nat :=
  σ.2 .shfl + σ.2 .vote + (σ.2 (.mma .won) + σ.2 (.mma .lost))

private theorem start_coll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {s : Startup.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt L 12 s n) :
    Sched.isWarpColl e = (match s.site with | .sh _ => true | _ => false) ∧
      (if Sched.isWarpColl e then 1 else 0) =
        (if isColl e then 1 else 0) + (if isElectEv e then 1 else 0) := by
  obtain ⟨hev, -⟩ := start_fired hp hX he hσ
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt] at hS
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;> subst h <;>
      exact ⟨rfl, rfl⟩
  case fence => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩
  case bar => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩

/-- Whether a thread state of the MMA warp is at a collective site. -/
def mmaAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Bool :=
  match σ with
  | (.inl s, _) => match s.site with | .sh _ => true | _ => false
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => d.site.wcoll
  | _ => false

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hub hg hw

/-- **An event of the MMA warp** is a warp collective exactly at a collective site, and is a
shuffle, a full ballot or an election. -/
theorem mma_event_coll {k : Nat} {σ : (thread p L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Sched.isWarpColl e = mmaAt p L g σ ∧ (if Sched.isWarpColl e then 1 else 0) =
      (if isColl e then 1 else 0) + (if isElectEv e then 1 else 0) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · exact start_coll hp hX he hσ hR.1
  · rcases d with s | ⟨u, d⟩
    · have hev : Mma.PreEv e := by
        rcases Mma.open_ev hp hX hFw hw he hne with ⟨s', n', hσ', -⟩ | ⟨s', n', hσ', -, -, hev⟩ |
          ⟨d', n', hσ', -⟩
        · rw [hσ] at hσ'; cases hσ'
        · exact hev
        · rw [hσ] at hσ'; cases hσ'
      obtain ⟨pc, kd⟩ := e
      rcases hev with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp only at h <;>
        subst h <;> exact ⟨rfl, rfl⟩
    · exact (mma_ev_kind (Mma.mfired hp hX he hσ).1 hne).counts

/-- **The collectives before a state of the MMA warp** are its ghost counts. -/
theorem mma_cnt_eq {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP Sched.isWarpColl = mmaCnt p L g σ := by
  have h1 : ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take k).countP isColl + ((X.tr g).take k).countP isElectEv := by
    clear hσ
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.take_add_one]
      cases he : (X.tr g)[k]? with
      | none => simpa using ih
      | some e =>
        have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf =>
          hub ⟨(g, k), pc, f, show (X.tr g)[k]? = _ by rw [he, hf]⟩
        obtain ⟨σ', hσ', -⟩ := good_state hp hX (show X.get (g, k) = some e from he) hne
          (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k)
        have := (mma_event_coll hp hX hFw hub hg hw (show X.get (g, k) = some e from he) hσ').2
        simp only [Option.toList_some, List.countP_append, List.countP_singleton]
        omega
  have h2 := elect_split hX (g := g) k
  obtain ⟨hs, hv⟩ := counts hσ
  rw [h1, countColl, hs, hv]
  have c1 := count hσ (.mma .won)
  have c2 := count hσ (.mma .lost)
  change elections X g k = ((X.tr g).take k).countP (cls L g (.mma .won)) +
    ((X.tr g).take k).countP (cls L g (.mma .lost)) at h2
  rw [c1, c2] at h2
  change ((X.tr g).take k).countP isElectEv = _ at h2
  rw [h2]
  rfl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
