-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.CollKind
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.ElectForm
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp collectives of the loader warps: their shuffles, ballots and elections -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The loader warps' sites whose event is a warp collective. -/
def Loader.Site.wcoll : Loader.Site → Bool
  | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .xl _ _ _ | .xh _ _ _ | .te _ _
  | .de => true
  | _ => false

/-- **The kind of a loader event.** -/
theorem ld_ev_kind {w : Nat} {d : Loader.D} {e : Event} (hev : Loader.Ev p L g w d e)
    (hub : ∀ f, e.kind ≠ .ub f) : CollKind e.kind d.site.wcoll := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  case word k | down k | total k | vote k | pre k | tiles k =>
    exact epi_kind hev (by simp [Loader.Site.toE]) hub
  case up k j => exact epi_kind hev (by simp [Loader.Site.toE]) hub
  case setmax => obtain ⟨_, _, _, h⟩ := hev; rw [h]; exact .setMax _ _ _
  case q0 | q1 | uk | pgLd =>
    rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .rd _ _
    · exact absurd h (hub f)
  case pgSt | rwSt | ptS =>
    rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
    · rw [h]; exact .wr _ _
    · exact absurd h (hub f)
  case slot | tw | dw | dq => obtain ⟨_, h⟩ := hev; rw [h]; exact .wait _ _ _ _ _
  case ptP | ptR | lw => obtain ⟨_, h⟩ := hev; rw [h]; exact .rd _ _
  case xl | xh => obtain ⟨_, _, h⟩ := hev; rw [h]; exact .shfl _ _ _ _ _ _
  case cp =>
    rcases hev with ⟨_, h⟩ | ⟨f, h⟩
    · rw [h]; exact .copy _
    · exact absurd h (hub f)
  case commit => rw [hev]; exact .commit
  case arrive => rw [hev]; exact .asyncArr _ _
  case te | de =>
    rcases hev with ⟨_, _, -, h⟩ | ⟨f, h⟩
    · rw [h]; exact .elect _ _ _
    · exact absurd h (hub f)
  case ta | da => rw [hev]; exact .arrive _ _ _ _ _
  case tc =>
    rcases hev with ⟨_, _, h, -⟩ | ⟨f, h⟩
    · rw [h]; exact .tensor _ _
    · exact absurd h (hub f)
  case exit => rw [hev]; exact .exit

/-- Whether a thread state of a loader warp is at a collective site. -/
def ldAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Bool :=
  match σ with
  | (.inl s, _) => match s.site with | .sh _ => true | _ => false
  | (.inr ⟨.loader _, d⟩, _) => d.site.wcoll
  | _ => false

private theorem ld_start_coll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {w : Nat} {s : Startup.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt L w s n) :
    Sched.isWarpColl e = (match s.site with | .sh _ => true | _ => false) ∧
      (if Sched.isWarpColl e then 1 else 0) =
        (if isColl e then 1 else 0) + (if Loader.roleEl e then 1 else 0) := by
  obtain ⟨hev, -⟩ := start_fired hp hX he hσ
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt] at hS
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;> subst h <;>
      exact ⟨rfl, rfl⟩
  case fence => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩
  case bar => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩

private theorem ld_start_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {w : Nat} {s : Startup.D} {n : Cls → Nat} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt L w s n) :
    Loader.roleEl e = false := by
  obtain ⟨hev, -⟩ := start_fired hp hX he hσ
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site <;> simp only [StartAt] at hS
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;> subst h <;> rfl
  case fence => simp only [Startup.Ev] at hev; subst hev; rfl
  case bar => simp only [Startup.Ev] at hev; subst hev; rfl

private theorem roleEl_eq {w : Nat} {d : Loader.D} {e : Event} (hev : Loader.Ev p L g w d e)
    (hub : ∀ f, e.kind ≠ .ub f) : Loader.roleEl e = isElectEv e := by
  cases h : isElectEv e with
  | false => simp [Loader.roleEl, h]
  | true =>
    obtain ⟨h1, h2⟩ := Loader.el_site hev hub
    have hel := h1.mp h
    have hc := Loader.el_pc.ok d.site
    rw [hel] at hc
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    simp [Loader.roleEl, h, h2 hel, hc]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hub : ¬ HasUb X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hub hg hw

/-- **An event of a loader warp** is a warp collective exactly at a collective site, and is a
shuffle, a full ballot or an election of the role. -/
theorem ld_event_coll {k : Nat} {σ : (thread p L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Sched.isWarpColl e = ldAt p L g σ ∧ (if Sched.isWarpColl e then 1 else 0) =
      (if isColl e then 1 else 0) + (if Loader.roleEl e then 1 else 0) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hR := (LdWarp.good hp hX hw hg rfl k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · exact ld_start_coll hp hX he hσ hR.1
  · have hev := (LdWarp.lfired hp hX he hσ).1
    rw [roleEl_eq hev hne]
    exact (ld_ev_kind hev hne).counts

/-- **The collectives before a state of a loader warp** are its ghost counts and the elections. -/
theorem ld_cnt_eq {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP Sched.isWarpColl = σ.2 .shfl + σ.2 .vote + Loader.els X g k := by
  have h1 : ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take k).countP isColl + Loader.els X g k := by
    clear hσ
    unfold Loader.els
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
          (LdWarp.good hp hX hw hg rfl k)
        have := (ld_event_coll hp hX hub hg hw (show X.get (g, k) = some e from he) hσ').2
        simp only [Option.toList_some, List.countP_append, List.countP_singleton]
        omega
  obtain ⟨hs, hv⟩ := counts hσ
  rw [h1, countColl, hs, hv]

omit hub in
/-- The startup of a loader warp makes no election. -/
theorem ld_start_els {k : Nat} {s : Startup.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) : Loader.els X g k = 0 := by
  induction k generalizing s n with
  | zero => rfl
  | succ k ih =>
    cases he : (X.tr g)[k]? with
    | none =>
      have hle : (X.tr g).length ≤ k := by simpa using he
      have := ih (by rw [Frame.stateAt_of_le (by omega)] at hσ ⊢; exact hσ)
      unfold Loader.els at this ⊢
      rw [List.take_of_length_le (by omega)] at this ⊢
      exact this
    | some e =>
      have hst := Frame.stateAt_succ (C := thread p L) he
      rw [hσ] at hst
      have hG := LdWarp.good hp hX hw hg rfl k
      cases h0 : Frame.stateAt (thread p L) X g k with
      | none => rw [h0] at hst; simp at hst
      | some o =>
        cases o with
        | none => exact absurd h0 hG.1
        | some σ0 =>
          rw [h0] at hst
          have hn : (thread p L g).next σ0 e = some (some (.inl s, n)) := hst.symm
          have hR := hG.2 σ0 h0
          obtain ⟨σ1, n0⟩ := σ0
          obtain ⟨h1, -⟩ := Code.counted_next_some hn
          rcases σ1 with s0 | ⟨i, d0⟩
          · have hv : Loader.roleEl e = false := ld_start_zero hp hX he h0 hR.1
            unfold Loader.els
            rw [List.take_add_one, he, List.countP_append]
            have := ih h0
            unfold Loader.els at this
            rw [this]
            simp [hv]
          · exfalso
            simp only [glued, Code.glue] at h1
            cases hr : (frag p L g i).next d0 e with
            | none => rw [hr] at h1; simp at h1
            | some o => cases o <;> rw [hr] at h1 <;> simp at h1

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
