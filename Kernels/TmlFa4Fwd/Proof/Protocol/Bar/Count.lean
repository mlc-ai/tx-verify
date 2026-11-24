-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Lemmas.Kernel.Safety.StateInv
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

public import Lemmas.Kernel.Safety.StateInvU

@[expose] public section

/-! # A lane's barrier events in its role's barrier classes

The thread ledger counts every barrier event (`Mma.cls .bar`, any id) and, per role, the role's
barrier classes: the correction warps' barrier 2 and their two named barriers
(`Correction.cls .bar2`, `.nb 0`, `.nb 1`), the softmax warps' barrier 2, their named barrier
with a correction warp and their stage's named barrier (`Softmax.cls .bar2`, `.nb`, `.sb`). Every
state of a lane keeps (`bar_count`): no barrier event at a startup state; at a correction or
softmax state, one barrier event (the startup's barrier 0) plus the role's classes; at another
role's state, at least one. The role's classes have closed forms in its places
(`Correction.RefQ`, `Softmax.RefQ`), so a lane's barrier ordinal at each barrier site is a closed
form in its site and rounds. Proved by `Frame.RoleTable.stateInv` on the thread machine's role
table: a startup event is a barrier only at the startup's barrier site, from which the startup
enters its role (`succ_exit_bar`); a role's barrier event names exactly one of its classes (the
ids 2, `3 + (w mod 4)`, `7 + (w mod 4)` of a correction warp, 2, `nbW` from 3 to 10, 11 or 12 of a
softmax warp). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- One for an event of a class. -/
abbrev ind (b : Bool) : Nat := if b then 1 else 0

/-- **The barrier counts of a thread state.** -/
def BarT (L : Launch) (g : Nat) : (thread p L g).D → Prop
  | (.inl _, n) => n (.mma .bar) = 0
  | (.inr ⟨.correction, _⟩, n) =>
      n (.mma .bar) = 1 + n (.corr .bar2) + n (.corr (.nb 0)) + n (.corr (.nb 1))
  | (.inr ⟨.softmax, _⟩, n) =>
      n (.mma .bar) = 1 + n (.soft .bar2) + n (.soft .nb) + n (.soft .sb)
  | (.inr ⟨_, _⟩, n) => 1 ≤ n (.mma .bar)

/-- The correction warps' named barriers: 3 to 6, and 7 to 10. -/
theorem corr_nb_range (L : Launch) (g : Nat) :
    3 ≤ (Correction.nb0W L g).toNat ∧ (Correction.nb0W L g).toNat ≤ 6 ∧
      7 ≤ (Correction.nb1W L g).toNat ∧ (Correction.nb1W L g).toNat ≤ 10 := by
  have h := (show (Epilogue.andi (BitVec.ofNat 64 (g % L.block / 32)) 3).toNat ≤ 3 from by
    simp only [Epilogue.andi, Epilogue.r32, Epilogue.i32, BitVec.toNat_and]
    exact (Nat.and_le_right).trans (by decide))
  simp only [Correction.nb0W, Correction.nb1W, Epilogue.addi, Epilogue.r32, Epilogue.i32,
    truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  generalize (Epilogue.andi (BitVec.ofNat 64 (g % L.block / 32)) 3).toNat = a at h ⊢
  have e3 : ((3 : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 3 := by decide
  have e7 : ((7 : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 7 := by decide
  rw [e3, e7]
  omega

theorem soft_nbW_range : ∀ w < 8,
    3 ≤ (Epilogue.addi (Epilogue.add32 (Epilogue.sub32 (BitVec.ofNat 64 w)
      (Epilogue.andi (Epilogue.add32 (BitVec.ofNat 64 w)
        (Epilogue.shru (Epilogue.shrs (BitVec.ofNat 64 w) 31) 30)) (-4)))
      (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (Epilogue.i32 4)
        (Epilogue.i32 0))) 3).toNat ∧
    (Epilogue.addi (Epilogue.add32 (Epilogue.sub32 (BitVec.ofNat 64 w)
      (Epilogue.andi (Epilogue.add32 (BitVec.ofNat 64 w)
        (Epilogue.shru (Epilogue.shrs (BitVec.ofNat 64 w) 31) 30)) (-4)))
      (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (Epilogue.i32 4)
        (Epilogue.i32 0))) 3).toNat ≤ 10 := by
  decide

/-- A softmax lane's named barrier with its correction warp: 3 to 10. -/
theorem soft_nb_range (h : g % L.block / 32 < 8) :
    3 ≤ (Softmax.nbW L g).toNat ∧ (Softmax.nbW L g).toNat ≤ 10 :=
  soft_nbW_range _ h

set_option maxHeartbeats 4000000 in
/-- **A correction event is a barrier event exactly when it is of one of the role's barrier
classes**, and of one only. -/
theorem corr_bar_ind {d : Correction.D} {e : Event} (hev : Correction.Ev p L g d e) :
    ind (Mma.cls L g .bar e) = ind (Correction.cls L g .bar2 e) +
      ind (Correction.cls L g (.nb 0) e) + ind (Correction.cls L g (.nb 1) e) := by
  obtain ⟨h0, h1, h2, h3⟩ := corr_nb_range L g
  have e0 : (Correction.nb0W L g).toNat ≠ 2 := by omega
  have e1 : (Correction.nb1W L g).toNat ≠ 2 := by omega
  have e2 : (Correction.nb0W L g).toNat ≠ (Correction.nb1W L g).toNat := by omega
  have e3 : (Correction.nb1W L g).toNat ≠ (Correction.nb0W L g).toNat := by omega
  have e4 : 2 ≠ (Correction.nb0W L g).toNat := by omega
  have e5 : 2 ≠ (Correction.nb1W L g).toNat := by omega
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case nb kk | rbar kk | fbar kk =>
    all_goals simp only [Correction.Ev] at hev
    all_goals subst hev
    all_goals fin_cases kk
    all_goals simp [ind, Mma.cls, Correction.cls, Correction.nbOf, Correction.nbW,
      Correction.barK, e0, e1, e2, e3, e4, e5]
  all_goals simp only [Correction.Ev, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals simp [ind, Mma.cls, Correction.cls, Correction.nbOf, e4, e5]

set_option maxHeartbeats 4000000 in
/-- **A softmax event is a barrier event exactly when it is of one of the role's barrier
classes**, and of one only. -/
theorem soft_bar_ind (hw : g % L.block / 32 < 8) {d : Softmax.D} {e : Event}
    (hev : Softmax.Ev p L g d e) :
    ind (Mma.cls L g .bar e) = ind (cls L g (.soft .bar2) e) + ind (cls L g (.soft .nb) e) +
      ind (cls L g (.soft .sb) e) := by
  obtain ⟨h0, h1⟩ := soft_nb_range (L := L) hw
  have f0 : 2 ≠ (Softmax.nbW L g).toNat := by omega
  have f1 : (Softmax.nbW L g).toNat ≠ 2 := by omega
  have f2 : (Softmax.nbW L g).toNat ≠ 11 := by omega
  have f3 : (Softmax.nbW L g).toNat ≠ 12 := by omega
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case bsync b =>
    simp only [Softmax.Ev] at hev
    subst hev
    cases hst : Softmax.stg L g <;>
      simp [ind, Mma.cls, cls, Softmax.cls, Softmax.Cnt.pointed, hw, hst, f0, f1, f2, f3] <;>
      omega
  case narr r =>
    simp only [Softmax.Ev] at hev
    subst hev
    cases hst : Softmax.stg L g <;>
      simp [ind, Mma.cls, cls, Softmax.cls, Softmax.Cnt.pointed, hw, hst, f0, f1, f2, f3] <;>
      omega
  case finarr =>
    simp only [Softmax.Ev] at hev
    subst hev
    cases hst : Softmax.stg L g <;>
      simp [ind, Mma.cls, cls, Softmax.cls, Softmax.Cnt.pointed, hw, hst, f0, f1, f2, f3] <;>
      omega
  all_goals simp only [Softmax.Ev, Epilogue.Ev, Softmax.Site.toE] at hev
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals cases hst : Softmax.stg L g <;>
    simp [ind, Mma.cls, cls, Softmax.cls, Softmax.Cnt.pointed, hw, hst, f0, f1, f2, f3] <;> omega

/-- A startup state of a lane's reference invariant is not at a role's entry. -/
theorem jr_start_site {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n))
    (r : Startup.Entry) : s.site ≠ .enter r := by
  intro hs
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs
  subst hs
  rw [JR_eq] at hJ
  split_ifs at hJ
  · simp only [SmWarp.Ref, SmWarp.StartW] at hJ
    split_ifs at hJ <;> simp [StartAt0, StartAt] at hJ
  · unfold RefAll at hJ
    split_ifs at hJ <;>
      simp [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref, StartAt] at hJ

set_option maxHeartbeats 8000000 in
/-- **Every state of a lane keeps its barrier counts** (`BarT`). -/
theorem bar_count (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) :
    ∀ k σ, Frame.NoUbBefore X g k → Frame.stateAt (thread p L) X g k = some (some σ) →
        BarT L g σ := by
  refine Frame.RoleTable.stateInvU (T := table p L) (S := fun g => g < L.threads)
    (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) (P := fun g σ => BarT L g σ) hg rfl ?_
  rintro ⟨σ1, n⟩ e ⟨σ1', n'⟩ hJ hi hev hB hn hJ'
  obtain ⟨h1, rfl⟩ := Code.counted_next_some (C := glued p L g) hn
  rcases σ1 with s | ⟨i, d⟩
  · -- a startup state
    simp only [BarT] at hB
    have hevS : Startup.Ev L g s e := hev
    simp only [glued, Code.glue, Startup.code] at h1
    cases hsu : Startup.succ L g s e with
    | none => rw [hsu] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hsu] at h1; simp at h1
      | some s' =>
        rw [hsu] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        cases hx : exit L g s' with
        | none =>
          -- stays in the startup: the event is no barrier
          simp only [Code.enter, hx, BarT]
          have hnb : Mma.cls L g .bar e = false := by
            by_contra hb
            have hJs : JR p L g (.inl s, n) := hJ
            obtain ⟨pc, kind⟩ := e
            obtain ⟨site, x1, x2, x3⟩ := s
            have hsb : site = .bar := by
              cases site
              case bar => rfl
              case enter r => exact absurd rfl (jr_start_site hJs r)
              case sh j =>
                fin_cases j <;> simp only [Startup.Ev] at hevS <;>
                  obtain ⟨_, _, hk⟩ := hevS <;> simp [Mma.cls, hk] at hb
              case fence => simp only [Startup.Ev] at hevS; simp [Mma.cls, hevS] at hb
              all_goals simp only [Startup.Ev] at hevS
              all_goals first
                | (rcases hevS with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> simp [Mma.cls, hk] at hb)
                | (rcases hevS with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> simp [Mma.cls, hk] at hb)
            subst hsb
            simp only [Startup.succ, Option.some.injEq] at hsu
            subst hsu
            have hJ'' : JR p L g (Code.enter (Startup.code p L g) (frag p L g) (exit L g)
              (Startup.enterOf ⟨.bar, x1, x2, x3⟩), Code.bump (cls L g) n ⟨pc, kind⟩) := hJ'
            simp only [Code.enter, hx] at hJ''
            have hen : ∃ r, (Startup.enterOf ⟨.bar, x1, x2, x3⟩).site = .enter r := by
              unfold Startup.enterOf; split_ifs <;> exact ⟨_, rfl⟩
            obtain ⟨r, hr⟩ := hen
            exact jr_start_site hJ'' r hr
          simp [Code.bump, cls, hnb, hB]
        | some r =>
          have hsb := succ_exit_bar hsu (by rw [hx]; simp)
          have hJs : JR p L g (.inl s, n) := hJ
          have hJr : JR p L g (.inr ⟨r, (frag p L g r).init⟩, Code.bump (cls L g) n e) := by
            have := hJ'; simpa [table, Code.enter, hx] using this
          obtain ⟨pc, kind⟩ := e
          obtain ⟨site, x1, x2, x3⟩ := s
          simp only at hsb
          subst hsb
          simp only [Startup.Ev] at hevS
          subst hevS
          simp only [Code.enter, hx]
          have hbar : Mma.cls L g .bar ⟨pc, .bar 0 none .sync⟩ = true := rfl
          cases r with
          | correction =>
            have hZ : CorrWarp.ZeroK n := by
              rw [JR_eq] at hJs hJr
              split_ifs at hJs hJr with h8
              · simp [SmWarp.Ref] at hJr
              · unfold RefAll at hJs hJr
                split_ifs at hJs hJr <;>
                  simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
            have z0 := hZ .bar2
            have z1 := hZ (.nb 0)
            have z2 := hZ (.nb 1)
            simp only [BarT, Code.bump, cls, hbar, hB, Correction.cls]
            simp [corr_nb_ne']
            omega
          | softmax =>
            have hZ : SmWarp.ZeroS n := by
              rw [JR_eq] at hJs hJr
              split_ifs at hJs hJr with h8
              · exact hJs.2.2
              · unfold RefAll at hJs hJr
                split_ifs at hJs hJr <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
            have z0 := hZ .bar2
            have z1 := hZ .nb
            have z2 := hZ .sb
            simp only [BarT, Code.bump, cls, hbar, hB, Softmax.cls]
            by_cases hw : g % L.block / 32 < 8
            · simp [soft_nb_ne' hw, hw, Softmax.Cnt.pointed]
              split_ifs <;> first | omega | simp_all
            · simp [hw]; omega
          | _ => simp [BarT, Code.bump, cls, hbar, hB]
  · -- a role state: the role's step
    simp only [glued, Code.glue] at h1
    cases hr : (frag p L g i).next d e with
    | none => rw [hr] at h1; simp at h1
    | some o =>
      cases o with
      | none => rw [hr] at h1; simp at h1
      | some d1 =>
        rw [hr] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        cases i with
        | correction =>
          simp only [BarT] at hB ⊢
          have hh : _ := Correction.Control.Ev.data_or_vote hev.1
          have hind : ind (Mma.cls L g .bar e) = ind (Correction.cls L g .bar2 e) +
              ind (Correction.cls L g (.nb 0) e) + ind (Correction.cls L g (.nb 1) e) := by
            rcases hh with h | ⟨_,_,h⟩
            · exact corr_bar_ind h
            · obtain ⟨pc,kind⟩ := e
              cases h
              rfl
          change n (.mma .bar) + ind (Mma.cls L g .bar e) =
            1 + (n (.corr .bar2) + ind (Correction.cls L g .bar2 e)) +
              (n (.corr (.nb 0)) + ind (Correction.cls L g (.nb 0) e)) +
              (n (.corr (.nb 1)) + ind (Correction.cls L g (.nb 1) e))
          omega
        | softmax =>
          simp only [BarT] at hB ⊢
          have hc : Softmax.Ev p L g d e := hev.1
          have hw : g % L.block / 32 < 8 := hi.2
          have := soft_bar_ind hw hc
          change n (.mma .bar) + ind (Mma.cls L g .bar e) =
            1 + (n (.soft .bar2) + ind (cls L g (.soft .bar2) e)) +
              (n (.soft .nb) + ind (cls L g (.soft .nb) e)) +
              (n (.soft .sb) + ind (cls L g (.soft .sb) e))
          omega
        | _ =>
          simp only [BarT] at hB ⊢
          simp only [Code.bump]
          omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
