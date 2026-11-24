-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure

@[expose] public section

/-!
# The MMA role's steps: which sites follow the election, and how the role ends

The MMA warp's elections (`qkElect`, `pvElect`, `finElect`) send the lane the election returned
into the guarded block and the other lanes past it. Three facts of `Mma.next` follow, each by
cases on the site, and they let a lemma over an execution tell, from a thread's state, that the
thread led an election and what it will do next:

* `next_pv`, `next_qk`: a state at a PV (QK) MMA or commit site is entered from the PV (QK) election
  with the election returning the thread's own lane, or from a state of the same half;
* `next_fin`: from a state before the role's last commit that is not `finElect`, the successor is
  still before it; from `finElect` with the election returning the thread's own lane it is
  `finCommit`;
* `wnext_mma`: a state of the composed worker machine at the MMA role is entered from the role's
  own step, or at its first site `setMaxReg`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpMma
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The sites of the PV half's MMAs and commits. -/
def isPv : Mma.Site → Bool
  | .pv _ | .pvCommit1 | .pvCommit2 => true
  | _ => false

/-- The sites of the QK half's MMAs and commit. -/
def isQk : Mma.Site → Bool
  | .qk _ | .qkCommit => true
  | _ => false

/-- The sites from which the role has not yet passed its last commit. -/
def Alive (s : Mma.Site) : Prop := s ≠ .bar1 ∧ s ≠ .setMaxRegInc

/-- **A PV state is entered from the PV election, which returned the thread's lane, or from a PV
state.** -/
theorem next_pv {d d' : Mma.D} {e : Event} (h : Mma.next L g d e = some (some d'))
    (hs : isPv d'.site = true) :
    (d.site = .pvElect ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g = ld) ∨
      isPv d.site = true := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [Mma.next, Mma.start, Mma.afterQk, Mma.qkNext, Mma.pvNext,
    Mma.iterNext] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [isPv])

/-- **A QK state is entered from the QK election, which returned the thread's lane, or from a QK
state.** -/
theorem next_qk {d d' : Mma.D} {e : Event} (h : Mma.next L g d e = some (some d'))
    (hs : isQk d'.site = true) :
    (d.site = .qkElect ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g = ld) ∨
      isQk d.site = true := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [Mma.next, Mma.start, Mma.afterQk, Mma.qkNext, Mma.pvNext,
    Mma.iterNext] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [isQk])

/-- **The role's last commit**: from a state before it, other than `finElect` and `finCommit`, the
successor is a state before it, and from `finElect` the election returning the thread's lane
leads to `finCommit`. -/
theorem next_fin {d d' : Mma.D} {e : Event} (h : Mma.next L g d e = some (some d'))
    (ha : Alive d.site) (hc : d.site ≠ .finCommit) :
    (d.site = .finElect → ∀ mk inst ld, e.kind = .elect mk inst ld → laneOf L g = ld →
      d'.site = .finCommit) ∧ (d.site ≠ .finElect → Alive d'.site) := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  obtain ⟨h1, h2⟩ := ha
  simp only at h1 h2 hc
  cases site <;> simp only [Mma.next, Mma.start, Mma.afterQk, Mma.qkNext, Mma.pvNext,
    Mma.iterNext] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [Alive])

/-- The only MMA state a role byte starts is the role's first site. -/
theorem roleStart_mma {P : Loader.Pro} {s : Worker.Site} {d : Mma.D} {P' : Loader.Pro}
    (h : WComp.roleStart L g P s = some (some (.mma d P'))) : d.site = .setMaxReg := by
  cases s <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq, WComp.WSt.mma.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl)

/-- **A state of the composed worker machine at the MMA role** is entered from the role's own
step, or is its first site. -/
theorem wnext_mma {w : WComp.WSt} {d : Mma.D} {P : Loader.Pro} {e : Event}
    (h : WComp.next L g w e = some (some (.mma d P))) :
    (∃ d0, w = .mma d0 P ∧ d0.site ≠ .setMaxRegInc ∧ Mma.next L g d0 e = some (some d)) ∨
      d.site = .setMaxReg := by
  cases w with
  | worker w0 =>
    obtain ⟨site, P0⟩ := w0
    by_cases hr : site = .ldRole
    · subst hr
      simp only [WComp.next, WComp.dispatch] at h
      split at h
      · rename_i d' hd'
        exact .inr (roleStart_mma h)
      · simp at h
      · simp at h
    · have h' : (Worker.next L g ⟨site, P0⟩ e).map (Option.map WComp.WSt.worker) =
          some (some (.mma d P)) := by
        cases site <;> first | exact absurd rfl hr | exact h
      obtain ⟨a, -, ha⟩ := Ledger.mapInv h'
      cases ha
  | idle d0 =>
    simp only [WComp.next] at h
    split at h
    · simp at h
    · obtain ⟨a, -, ha⟩ := Ledger.mapInv h
      cases ha
  | loader d0 P0 =>
    simp only [WComp.next] at h
    split at h
    · simp at h
    · obtain ⟨a, -, ha⟩ := Ledger.mapInv h
      cases ha
  | mma d0 P0 =>
    simp only [WComp.next] at h
    split at h
    · simp at h
    · rename_i hne
      obtain ⟨a, ha, hb⟩ := Ledger.mapInv h
      simp only [WComp.WSt.mma.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact .inl ⟨d0, rfl, hne, ha⟩
  | exit x =>
    simp only [WComp.next] at h
    split at h <;> simp at h

/-- **A step of the MMA role that does not end it** is the role's own step. -/
theorem wnext_mma_fwd {d : Mma.D} {P : Loader.Pro} {w' : WComp.WSt} {e : Event}
    (h : WComp.next L g (.mma d P) e = some (some w')) (hs : d.site ≠ .setMaxRegInc) :
    ∃ d', w' = .mma d' P ∧ Mma.next L g d e = some (some d') := by
  simp only [WComp.next] at h
  obtain ⟨a, ha, hb⟩ := Ledger.mapInv h
  exact ⟨a, hb.symm, ha⟩

end
end PTX.Kernels.InklingRelDecode.Proof.IpMma
