-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX

/-- Requests of a round before a site: the head's, then the role's. -/
def requestOffset : Site → Nat
  | .head => 0
  | .idleSync | .idleSyncAgain | .idleInc => 2
  | _ => 1

def requestPhase (d : D) := 3*d.round + requestOffset d.site

private theorem site_hit (s : Site) : s.pc ∈ Lib.requestPcs ↔
    s = .head ∨ s = .idleDec ∨ s = .idleInc ∨ s = .loaderEntry ∨ s = .mmaEntry := by
  cases s <;> decide

private theorem target_phase (n) : requestOffset (target n) = 1 := by
  unfold target
  split <;> rfl

private theorem read_phase {bs s} (h : readTarget bs = some s) : requestOffset s = 1 := by
  unfold readTarget at h
  cases hr : (rebuild 3 bs).toOption with
  | none => simp [hr] at h
  | some v =>
    cases hx : (extendLoaded (.zero 32) 8 v).toOption with
    | none => simp [hr,hx] at h
    | some x =>
      simp [hr,hx] at h
      split at h <;> try contradiction
      cases h
      exact target_phase _

/-- The retry after an invalid role byte repeats the head's request without the round's other
two, so the count is exact only where that path is not taken. -/
theorem request_next {L g d ev dn} (ok : d.site ≠ .badSyncAgain)
    (hn : next L g d ev = some (some dn)) :
    requestPhase dn = requestPhase d +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,r⟩ := d
  cases s
  case badSyncAgain => exact (ok rfl).elim
  case read =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i bs _
    cases hr : readTarget bs with
    | none => simp [hr] at hn
    | some dest =>
      simp only [hr,Option.map_some,Option.some.injEq] at hn
      subst dn
      change 3*r + requestOffset dest = 3*r + 1 + 0
      rw [read_phase hr,Nat.add_zero]
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp [requestPhase,requestOffset,Nat.mul_add]

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
