-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX

def publicationOffset : Site → Nat
  | .head | .sync => 0
  | .idleSyncAgain | .badSyncAgain => 2
  | .idleInc => 3
  | _ => 1

def publicationPhase (d : D) := 3*d.round + publicationOffset d.site

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔
    s = .sync ∨ s = .idleSync ∨ s = .idleSyncAgain ∨ s = .badSync ∨ s = .badSyncAgain := by
  cases s <;> decide

private theorem target_phase (n) : publicationOffset (target n) = 1 := by
  unfold target
  split <;> rfl

private theorem read_phase {bs s} (h : readTarget bs = some s) : publicationOffset s = 1 := by
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

theorem publication_next {L g d ev dn} (hn : next L g d ev = some (some dn)) :
    publicationPhase dn = publicationPhase d +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i bs _
    cases hr : readTarget bs with
    | none => simp [hr] at hn
    | some dest =>
      simp only [hr,Option.map_some,Option.some.injEq] at hn
      subst dn
      change 3*r + publicationOffset dest = 3*r + 1 + 0
      rw [read_phase hr,Nat.add_zero]
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp [publicationPhase,publicationOffset,Nat.mul_add]

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
