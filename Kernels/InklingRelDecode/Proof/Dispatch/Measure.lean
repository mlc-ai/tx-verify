-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.RoleByte

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow PTX.Proof

/-- Room for either worker loop before the final dispatch. The role machines
have 32-bit counters and fewer than 32 observable sites per iteration. -/
def callBound := 32*(2^32+3)

def measure (d : D) : Nat :=
  let high := if d.round=0 then callBound+12 else 6
  match d.site with
  | .head => high+2 | .sync => high+1 | .read => high
  | .loaderEntry | .mmaEntry => callBound+10
  | .idleDec => 14 | .idleSync => 13 | .idleSyncAgain => 12 | .idleInc => 11
  | .badSync => 12 | .badSyncAgain => 11
  | .exitSync => 3 | .exitDealloc => 2 | .ret => 1

theorem measure_bound (d : D) : measure d≤callBound+14 := by
  obtain ⟨s,r⟩ := d
  cases s <;> simp [measure,callBound] <;> split_ifs <;> omega

theorem measure_next {L g d dn ev} (later : d.site=.read → d.round≠0 →
    ∀ a bs, ev.kind=.rd a bs → readTarget bs=some .exitSync)
    (step : next L g d ev=some (some dn)) : measure dn<measure d := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i a bs kind
    obtain ⟨dest,select,eq⟩ := Option.map_eq_some_iff.mp step
    cases eq
    by_cases h : r=0
    · have safe : dest≠.head ∧ dest≠.sync ∧ dest≠.read := by
        unfold readTarget at select
        cases hr : (rebuild 3 bs).toOption with
        | none => simp [hr] at select
        | some v =>
          cases hx : (extendLoaded (.zero 32) 8 v).toOption with
          | none => simp [hr,hx] at select
          | some y =>
            simp [hr,hx] at select
            split at select <;> try contradiction
            cases select
            unfold target
            split <;> decide
      cases dest <;> simp_all [measure,callBound]
    · rw [later rfl h a bs kind] at select
      cases select
      simp [measure,h]
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp [measure]

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
