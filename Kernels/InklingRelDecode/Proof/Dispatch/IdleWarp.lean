-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.RoleByte

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow PTX.Proof

/-- The idle sites of a round are the idle warps' (warps 4 and 5). -/
def IdleLow (warp : Nat) (d : D) : Prop :=
  (d.site=.idleDec ∨ d.site=.idleSync ∨ d.site=.idleSyncAgain ∨ d.site=.idleInc) → warp<6

private theorem read_idle {L : Launch} {g r bs dest} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (bytes : bs=[(b32 (if r=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (h : readTarget bs=some dest) (idle : dest=.idleDec ∨ dest=.idleSync ∨
      dest=.idleSyncAgain ∨ dest=.idleInc) : g%L.block/32<6 := by
  have choose := role_target ⟨g%L.block/32-4,by omega⟩ (decide (r=0))
  simp only [decide_eq_true_eq] at choose
  rw [bytes] at h
  have h := choose.symm.trans h
  simp only [Option.some.injEq] at h
  by_cases init : r=0
  · by_contra warp
    rcases (show g%L.block/32-4=2 ∨ g%L.block/32-4=3 by omega) with t | t <;>
      simp [init,t] at h <;> subst h <;> simp at idle
  · simp [init] at h
    subst h
    simp at idle

theorem idle_next {L g d ev dn} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (read : ∀ a bs, d.site=.read → ev.kind=.rd a bs →
      bs=[(b32 (if d.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (old : IdleLow (g%L.block/32) d) (step : next L g d ev=some (some dn)) :
    IdleLow (g%L.block/32) dn := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at step
    cases hk : ev.kind <;> simp only [hk] at step <;> try contradiction
    rename_i a bs
    obtain ⟨dest,found,eq⟩ := Option.map_eq_some_iff.mp step
    cases Option.some.inj eq
    exact fun site => read_idle low high (read a bs rfl hk) found site
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals cases step
  all_goals simp_all [IdleLow]

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
