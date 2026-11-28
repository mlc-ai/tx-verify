-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow PTX.Proof

/-- Decode a single byte extracted from either publication, with its original
32-bit memory provenance. Indices 0 and 1 belong to the two idle warps. -/
theorem role_target (i : Fin 4) (initial : Bool) :
    readTarget [(b32 (if initial then 16777730 else 50529027)).toBytes[i.val]?] =
      some (if initial then (if i.val=2 then .loaderEntry else
        if i.val=3 then .mmaEntry else .idleDec) else .exitSync) := by
  fin_cases i <;> cases initial <;>
    simp [readTarget,b32,rebuild,rebuild.halves,Value.byteAt,intByte,rebuildBits,littleEndianBits,
      byteBits,Value.bitPattern,Value.bytes,Value.toBytes,pure,Except.pure,extendLoaded,
      MemExt.extendBits,target,truncBits,Except.toOption]

def Called (warp : Nat) (d : D) : Prop :=
  (d.site=.loaderEntry → warp=6 ∧ d.round=0) ∧ (d.site=.mmaEntry → warp=7 ∧ d.round=0)

/-- The site a read of the role word leads to. -/
theorem read_dst {L g r ev dn} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (read : ∀ a bs, ev.kind=.rd a bs →
      bs=[(b32 (if r=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (step : next L g ⟨.read,r⟩ ev=some (some dn)) :
    dn = ⟨if r=0 then (if g%L.block/32=6 then .loaderEntry else if g%L.block/32=7 then .mmaEntry
      else .idleDec) else .exitSync, r⟩ := by
  simp only [next] at step
  split at step <;> try contradiction
  rename_i a bs kind
  have bytes := read a bs kind
  let i : Fin 4 := ⟨g%L.block/32-4,by omega⟩
  have choose := role_target i (decide (r=0))
  simp only [decide_eq_true_eq] at choose
  rw [bytes,choose] at step
  simp only [Option.map_some,Option.some.injEq] at step
  subst dn
  have h2 : i.val=2 ↔ g%L.block/32=6 := by dsimp [i]; omega
  have h3 : i.val=3 ↔ g%L.block/32=7 := by dsimp [i]; omega
  simp only [h2,h3]

theorem called_next {L g d ev dn} (low : 4≤g%L.block/32) (high : g%L.block/32<8)
    (read : ∀ a bs, d.site=.read → ev.kind=.rd a bs →
      bs=[(b32 (if d.round=0 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?])
    (step : next L g d ev=some (some dn)) : Called (g%L.block/32) dn := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    have dst := read_dst low high (fun a bs kd => read a bs rfl kd) step
    subst dst
    by_cases init : r=0 <;> by_cases w6 : g%L.block/32=6 <;> by_cases w7 : g%L.block/32=7 <;>
      simp_all [Called]
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals cases step
  all_goals simp [Called]

theorem round_mono {L g d dn ev} (move : next L g d ev=some (some dn)) : d.round≤dn.round := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at move
    split at move <;> try contradiction
    obtain ⟨_,_,h⟩ := Option.map_eq_some_iff.mp move
    cases h
    rfl
  all_goals simp only [next] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals simp

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
