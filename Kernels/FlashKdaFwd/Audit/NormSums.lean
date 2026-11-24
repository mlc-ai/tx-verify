-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormArithmetic

/-! Certified evaluation of the local fused updates and the cross-lane sums on the
one-token raw input. The reductions use the standalone binary32 additions observed in SASS. -/
namespace FlashKda.Normalize
open PTX OneToken
noncomputable section

def squaredWord (key : Bool) : Nat := if key then 0x3f604000 else 0x40401000

/-- One packed load supplies eight bfloat16 coordinates to each lane. -/
def rawPacket (key : Bool) (lane : Nat) : List Nat :=
  if lane = 0 then
    (if key then [0x3e80,0x3f00,0x3f40,0x3d00] else [0x3f80,0x3f80,0xbf80,0xbd00]) ++
      List.replicate 4 0
  else List.replicate 8 0

def candidates (key : Bool) (lane : Nat) : List Nat :=
  if lane = 0 then
    (if key then [0x3d800000,0x3ea00000,0x3f600000] else [0x3f800000,0x40000000,0x40400000])
      ++ List.replicate 5 (squaredWord key)
  else List.replicate 8 0

/-- The widening conversion preserves the real value of each finite bfloat16 input. Reading
the same field shifted into binary32 checks this property on each supplied source word. -/
def widened (raw : Nat) : Option FVal := do
  let v ← brainFloat.decode raw
  guard (binary32.decode (raw <<< 16) = some v)
  return v

def laneSum (initial : FVal) : List Nat → Option FVal
  | [] => some initial
  | raw::rest => do laneSum (← squareStep initial (← widened raw)) rest

def checkedLane (initial : FVal) (raw words : List Nat) :
    Option { v : FVal // laneSum initial raw = some v } :=
  match raw, words with
  | [], [] => some ⟨initial,rfl⟩
  | h::tail, w::ws =>
    match hx : widened h with
    | none => none
    | some x => do
      if hc : squareCertificate initial x w = true then
        let ⟨result, checked⟩ ← checkedLane (wordValue w) tail ws
        return ⟨result, by simp [laneSum, hx, squareStep_sound hc, checked]⟩
      else none
  | _, _ => none

/-- Follow the source lanes in reverse order through the four butterfly exchanges. -/
def warpSum (key : Bool) : List Nat → Nat → Option FVal
  | [], lane => laneSum (.zero false) (rawPacket key lane)
  | d::ds, lane => do
    let (peer, valid) := shflSource .bfly lane d 31
    guard valid
    sumStep (← warpSum key ds lane) (← warpSum key ds peer)

def checkedWarp (key : Bool) (distances : List Nat) (lane : Nat) :
    Option { v : FVal // warpSum key distances lane = some v } :=
  match distances with
  | [] => checkedLane (.zero false) (rawPacket key lane) (candidates key lane)
  | d::ds =>
    match hp : shflSource .bfly lane d 31 with
    | (_,false) => none
    | (peer,true) => do
      let ⟨a,ha⟩ ← checkedWarp key ds lane
      let ⟨b,hb⟩ ← checkedWarp key ds peer
      let field := if a == .zero false && b == .zero false then 0 else squaredWord key
      if hf : (add32 (some .rn)).flushIn [a,b] = [a,b] then
        if hc : exactField (a.add .rn b) field = true then
          let add := sum_of_round hf (exactField_sound hc)
          return ⟨wordValue field, by simp [warpSum, hp, ha, hb, add]⟩
        else none
      else none

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Source PTX selects lane zero to write the first row's reciprocal square roots. -/
theorem checked_sums (key : Bool) :
    warpSum key [1,2,4,8] 0 = some (wordValue (squaredWord key)) := by
  have cert : (checkedWarp key [1,2,4,8] 0).map Subtype.val = some (wordValue (squaredWord key)) :=
    by cases key <;> decide +kernel
  obtain ⟨⟨v,h⟩, _, hv⟩ := Option.map_eq_some_iff.mp cert
  exact h.trans (congrArg some hv)

end
end FlashKda.Normalize
