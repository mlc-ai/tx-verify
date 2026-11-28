-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Gen.StepSoftmax11

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

/-- Packing the P payload preserves all control inputs of the counter update. -/
theorem before_increment {s : Site} (sub : ∀ r ∈ ctlLive 1046, r ∈ ctlLive s.pc) :
    SegU kernel Assumptions.all L g 1014 (facts e L g ⟨s,i,v⟩ s.pc)
      1046 (facts e L g ⟨s,i,v⟩ 1046) := by
  apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by decide) (by decide +kernel)
  · rw [facts,factsFrom_keys]
    decide +kernel
  · exact project sub

private noncomputable def frame := (ctlLive 1049).filter fun r => !(r ∈ [1912,1913,2446])

private theorem frame_def : frame = [3,175,177,462,463,464,478,483,486,491,496,497,500,501,532,533,
            610,623,624,666,1533,1956,1957,1958,1959,2023,2024] := by decide +kernel

private theorem write_counter {s z : Site} :
    let val := valueOf e L g ⟨s,i,v⟩
    let out := valueOf e L g ⟨z,i+1,v⟩
    Seg kernel Assumptions.all L g 3 1046 (facts e L g ⟨s,i,v⟩ 1046) 1049
      ((1912,out 1912)::(1913,out 1913)::(2446,out 2446)::factsFrom frame val) := by
  dsimp only
  have key : e.splits + (e.split+i*e.splits) = e.split+(i+1)*e.splits := by ring
  have block : e.split+i*e.splits+e.splits = e.split+(i+1)*e.splits := by ring
  intro t ht
  seg_fp ht using
    first | rfl | exact congrArg (fun n => u32 (n*128)) key | exact congrArg u32 block

private theorem stable_0 {s z : Site} : ∀ r ∈ [3,175,177,462,463,464,478],
    valueOf e L g ⟨s,i,v⟩ r = valueOf e L g ⟨z,i+1,v⟩ r := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  simp only [valueOf,scalarValue,Nat.reduceEqDiff,↓reduceIte,and_self]

private theorem stable_7 {s z : Site} : ∀ r ∈ [483,486,491,496,497,500,501],
    valueOf e L g ⟨s,i,v⟩ r = valueOf e L g ⟨z,i+1,v⟩ r := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  simp only [valueOf,scalarValue,Nat.reduceEqDiff,↓reduceIte,and_self]

private theorem stable_14 {s z : Site} : ∀ r ∈ [532,533,610,623,624,666,1533],
    valueOf e L g ⟨s,i,v⟩ r = valueOf e L g ⟨z,i+1,v⟩ r := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  simp only [valueOf,scalarValue,Nat.reduceEqDiff,↓reduceIte,and_self]

private theorem stable_21 {s z : Site} : ∀ r ∈ [1956,1957,1958,1959,2023,2024],
    valueOf e L g ⟨s,i,v⟩ r = valueOf e L g ⟨z,i+1,v⟩ r := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  simp only [valueOf,scalarValue,Nat.reduceEqDiff,↓reduceIte,and_self]

private theorem frame_value {s z : Site} {r : Nat} (mem : r ∈ frame) :
    valueOf e L g ⟨s,i,v⟩ r = valueOf e L g ⟨z,i+1,v⟩ r := by
  have groups : ∀ n ∈ frame,
    n ∈ [3,175,177,462,463,464,478] ∨
    n ∈ [483,486,491,496,497,500,501] ∨
    n ∈ [532,533,610,623,624,666,1533] ∨
    n ∈ [1956,1957,1958,1959,2023,2024] := by
    rw [frame_def]; decide
  rcases groups r mem with h|h|h|h
  · exact stable_0 r h
  · exact stable_7 r h
  · exact stable_14 r h
  · exact stable_21 r h

theorem increment {s z : Site} :
    SegU kernel Assumptions.all L g 1046 (facts e L g ⟨s,i,v⟩ 1046)
      1049 (facts e L g ⟨z,i+1,v⟩ 1049) := by
  apply SegU.of_seg
  apply (write_counter (s := s) (z := z)).weaken_end
  intro R hR
  obtain ⟨h12,h13,h46,rest⟩ := hR
  apply holds_of_pointwise
  intro r hr
  by_cases h : r ∈ [1912,1913,2446]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> assumption
  · have mem : r ∈ frame := List.mem_filter.mpr ⟨hr,by simpa using h⟩
    change R r = some (valueOf e L g ⟨z,i+1,v⟩ r)
    rw [← frame_value (s := s) (z := z) (e := e) (L := L) (g := g) (i := i) (v := v) mem]
    exact holds_mem rest (mem_factsFrom mem)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
