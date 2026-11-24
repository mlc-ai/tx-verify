-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Prologue
public import Kernels.FlashKdaFwd.Packed.StateMap
public import Kernels.FlashKdaFwd.Packed.Launch

@[expose] public section
namespace FlashKda.Packed.OneToken
set_option maxRecDepth 60000
open PTX

abbrev TensorMap := (outer : Nat) × TensorDescriptor.Descriptor outer

def mapping {outer : Nat} (format : TensorDescriptor.Format) (base : Nat)
    (extent : Fin (outer+1) → Nat) (stride : Fin outer → Nat) (size : Fin (outer+1) → Nat) :
    TensorMap := ⟨outer,⟨format,base,extent,stride,⟨size,fun _ => 1⟩,.none,.zero,.small⟩⟩

def matrixMap (base width rows planes : Nat) : TensorMap :=
  mapping (outer := 2) .bf16 base ![width,rows,planes] ![2*width,2*width*rows] ![8,16,1]

def maps : Fin 11 → TensorMap :=
  ![matrixMap 196608 128 1 1,
    mapping (outer := 0) .bf16 262144 ![1] ![] ![32],
    matrixMap 131072 128 16 2, matrixMap 139264 128 16 2, matrixMap 147456 128 16 2,
    mapping (outer := 1) .f32 155648 ![128,2] ![512] ![128,1],
    matrixMap 156672 16 16 2, matrixMap 157696 16 16 2,
    ⟨2,StateMap.descriptor 393216 1 .small⟩, ⟨2,StateMap.descriptor 589824 1 .small⟩,
    matrixMap 524288 128 1 1]

theorem maps_valid (i : Fin 11) :
    TensorDescriptor.Valid (maps i).2 ∧ 65552 ≤ (maps i).2.base := by
  fin_cases i <;> decide

def mapAddress (i : Fin 11) := 1048576 + 256*i.val

def tensorMapAt (a : Nat) : Option TensorMap :=
  if h : 1048576 ≤ a ∧ (a-1048576)%256 = 0 ∧ (a-1048576)/256 < 11 then
    some (maps ⟨(a-1048576)/256,h.2.2⟩)
  else none

def objectAt (name : String) : Option (ParamObjectDecl × Nat) :=
  ((List.finRange 11).find? fun i => name == Prologue.param i.val).map fun i =>
    (⟨name,8,256,128⟩,mapAddress i)

def otherParams (name : String) : Option (BitVec 64) :=
  if name = Prologue.param 11 then some 524288
  else if name = Prologue.param 12 ∨ name = Prologue.param 13 ∨ name = Prologue.param 14 then some 1
  else if name = Prologue.param 16 then some 2
  else none

def launch : Launch where
  grid := 1
  block := 192
  params := Function.update otherParams (Prologue.param 15) (some 65536)
  paramObjects := objectAt
  tensorMaps := tensorMapAt

theorem grid_valid : launch.clusterGridValid := by
  apply Launch.oneDimLaunch_clusterGridValid
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

set_option maxHeartbeats 2000000 in
theorem host_offset : launch.params (Prologue.param 15) = some 65536 := by
  exact Function.update_self (Prologue.param 15) (some (65536 : BitVec 64)) otherParams

theorem map_bound {a outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (found : launch.tensorMaps a = some ⟨outer,d⟩) : 65552 ≤ d.base := by
  change tensorMapAt a = _ at found
  unfold tensorMapAt at found
  split at found
  · rename_i h
    have bound := (maps_valid ⟨_,h.2.2⟩).2
    rw [Option.some.inj found] at bound
    exact bound
  · cases found

theorem map_binding (i : Fin 11) :
    launch.paramObjects (Prologue.param i.val) =
      some (⟨Prologue.param i.val,8,256,128⟩,mapAddress i) ∧
    launch.tensorMaps (mapAddress i) = some (maps i) := by
  constructor
  · have chosen : (List.finRange 11).find? (fun j => Prologue.param i.val == Prologue.param j.val)
        = some i := by
      have eq : (fun j : Fin 11 => Prologue.param i.val == Prologue.param j.val) =
          (fun j => i == j) := by
        funext j
        by_cases h : i = j
        · simp [h]
        · have diff : (⟨i.val,by omega⟩ : Fin 17) ≠ ⟨j.val,by omega⟩ := by
            intro e
            exact h (Fin.ext (congrArg (fun x : Fin 17 => x.val) e))
          simp [h,Prologue.param_injective diff]
      rw [eq]
      exact (show ∀ j : Fin 11, (List.finRange 11).find? (fun k => j == k) = some j by decide) i
    change Option.map _ _ = _
    rw [chosen]
    rfl
  · change tensorMapAt _ = _
    simp [tensorMapAt,mapAddress,i.isLt]

end FlashKda.Packed.OneToken
