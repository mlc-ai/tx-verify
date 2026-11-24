-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Spec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.OutputMap
open PTX

def copy (i : Nat) : Instr :=
  let src := if i = 0 then 1081 else if i = 1 then 1084 else 1083+2*i
  let col := if i = 0 then 1082 else if i = 1 then 1085 else 1084+2*i
  ⟨none, .cpTensorStore (.reg 2882) [.reg col, .reg 1083, .reg 1086] src 0 none .tile none⟩

def advance (i : Nat) : Instr :=
  Transfers.add (if i = 1 then 1084 else 1083+2*i) 1117 (86912+256*i)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 60000 in
theorem sites : Transfers.slice 3051 32 = some ([copy 0] ++
    ((List.range 15).flatMap fun j => [advance (j+1), copy (j+1)]) ++ [⟨none, .bulkCommit⟩]) := by
  rfl

def descriptor (p : Problem) (allocation : TensorDescriptor.AllocationClass) :
    TensorDescriptor.Descriptor 2 where
  format := .bf16
  base := p.outputBase
  extent := ![128, Batches.firstToken p.length p.sequences, p.heads]
  outerStride := ![256*p.heads, 256]
  box := ⟨![8, 16, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := allocation

def strip (p : Problem) (allocation : TensorDescriptor.AllocationClass) (smem : Loc)
    (stage : Fin 2) (token head : Nat) (group : Fin 16) : TensorStore.Spec where
  outer := 2
  descriptor := descriptor p allocation
  origin := ![((8*group.val : Nat) : Int), (token : Int), (head : Int)]
  sharedBase := { smem with addr := smem.addr + 86912 + 4096*stage.val + 256*group.val }

section
variable (p : Problem) (a : TensorDescriptor.AllocationClass) (smem : Loc) (stage : Fin 2)
local notation "d" => descriptor p a
local notation "s" => strip p a smem stage

def slot (col : Fin 8) (row : Fin 16) (byte : Fin 2) : TensorTransfer.Slot d :=
  ⟨⟨col, by simp [descriptor, TensorTile.count, TensorTile.step]⟩,
   ⟨row, by simp [descriptor, TensorTile.rows, TensorTile.rowsOf,
     TensorTile.count, TensorTile.step]⟩, byte⟩

local notation "cell" => slot p a

theorem coordinates (token head : Nat) (group : Fin 16) (col : Fin 8) (row : Fin 16)
    (byte : Fin 2) :
    let st := s token head group
    TensorTransfer.coord st.descriptor st.origin st.rows (cell col row byte) =
      ![((8*group.val+col.val : Nat) : Int), ((token+row.val : Nat) : Int), (head : Int)] := by
  dsimp only
  funext axis
  fin_cases axis <;>
    simp [strip, descriptor, slot, TensorTransfer.coord, TensorTransfer.index, TensorTile.coord,
      TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step, Fin.cases,
      Nat.mod_eq_of_lt row.isLt, Nat.div_eq_of_lt row.isLt] <;> rfl

theorem global (token head : Nat) (group : Fin 16) (col : Fin 8) (row : Fin 16) (byte : Fin 2)
    (live : token+row.val < Batches.firstToken p.length p.sequences) (hh : head < p.heads) :
    (s token head group).globalAddress (cell col row byte) = some (p.outputBase +
      256*((token+row.val)*p.heads+head) + 2*(8*group.val+col.val) + byte.val) := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup
  rw [coordinates]
  let c : Fin 3 → Int :=
    ![((8*group.val+col.val : Nat) : Int), ((token+row.val : Nat) : Int), (head : Int)]
  have inside (i : Fin 3) : 0 ≤ c i ∧ c i < (((descriptor p a).extent i : Nat) : Int) := by
    fin_cases i <;> simp [c, descriptor] <;> omega
  rw [ite_eq_left ⟨inside, byte.isLt⟩]
  congr 1
  simp only [TensorAddress.byteAddress, Fin.sum_univ_succ]
  change p.outputBase + ((8*group.val+col.val)*2 +
      ((token+row.val)*(256*p.heads) + (head*256 + 0))) + byte.val = _
  ring

theorem output_location (seq head block : Nat) (row : Fin 16) (v : Fin 128) (b : Fin 2)
    (hs : seq < p.sequences) (hh : head < p.heads) (ht : 16*block+row.val < p.length seq) :
    let token := Batches.firstToken p.length seq + 16*block
    ∃ (group : Fin 16) (col : Fin 8), (s token head group).globalAddress (cell col row b) =
      some ((p.outputLoc seq head (16*block+row.val) v).addr + b.val) := by
  dsimp only
  let token := Batches.firstToken p.length seq + 16*block
  have live := Batches.token_lt_end p.length hs ht
  refine ⟨⟨v.val/8, by omega⟩, ⟨v.val%8, by omega⟩, ?_⟩
  rw [global _ _ _ _ _ _ _ _ _ _ (by omega) hh]
  dsimp [Problem.outputLoc]
  rw [show 8*(v.val/8)+v.val%8 = v.val by omega]
  ring

theorem output_disjoint {i j ti tj hi hj : Nat} {v w : Fin 128} {b c : Fin 2}
    (it : ti < p.length i) (jt : tj < p.length j) (ih : hi < p.heads) (jh : hj < p.heads)
    (same : (p.outputLoc i hi ti v).addr + b.val = (p.outputLoc j hj tj w).addr + c.val) :
    i = j ∧ ti = tj ∧ hi = hj ∧ v = w ∧ b = c := by
  simp only [Problem.outputLoc] at same
  have hv : v = w := Fin.ext (by omega)
  have hb : b = c := Fin.ext (by omega)
  have hh : (Batches.firstToken p.length i+ti)*p.heads+hi =
      (Batches.firstToken p.length j+tj)*p.heads+hj := by omega
  obtain ⟨ht, eh⟩ := Batches.workspace_index ih jh hh
  obtain ⟨eqs, eqt⟩ := Batches.token_unique p.length it jt ht
  exact ⟨eqs, eqt, eh, hv, hb⟩

theorem shared (token head : Nat) (group : Fin 16) (col : Fin 8) (row : Fin 16) (byte : Fin 2) :
    (s token head group).sharedLoc (cell col row byte) = ⟨smem.space, smem.cta,
      smem.addr + 86912 + 4096*stage.val + 256*group.val + 16*row.val + 2*col.val + byte.val⟩ := by
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  simp only [strip, descriptor, slot, TensorDescriptor.Format.bytes, TensorTile.rowBytes,
    TensorTile.count, TensorTile.step, TensorTile.swizzleWidth, TensorSwizzle.offset_none]
  congr 1
  simp [Nat.mul_comm, Nat.add_assoc]

theorem completed (token head : Nat) (group : Fin 16) (col : Fin 8) (row : Fin 16)
    (byte : Fin 2) (live : token+row.val < Batches.firstToken p.length p.sequences)
    (hh : head < p.heads) (e : TensorStore.Effects (s token head group))
    (ok : TensorStore.CopyOk _ e) (done_ : e.fullDone = true) :
    let j := cell col row byte
    let target := p.outputBase + 256*((token+row.val)*p.heads+head) +
      2*(8*group.val+col.val) + byte.val
    TensorStore.destination (s token head group) j = some ⟨.global, 0, target⟩ ∧
      ∃ value, e.read j = some value ∧ e.write j = some value := by
  dsimp only
  have addr := global p a smem stage token head group col row byte live hh
  have dest := congrArg (Option.map (fun x => (⟨.global, 0, x⟩ : Loc))) addr
  refine ⟨dest, ?_⟩
  obtain ⟨v, hv⟩ := (ok.complete done_).2 _ _ dest
  obtain ⟨_, w, hw, eqv⟩ := ok.writes _ _ hv
  exact ⟨v, eqv rfl ▸ hw, hv⟩

end
end FlashKda.Packed.OutputMap
