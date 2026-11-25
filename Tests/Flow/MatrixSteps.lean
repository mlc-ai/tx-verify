-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MatrixStep
public import Lemmas.Flow.MatrixShape
public import Kernels.FlashKdaFwd.Flow.Code
public import Kernels.FlashKdaFwd.Flow.Sites

/-! # Step combinators and shape lemmas of the warp matrix instructions, on FlashKDA

The combinators of `Lemmas/Flow/MatrixStep.lean` and the shape lemmas of
`Lemmas/Flow/MatrixShape.lean`, each instantiated on a decoded instruction of the FlashKDA
forward kernel, to check that their hypotheses are dischargeable from a generated code lemma
(`Flow.code_<site>`), a `factsFrom` value table and a transition function written by cases on
the event:

* `ldmatrix.sync.aligned.x4.m8n8.shared.b16` at `matrixLoad_1` (states `ldRd`, `ldMx`) and its
  `.trans` variant at `matrixLoad_36` (states `ltRd`, `ltMx`): the row read, then the matrix
  event;
* `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32` at `warpMma_0` (state `mma`);
* `movmatrix.sync.aligned.m8n8.trans.b16` at `matrixMove_0` (state `mov`);
* `stmatrix.sync.aligned.x4.m8n8.shared.b16` at `matrixStore_0` (states `stMx`, `stWr`): the
  matrix event, then the row write.

The toy machine has one state per sub-step and one per successor (the next instruction, with
the facts the event leaves), and records what each event returns. -/

namespace PTX.Tests.MatrixSteps
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashKdaFwd

noncomputable section

/-- The states of the toy machine. -/
inductive Site where
  /-- `ldmatrix` at `matrixLoad_1`, before the row read. -/
  | ldRd
  /-- `ldmatrix` at `matrixLoad_1`, after reading the row `row`. -/
  | ldMx (row : List (Option Byte))
  /-- After `matrixLoad_1`, whose destinations received `vs`. -/
  | ldDone (vs : List Value)
  /-- `mma.sync` at `warpMma_0`. -/
  | mma
  /-- After `warpMma_0`, whose destinations received `vs`. -/
  | mmaDone (vs : List Value)
  /-- `movmatrix` at `matrixMove_0`. -/
  | mov
  /-- After `matrixMove_0`, whose destination received `vs`. -/
  | movDone (vs : List Value)
  /-- `stmatrix` at `matrixStore_0`, before the matrix event. -/
  | stMx
  /-- `stmatrix` at `matrixStore_0`, after receiving the row `row`. -/
  | stWr (row : List (Option Byte))
  /-- After `matrixStore_0`. -/
  | stDone
  /-- `ldmatrix … .trans` at `matrixLoad_36`, before the row read. -/
  | ltRd
  /-- `ldmatrix … .trans` at `matrixLoad_36`, after reading the row `row`. -/
  | ltMx (row : List (Option Byte))
  /-- After `matrixLoad_36`, whose destinations received `vs`. -/
  | ltDone (vs : List Value)

/-- The program counter of each state. -/
def pcOf : Site → Nat
  | .ldRd | .ldMx _ => Flow.matrixLoad_1
  | .ldDone _ => Flow.matrixLoad_1 + 1
  | .mma => Flow.warpMma_0
  | .mmaDone _ => Flow.warpMma_0 + 1
  | .mov => Flow.matrixMove_0
  | .movDone _ => Flow.matrixMove_0 + 1
  | .stMx | .stWr _ => Flow.matrixStore_0
  | .stDone => Flow.matrixStore_0 + 1
  | .ltRd | .ltMx _ => Flow.matrixLoad_36
  | .ltDone _ => Flow.matrixLoad_36 + 1

/-- The source registers of the MMA at `warpMma_0`: A (4), B (2) and the zero accumulator. -/
def mmaLive : List Nat := [1162, 1163, 1164, 1165, 1166, 1167, 1168]

/-- The register facts of each state, from a value table `val`. -/
def factsOf (val : Nat → Value) : Site → List (Nat × Value)
  | .ldRd | .ldMx _ => factsFrom [1159] val
  | .ldDone vs => vecFacts [1171, 1172, 1173, 1174] vs (factsFrom [1159] val)
  | .mma => factsFrom mmaLive val
  | .mmaDone vs => vecFacts [1188, 1189, 1190, 1191] vs (factsFrom mmaLive val)
  | .mov => factsFrom [1575] val
  | .movDone vs => vecFacts [1583] vs (factsFrom [1575] val)
  | .stMx | .stWr _ | .stDone => factsFrom [1672, 1673, 1674, 1675, 1676] val
  | .ltRd | .ltMx _ => factsFrom [1682] val
  | .ltDone vs => vecFacts [1687, 1688, 1689, 1690] vs (factsFrom [1682] val)

/-- The transitions: each state records what its event returned, and stops where the model
faults. -/
def next : Site → Event → Option (Option Site)
  | .ldRd, e => match e.kind with
    | .rd _ bs => if bs.all Option.isSome then some (some (.ldMx bs)) else none
    | _ => none
  | .ldMx _, e => match e.kind with
    | .matrix _ _ recv => match matrixVals 32 4 recv with
      | .ok vs => some (some (.ldDone vs))
      | .error _ => none
    | _ => none
  | .mma, e => match e.kind with
    | .matrix _ _ recv => match matrixVals 32 4 recv with
      | .ok vs => some (some (.mmaDone vs))
      | .error _ => none
    | _ => none
  | .mov, e => match e.kind with
    | .matrix _ _ recv => match matrixVals 32 1 recv with
      | .ok vs => some (some (.movDone vs))
      | .error _ => none
    | _ => none
  | .stMx, e => match e.kind with
    | .matrix _ _ recv =>
      if recv.length = 16 ∧ recv.all Option.isSome then some (some (.stWr recv)) else none
    | _ => none
  | .stWr _, e => match e.kind with
    | .wr _ _ => some (some .stDone)
    | _ => none
  | .ltRd, e => match e.kind with
    | .rd _ bs => if bs.all Option.isSome then some (some (.ltMx bs)) else none
    | _ => none
  | .ltMx _, e => match e.kind with
    | .matrix _ _ recv => match matrixVals 32 4 recv with
      | .ok vs => some (some (.ltDone vs))
      | .error _ => none
    | _ => none
  | _, _ => none

/-- The toy machine on the FlashKDA kernel, for thread `g` of launch `L`. -/
def code (L : Launch) (g : Nat) (val : Nat → Value) : Code Decoded.kernel [] L g where
  D := Site
  init := .ldRd
  pc := pcOf
  facts := factsOf val
  sub := fun
    | .ldMx _ | .stWr _ | .ltMx _ => 1
    | _ => 0
  acc := fun
    | .ldMx row | .stWr row | .ltMx row => rowVals row
    | _ => []
  inv := fun _ => True
  next := next

variable {L : Launch} {g : Nat} {val : Nat → Value}

/-! ## Step combinators -/

/-- `ldmatrix`, sub-step 0: the row read, recorded in the next state's accumulator. -/
theorem step_ldRd : (code L g val).StepOk .ldRd :=
  step_ldmatrix_rd (nv := fun bs => some (some (.ldMx bs))) Flow.code_matrixLoad_1 rfl rfl
    (laneOf_lt_rows rfl) rfl
    (fun x bs _ hall => by simp [code, next, hall])
    (fun x bs _ hall => .inl (by simp [code, next, hall]))
    (fun _ _ _ => by simp)
    (fun bs d' _ _ h => by
      cases h
      exact ⟨rfl, rfl, rfl, rfl, fun h => h⟩)

/-- `ldmatrix`, sub-step 1: the matrix event, whose four rebuilt values are recorded. -/
theorem step_ldMx (row : List (Option Byte)) : (code L g val).StepOk (.ldMx row) :=
  step_ldmatrix_mx (nv := fun vs => some (some (.ldDone vs))) Flow.code_matrixLoad_1 rfl rfl
    Nat.one_ne_zero (by decide)
    (fun own recv vs h => by
      have h' : matrixVals 32 4 recv = .ok vs := h
      simp [code, next, h'])
    (fun own recv f h => .inl (by
      have h' : matrixVals 32 4 recv = .error f := h
      simp [code, next, h']))
    (fun _ _ => by simp)
    (fun vs d' _ h => by
      cases h
      exact ⟨fun _ => ⟨0, Seg.refl _ _⟩, rfl, rfl, fun h => h⟩)

/-- `ldmatrix … .trans`, sub-step 0. -/
theorem step_ltRd : (code L g val).StepOk .ltRd :=
  step_ldmatrix_rd (nv := fun bs => some (some (.ltMx bs))) Flow.code_matrixLoad_36 rfl rfl
    (laneOf_lt_rows rfl) rfl
    (fun x bs _ hall => by simp [code, next, hall])
    (fun x bs _ hall => .inl (by simp [code, next, hall]))
    (fun _ _ _ => by simp)
    (fun bs d' _ _ h => by
      cases h
      exact ⟨rfl, rfl, rfl, rfl, fun h => h⟩)

/-- `ldmatrix … .trans`, sub-step 1. -/
theorem step_ltMx (row : List (Option Byte)) : (code L g val).StepOk (.ltMx row) :=
  step_ldmatrix_mx (nv := fun vs => some (some (.ltDone vs))) Flow.code_matrixLoad_36 rfl rfl
    Nat.one_ne_zero (by decide)
    (fun own recv vs h => by
      have h' : matrixVals 32 4 recv = .ok vs := h
      simp [code, next, h'])
    (fun own recv f h => .inl (by
      have h' : matrixVals 32 4 recv = .error f := h
      simp [code, next, h']))
    (fun _ _ => by simp)
    (fun vs d' _ h => by
      cases h
      exact ⟨fun _ => ⟨0, Seg.refl _ _⟩, rfl, rfl, fun h => h⟩)

/-- `mma.sync`: one matrix event, whose four rebuilt values are recorded. -/
theorem step_mma : (code L g val).StepOk .mma :=
  step_matrix_sel (w := 32) (nv := fun vs => some (some (.mmaDone vs))) Flow.code_warpMma_0
    (by simp) rfl (by decide)
    (fun own recv vs h => by
      have h' : matrixVals 32 4 recv = .ok vs := h
      simp [code, next, h'])
    (fun own recv f h => .inl (by
      have h' : matrixVals 32 4 recv = .error f := h
      simp [code, next, h']))
    (fun _ _ => by simp)
    (fun vs d' _ h => by
      cases h
      exact ⟨fun _ => ⟨0, Seg.refl _ _⟩, rfl, rfl, fun h => h⟩)

/-- `movmatrix`: one matrix event, whose rebuilt value is recorded. -/
theorem step_mov : (code L g val).StepOk .mov :=
  step_matrix_sel (w := 32) (nv := fun vs => some (some (.movDone vs))) Flow.code_matrixMove_0
    (by simp) rfl (by decide)
    (fun own recv vs h => by
      have h' : matrixVals 32 1 recv = .ok vs := h
      simp [code, next, h'])
    (fun own recv f h => .inl (by
      have h' : matrixVals 32 1 recv = .error f := h
      simp [code, next, h']))
    (fun _ _ => by simp)
    (fun vs d' _ h => by
      cases h
      exact ⟨fun _ => ⟨0, Seg.refl _ _⟩, rfl, rfl, fun h => h⟩)

/-- `stmatrix`, sub-step 0: the matrix event, whose 16 received bytes are recorded. -/
theorem step_stMx : (code L g val).StepOk .stMx :=
  step_stmatrix_mx (nv := fun recv => some (some (.stWr recv))) Flow.code_matrixStore_0 rfl rfl
    (laneOf_lt_rows rfl) rfl
    (fun own recv hl hall => by simp [code, next, hl, hall])
    (fun own recv h => .inl (by
      simp only [code, next]
      exact ite_eq_right h))
    (fun _ _ _ => by simp)
    (fun recv d' _ _ h => by
      cases h
      exact ⟨rfl, rfl, rfl, rfl, fun h => h⟩)

/-- `stmatrix`, sub-step 1: the row write. -/
theorem step_stWr (row : List (Option Byte)) : (code L g val).StepOk (.stWr row) :=
  step_stmatrix_wr (dn := .stDone) Flow.code_matrixStore_0 rfl rfl Nat.one_ne_zero
    (fun x bs => by simp [code, next])
    ⟨fun _ => ⟨0, Seg.refl _ _⟩, rfl, rfl, fun h => h⟩

/-! ## Shapes -/

/-- The MMA of the kernel: `m16n8k16.row.col.f32.bf16.bf16.f32`. -/
def mmaSpec : MmaSpec :=
  { m := 16, n := 8, k := 16,
    types := { a := .float .bf16, b := .float .bf16, c := .float .f32, d := .float .f32 } }

/-- The shape of the event of each site, for row addresses `a` (the value of the address
registers) and source values `val`. -/
def Ev (L : Launch) (g : Nat) (val : Nat → Value) (a : Nat) : Site → Event → Prop
  | .ldRd, e => ∃ bs : List (Option Byte), bs.length = 16 ∧
      e = ⟨Flow.matrixLoad_1, .rd { loc := ⟨.shared, g / L.block, a⟩, size := 16 } bs⟩
  | .ldMx row, e => ∃ recv,
      e = ⟨Flow.matrixLoad_1, .matrix (.move ⟨false, .m8n8, 4, false, .b16⟩) row recv⟩
  | .mma, e => ∃ recv, e = ⟨Flow.warpMma_0, .matrix (.mma mmaSpec)
      (ownBytes ([1162, 1163, 1164, 1165, 1166, 1167, 1168, 1168, 1168, 1168].map val)) recv⟩
  | .mov, e => ∃ recv, e = ⟨Flow.matrixMove_0, .matrix .transpose (ownBytes [val 1575]) recv⟩
  | .stMx, e => ∃ recv, e = ⟨Flow.matrixStore_0, .matrix (.move ⟨true, .m8n8, 4, false, .b16⟩)
      (ownBytes ([1673, 1674, 1675, 1676].map val)) recv⟩
  | .stWr row, e => e = ⟨Flow.matrixStore_0,
      .wr { loc := ⟨.shared, g / L.block, a⟩, size := 16 } row.reduceOption⟩
  | _, _ => True

variable {a : Nat}

/-- The row read of `ldmatrix`, at the address its register holds. -/
theorem shape_ldRd (hblk : L.block % 32 = 0) (hv : val 1159 = b32 a) (ha : a < 2 ^ 32)
    (hal : a % 16 = 0) : (code L g val).ShapeAt (Ev L g val a) .ldRd := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_matrixLoad_1)
  have hF : Holds t.regs (factsFrom [1159] val) := hat.2.2.2.2
  refine shape_ldmatrix_rd hf hat.2.1 rfl rfl hblk rfl (laneOf_lt_rows rfl)
    (matrixRowLoc_b32 rfl rfl (hv ▸ regs_of_factsFrom hF (by decide)) ha hal)
    fun bs hl => ⟨bs, hl, rfl⟩

/-- The matrix event of `ldmatrix` contributes the row read (all of whose bytes are known). -/
theorem shape_ldMx (hblk : L.block % 32 = 0) {row : List (Option Byte)}
    (hall : row.all Option.isSome = true) :
    (code L g val).ShapeAt (Ev L g val a) (.ldMx row) := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_matrixLoad_1)
  exact shape_ldmatrix_mx hf hat.2.1 rfl rfl hblk rfl (laneOf_lt_rows rfl) hat.2.2.1 hall
    fun recv => ⟨recv, rfl⟩

/-- The matrix event of `mma.sync` contributes the bytes of its ten source operands. -/
theorem shape_mmaSite (hblk : L.block % 32 = 0) (hb : ∀ r, (val r).bytes = 4) :
    (code L g val).ShapeAt (Ev L g val a) .mma := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpMma_0)
  have hF : Holds t.regs (factsFrom mmaLive val) := hat.2.2.2.2
  exact shape_mma hf rfl rfl hblk
    (mmaOwn_srcs rfl rfl rfl (regs_of_live hF (by decide)) fun r _ => hb r)
    fun recv => ⟨recv, rfl⟩

/-- The matrix event of `movmatrix` contributes the bytes of its source register. -/
theorem shape_movSite (hblk : L.block % 32 = 0) (hb : ∀ r, (val r).bytes = 4) :
    (code L g val).ShapeAt (Ev L g val a) .mov := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_matrixMove_0)
  have hF : Holds t.regs (factsFrom [1575] val) := hat.2.2.2.2
  exact shape_movmatrix hf rfl rfl rfl hblk
    (regBytes_srcs rfl (regs_of_live hF (by decide)) fun r _ => hb r)
    fun recv => ⟨recv, rfl⟩

/-- The matrix event of `stmatrix` contributes the bytes of its four source registers. -/
theorem shape_stMx (hblk : L.block % 32 = 0) (hb : ∀ r, (val r).bytes = 4) :
    (code L g val).ShapeAt (Ev L g val a) .stMx := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_matrixStore_0)
  have hF : Holds t.regs (factsFrom [1672, 1673, 1674, 1675, 1676] val) := hat.2.2.2.2
  exact shape_stmatrix_mx hf hat.2.1 rfl rfl hblk rfl
    (regBytes_srcs rfl (regs_of_live hF (by decide)) fun r _ => hb r)
    fun recv => ⟨recv, rfl⟩

/-- The row write of `stmatrix`: the received bytes, at the address its register holds. -/
theorem shape_stWr (hblk : L.block % 32 = 0) (hv : val 1672 = b32 a) (ha : a < 2 ^ 32)
    (hal : a % 16 = 0) (row : List (Option Byte)) :
    (code L g val).ShapeAt (Ev L g val a) (.stWr row) := by
  intro t ins e o hat _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_matrixStore_0)
  have hF : Holds t.regs (factsFrom [1672, 1673, 1674, 1675, 1676] val) := hat.2.2.2.2
  exact shape_stmatrix_wr hf hat.2.1 rfl rfl hblk rfl hat.2.2.1
    (matrixRowLoc_b32 rfl rfl (hv ▸ regs_of_factsFrom hF (by decide)) ha hal) rfl

end
end PTX.Tests.MatrixSteps
