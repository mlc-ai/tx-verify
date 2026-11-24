-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.SiteTmpl

@[expose] public section

/-! # The local instructions of the code as pieces

Each local instruction the floating segments of the code execute, between the facts of one
abstract state at its `pc` and at the next (`factsAt`): the step writes the outcome of the
instruction on the values the facts give its sources (`SegD.one`, `SegD.two`). Where the outcome
can fault the piece carries its condition, and the thread is dead without it; a move of a value
that has its width (`val_bytes`) is a piece without condition. A use states that the abstract
state's table gives the written registers the outcome's value, which holds by evaluation. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {g : Nat} {d : D} {N : Nat}

/-- Facts of `d` at `pc`. -/
local notation "F" pc => factsAt P g pc d

theorem pc_unpack32 {lo hi w : Nat}
    (hc : kernel.code[N]? = some ⟨none, .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg w]⟩⟩)
    (hw : w ∈ Flow.live N) (hne : lo ≠ hi)
    (hlo : lo ∈ Flow.live (N + 1) → valueOf P g d lo = (splitValue 32 (valueOf P g d w)).1)
    (hhi : hi ∈ Flow.live (N + 1) → valueOf P g d hi = (splitValue 32 (valueOf P g d w)).2)
    (hcov : ∀ r ∈ Flow.live (N + 1), r = lo ∨ r = hi ∨ (r ≠ lo ∧ r ≠ hi ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((unpackE 32 (valueOf P g d w)).toBool = true) :=
  SegD.two hc rfl (fun _ ht => exec_unpackE coreMoves (by hooks_off) (.inl rfl)
      (reg_of ht.2.2.2.2 hw)) hne
    (fun _ hx => ⟨fun h => (hlo h).trans (by rw [unpackE_eq hx]),
      fun h => (hhi h).trans (by rw [unpackE_eq hx])⟩) hcov

theorem pc_unpack64 {lo hi w : Nat}
    (hc : kernel.code[N]? = some ⟨none, .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg w]⟩⟩)
    (hw : w ∈ Flow.live N) (hne : lo ≠ hi) (hok : (unpackE 64 (valueOf P g d w)).toBool = true)
    (hlo : lo ∈ Flow.live (N + 1) → valueOf P g d lo = (splitValue 64 (valueOf P g d w)).1)
    (hhi : hi ∈ Flow.live (N + 1) → valueOf P g d hi = (splitValue 64 (valueOf P g d w)).2)
    (hcov : ∀ r ∈ Flow.live (N + 1), r = lo ∨ r = hi ∨ (r ≠ lo ∧ r ≠ hi ∧ r ∈ Flow.live N)) :
    Seg kernel Prod L g 1 N (F N) (N + 1) (F (N + 1)) :=
  (SegD.two hc rfl (fun _ ht => exec_unpackE coreMoves (by hooks_off) (.inr rfl)
      (reg_of ht.2.2.2.2 hw)) hne
    (fun _ hx => ⟨fun h => (hlo h).trans (by rw [unpackE_eq hx]),
      fun h => (hhi h).trans (by rw [unpackE_eq hx])⟩) hcov).seg hok

theorem pc_widen {dd h : Nat}
    (hc : kernel.code[N]? = some ⟨none, .cvt (widenC dd (.reg h))⟩) (hh : h ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = okVal (b32 0) (widenE (valueOf P g d h)))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((widenE (valueOf P g d h)).toBool = true) :=
  SegD.one hc rfl (fun _ ht => exec_widenE ideal_widen decline (reg_of ht.2.2.2.2 hh))
    (fun _ hx hl => (hv hl).trans (okVal_of_ok hx)) hcov

theorem pc_fma {dd a c : Nat}
    (hc : kernel.code[N]? = some ⟨none, .float
      { fmaI .rn true with dsts := [some dd], srcs := [.reg a, .reg a, .reg c] }⟩)
    (ha : a ∈ Flow.live N) (hc' : c ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = okVal (b32 0)
      (floatE (fmaI .rn true) [valueOf P g d a, valueOf P g d a, valueOf P g d c]))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((floatE (fmaI .rn true) [valueOf P g d a, valueOf P g d a, valueOf P g d c]).toBool =
        true) :=
  SegD.one hc rfl (fun _ ht => exec_floatE_fma ideal_fma decline (.reg (reg_of ht.2.2.2.2 ha))
      (.reg (reg_of ht.2.2.2.2 ha)) (.reg (reg_of ht.2.2.2.2 hc')))
    (fun _ hx hl => (hv hl).trans (okVal_of_ok hx)) hcov

theorem pc_fmaImm {dd a : Nat}
    (hc : kernel.code[N]? = some ⟨none, .float
      { fmaI .rn true with dsts := [some dd], srcs := [.reg a, .reg a, .f32imm 0] }⟩)
    (ha : a ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = okVal (b32 0)
      (floatE (fmaI .rn true) [valueOf P g d a, valueOf P g d a, z0]))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((floatE (fmaI .rn true) [valueOf P g d a, valueOf P g d a, z0]).toBool = true) :=
  SegD.one hc rfl (fun _ ht => exec_floatE_fma ideal_fma decline (.reg (reg_of ht.2.2.2.2 ha))
      (.reg (reg_of ht.2.2.2.2 ha)) .imm)
    (fun _ hx hl => (hv hl).trans (okVal_of_ok hx)) hcov

theorem pc_mov {dd a : Nat}
    (hc : kernel.code[N]? = some ⟨none, .move ⟨.scalar, .int .b 32, [some dd], [.reg a]⟩⟩)
    (ha : a ∈ Flow.live N) (hb : (valueOf P g d a).bytes = 4)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = valueOf P g d a)
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    Seg kernel Prod L g 1 N (F N) (N + 1) (F (N + 1)) :=
  (SegD.one hc rfl (fun _ ht => exec_movE coreMoves (by hooks_off) (reg_of ht.2.2.2.2 ha))
    (fun _ hx hl => (hv hl).trans (movE_eq hx).symm) hcov).seg (movE_ok hb)

theorem pc_pack {dd a b : Nat}
    (hc : kernel.code[N]? = some ⟨none, .move ⟨.pack, .int .b 64, [some dd], [.reg a, .reg b]⟩⟩)
    (ha : a ∈ Flow.live N) (hb : b ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = joinValue (valueOf P g d a) (valueOf P g d b))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((packE (valueOf P g d a) (valueOf P g d b)).toBool = true) :=
  SegD.one hc rfl (fun _ ht => exec_packE coreMoves (by hooks_off) (reg_of ht.2.2.2.2 ha)
      (reg_of ht.2.2.2.2 hb))
    (fun _ hx hl => (hv hl).trans (packE_eq hx).symm) hcov

theorem pc_packOk {dd a b : Nat}
    (hc : kernel.code[N]? = some ⟨none, .move ⟨.pack, .int .b 64, [some dd], [.reg a, .reg b]⟩⟩)
    (ha : a ∈ Flow.live N) (hb : b ∈ Flow.live N)
    (ha4 : (valueOf P g d a).bytes = 4) (hb4 : (valueOf P g d b).bytes = 4)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = joinValue (valueOf P g d a) (valueOf P g d b))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    Seg kernel Prod L g 1 N (F N) (N + 1) (F (N + 1)) :=
  (pc_pack hc ha hb hv hcov).seg (packE_ok ha4 hb4)

theorem pc_mul {dd a b : Nat}
    (hc : kernel.code[N]? = some ⟨none, .float
      { mul2I .rz true with dsts := [some dd], srcs := [.reg a, .reg b] }⟩)
    (ha : a ∈ Flow.live N) (hb : b ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) → valueOf P g d dd = okVal (.pair (b32 0) (b32 0))
      (floatE (mul2I .rz true) [valueOf P g d a, valueOf P g d b]))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((floatE (mul2I .rz true) [valueOf P g d a, valueOf P g d b]).toBool = true) :=
  SegD.one hc rfl (fun _ ht => exec_floatE_mul2 ideal_mul2 decline (reg_of ht.2.2.2.2 ha)
      (reg_of ht.2.2.2.2 hb))
    (fun _ hx hl => (hv hl).trans (okVal_of_ok hx)) hcov

theorem pc_cvt {dd a b : Nat}
    (hc : kernel.code[N]? = some ⟨none, .cvt (cvtPairInstr dd a b)⟩)
    (ha : a ∈ Flow.live N) (hb : b ∈ Flow.live N)
    (hv : dd ∈ Flow.live (N + 1) →
      valueOf P g d dd = cvtPairV (valueOf P g d a) (valueOf P g d b))
    (hcov : ∀ r ∈ Flow.live (N + 1), r = dd ∨ (r ≠ dd ∧ r ∈ Flow.live N)) :
    SegD kernel Prod L g 1 N (F N) (N + 1) (F (N + 1))
      ((cvtPairE (valueOf P g d a) (valueOf P g d b)).toBool = true) :=
  SegD.one hc rfl (fun _ ht => exec_cvtPair ideal_cvt decline (reg_of ht.2.2.2.2 ha)
      (reg_of ht.2.2.2.2 hb))
    (fun _ hx hl => (hv hl).trans (cvtPairV_of_ok hx)) hcov

end
end PTX.Kernels.RmsNorm.Proof
