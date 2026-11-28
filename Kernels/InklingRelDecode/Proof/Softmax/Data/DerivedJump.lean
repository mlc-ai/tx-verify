-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedTable
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The four runs as jumps of the table

The facts of `derV` hold along every local path from the barrier or the last preload to the
loop's first stop (`tk_rtg`): each run's start facts are read from `derV` below the newer runs'
facts (`holds_tail`), its end facts are put on top of it (`holds_head`, `holds_up`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

def kEn : List Nat := [1, 2, 496, 798]
def kDv : List Nat := [498, 805]
def kE8 : List Nat := [1956]
def kNg : List Nat := [499]
def kIe : List Nat := [810, 811]
def kIo : List Nat := (List.range 33).map (1960 + ·)

theorem kEn_eq (V : Nat → Value) : (Gen.en_facts1 V).map Prod.fst = kEn := rfl
theorem kDv_eq (V : Nat → Value) : (Gen.dv_facts1 V).map Prod.fst = kDv := rfl
theorem kE8_eq (V : Nat → Value) : (Gen.e8_facts1 V).map Prod.fst = kE8 := rfl
theorem kNg_eq (V : Nat → Value) : (Gen.ng_facts1 V).map Prod.fst = kNg := rfl
theorem kIe_eq (V : Nat → Value) : (Gen.ie_facts1 V).map Prod.fst = kIe := rfl
theorem kIo_eq (V : Nat → Value) : (Gen.io_facts3 V).map Prod.fst = kIo := rfl

variable {R : Nat → Option Value} {live : List Nat}

/-- Read below the runs after the `k`-th: none of the later runs' registers is among the live
ones. -/
abbrev Below (live k : List Nat) : Prop := live.all (fun r => !k.contains r) = true

/-- Read below the last run: its registers are not among the live ones. -/
theorem to5 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo) :
    Holds R (factsFrom live (lookupD (G5 e L g))) :=
  holds_tail (kIo_eq _) h h1

theorem to4 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo)
    (h2 : Below live kIe) : Holds R (factsFrom live (lookupD (G4 e L g))) :=
  holds_tail (kIe_eq _) (to5 h h1) h2

theorem to3 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo)
    (h2 : Below live kIe) (h3 : Below live kNg) :
    Holds R (factsFrom live (lookupD (G3 e L g))) :=
  holds_tail (kNg_eq _) (to4 h h1 h2) h3

theorem to2 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo)
    (h2 : Below live kIe) (h3 : Below live kNg) (h4 : Below live kE8) :
    Holds R (factsFrom live (lookupD (G2 e L g))) :=
  holds_tail (kE8_eq _) (to3 h h1 h2 h3) h4

theorem to1 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo)
    (h2 : Below live kIe) (h3 : Below live kNg) (h4 : Below live kE8) (h5 : Below live kDv) :
    Holds R (factsFrom live (lookupD (G1 e L g))) :=
  holds_tail (kDv_eq _) (to2 h h1 h2 h3 h4) h5

theorem to0 (h : Holds R (factsFrom live (derV e L g))) (h1 : Below live kIo)
    (h2 : Below live kIe) (h3 : Below live kNg) (h4 : Below live kE8) (h5 : Below live kDv)
    (h6 : Below live kEn) : Holds R (factsFrom live (lookupD (G0 e L g))) :=
  holds_tail (kEn_eq _) (to1 h h1 h2 h3 h4 h5) h6

/-- Put the runs' facts on top of `derV`: each run's registers read through the newer runs. -/
theorem up6 {V : Nat → Value} (h : Holds R (Gen.io_facts3 V)) (hv : V = lookupD (G5 e L g))
    (hl : live.all (fun r => kIo.contains r) = true) : Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_head (kIo_eq _) h hl

theorem up5 {V : Nat → Value} (h : Holds R (Gen.ie_facts1 V)) (hv : V = lookupD (G4 e L g))
    (hl : live.all (fun r => kIe.contains r) = true) (h1 : Below live kIo) :
    Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_up (kIo_eq _) (holds_head (kIe_eq _) h hl) h1

theorem up4 {V : Nat → Value} (h : Holds R (Gen.ng_facts1 V)) (hv : V = lookupD (G3 e L g))
    (hl : live.all (fun r => kNg.contains r) = true) (h1 : Below live kIo) (h2 : Below live kIe) :
    Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_up (kIo_eq _) (holds_up (kIe_eq _) (holds_head (kNg_eq _) h hl) h2) h1

theorem up3 {V : Nat → Value} (h : Holds R (Gen.e8_facts1 V)) (hv : V = lookupD (G2 e L g))
    (hl : live.all (fun r => kE8.contains r) = true) (h1 : Below live kIo) (h2 : Below live kIe)
    (h3 : Below live kNg) : Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_up (kIo_eq _) (holds_up (kIe_eq _) (holds_up (kNg_eq _)
    (holds_head (kE8_eq _) h hl) h3) h2) h1

theorem up2 {V : Nat → Value} (h : Holds R (Gen.dv_facts1 V)) (hv : V = lookupD (G1 e L g))
    (hl : live.all (fun r => kDv.contains r) = true) (h1 : Below live kIo) (h2 : Below live kIe)
    (h3 : Below live kNg) (h4 : Below live kE8) : Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_up (kIo_eq _) (holds_up (kIe_eq _) (holds_up (kNg_eq _) (holds_up (kE8_eq _)
    (holds_head (kDv_eq _) h hl) h4) h3) h2) h1

theorem up1 {V : Nat → Value} (h : Holds R (Gen.en_facts1 V)) (hv : V = lookupD (G0 e L g))
    (hl : live.all (fun r => kEn.contains r) = true) (h1 : Below live kIo) (h2 : Below live kIe)
    (h3 : Below live kNg) (h4 : Below live kE8) (h5 : Below live kDv) :
    Holds R (factsFrom live (derV e L g)) := by
  subst hv
  exact holds_up (kIo_eq _) (holds_up (kIe_eq _) (holds_up (kNg_eq _) (holds_up (kE8_eq _)
    (holds_up (kDv_eq _) (holds_head (kEn_eq _) h hl) h5) h4) h3) h2) h1

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
