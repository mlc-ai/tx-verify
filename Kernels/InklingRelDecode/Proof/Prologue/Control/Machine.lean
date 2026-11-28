-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
public import Lemmas.Flow.CodeU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- The initial zero moves precede the first loads. An elected initialization or
copy and a guarded query load can only be a site with its guard true. -/
def Inv (t : Nat) (d : D) : Prop :=
  match d.site with
  | .sMax | .ld 0 => d.first = b32 0 ∧ d.last = b32 0 ∧ d.seq = b32 0
  | .ld 1 => d.last = b32 0 ∧ d.seq = b32 0
  | .ld 2 => d.seq = b32 0
  | .init _ => t < 32 ∧ d.elected = true
  | .arr _ => t%128 = 0
  | .ptc _ _ => t%128 < 64 ∧ d.elected = true
  | .ldq j => queryOn t (j.val/16) d = true
  | _ => True

@[reducible] noncomputable def code (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := fun d => d.site.pc
  sub := fun d => d.site.sub
  facts := fun d => facts Q L g w d d.site.pc
  inv := Inv (g%L.block)
  next := next Q L g

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
