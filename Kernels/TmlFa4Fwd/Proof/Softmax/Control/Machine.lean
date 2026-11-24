-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Lemmas.Flow.CodeU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

noncomputable section

/-- The scan, request length, loop counters and barrier parities. -/
structure V where
  sc : Epilogue.D := { site := .start }
  ukw : BitVec 64 := 0
  nb : BitVec 64 := 0
  bt : BitVec 64 := 0
  bpar : BitVec 64 := 0
  spar : BitVec 64 := 0
  ppar : BitVec 64 := 0
  pl : BitVec 64 := 0

/-- The accumulator mirrors the PTX vector-load microstate until its final element. -/
structure D where
  site : Site
  v : V
  k : Fin 4 := 0
  acc : List Value := []

def V.scheduler (v : V) : Softmax.V :=
  { sc := v.sc, ukw := v.ukw, nb := v.nb, bt := v.bt, bpar := v.bpar,
    spar := v.spar, ppar := v.ppar, pl := v.pl }

def D.scheduler (d : D) : Softmax.D := ⟨d.site, d.v.scheduler, d.k, d.acc⟩

/-- Reuse scheduler calculations and site tables on the retained control fields. -/
instance : Coe D Softmax.D := ⟨D.scheduler⟩

def erase (d : Softmax.D) : D :=
  ⟨d.site, ⟨d.v.sc, d.v.ukw, d.v.nb, d.v.bt, d.v.bpar, d.v.spar, d.v.ppar, d.v.pl⟩,
    d.k, d.acc⟩

theorem erase_scheduler (d : D) : erase d.scheduler = d := rfl

/-- A read advances on every payload. A failed rebuild faults in the concrete continuation,
so the choice of a placeholder accumulator word then has no bearing on subsequent events. -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .sld r c => match e.kind with
    | .tc (.ld ..) => match r with
      | .plain => some (some ⟨.sldw c, d.v, 1, []⟩)
      | r => some (some ⟨if c.val = 3 then afterLoads r else .sld r (c + 1), d.v, 0, []⟩)
    | _ => none
  | .bld b c => match e.kind with
    | .rd _ bs =>
      if d.k.val < 3 then
        let word := (rebuild 3 bs).toOption.getD (.bits 32 0)
        some (some { d with k := d.k + 1, acc := d.acc ++ [word] })
      else some (some ⟨if c.val = 15 then .fence b else .bld b (c + 1), d.v, 0, []⟩)
    | _ => none
  | _ => (Softmax.succ p L g d.scheduler e).map (Option.map erase)

def Inv (d : D) : Prop :=
  match d.site with
  | .bld _ _ => d.acc.length = d.k.val
  | _ => (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc

@[reducible] def code (p : Params) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g where
  D := D
  init := ⟨.setmax, {}, 0, []⟩
  pc := (·.site.pc)
  facts := fun d => Softmax.facts p L g d.scheduler
  sub := (·.k.val)
  acc := (·.acc)
  inv := Inv
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
