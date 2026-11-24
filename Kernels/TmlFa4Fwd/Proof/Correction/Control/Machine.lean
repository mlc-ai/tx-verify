-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Live
public import Lemmas.Flow.CodeU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow
open Epilogue (i32 sub32 shl)

noncomputable section

/-- Scheduler words, the trip counter and the two ballot results. -/
structure V where
  sc : Epilogue.D := { site := .start }
  ukw : BitVec 64 := 0
  trip : BitVec 64 := 0
  b0 : BitVec 64 := 0
  b1 : BitVec 64 := 0

structure D where
  site : Site
  v : V
  k : Fin 4 := 0

/-- Supply the common scheduler arithmetic with its control inputs. -/
def V.scheduler (v : V) : Correction.V :=
  { sc := v.sc, ukw := v.ukw, trip := v.trip, b0 := v.b0, b1 := v.b1 }

def D.scheduler (d : D) : Correction.D := ⟨d.site, d.v.scheduler, d.k⟩

/-- Reuse scheduler calculations and site tables on the retained control fields. -/
instance : Coe D Correction.D := ⟨D.scheduler⟩

def erase (d : Correction.D) : D :=
  ⟨d.site, ⟨d.v.sc, d.v.ukw, d.v.trip, d.v.b0, d.v.b1⟩, d.k⟩

abbrev live (d : D) := liveAt d.site

def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let v := d.v.scheduler
  match d.site with
  | .rbar _ | .rscale _ | .rvote _ | .rwait _ | .rarr _ _ | .rld _ _ | .rldw _ _ | .rst _ _ =>
    valuesRound v L g ++ valuesTile p L g v
  | .farr0 | .fbar _ | .fsum _ | .fmax _ | .farr _ | .fw _ _ | .fence _ | .fdone _ _
  | .fld _ _ | .fwl _ _ | .fst _ _ _ =>
    finalControlRegs L g ++ fAddrs L g 0 ++ fAddrs L g 1 ++ valuesTile p L g v
  | .lse _ =>
    [(7491, .bits 64 (lseAddr p L g v)), (7077, .bits 32
      (sub32 (sub32 v.sc.c1 v.sc.c0) (shl (rowOff p L g v.sc) 8)))] ++
      finalControlRegs L g ++ valuesTile p L g v
  | _ => Correction.values p L g d.scheduler

def valueOf (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((valuesRole p L g).lookup r).getD
    (((valuesStart p L g).lookup r).getD (.pred false)))

abbrev facts (p : Params) (L : Launch) (g : Nat) (d : D) :=
  factsFrom (live d) (valueOf p L g d)

def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .rscale st => match e.kind with
    | .rd .. => some (some ⟨.rvote st, d.v, 0⟩)
    | _ => none
  | .fsum st => match e.kind with
    | .rd .. => some (some ⟨.fmax st, d.v, 0⟩)
    | _ => none
  | .fmax st => match e.kind with
    | .rd .. => some (some ⟨.farr st, d.v, 0⟩)
    | _ => none
  | .rld st c => match e.kind with
    | .tc (.ld ..) => some (some ⟨.rldw st c, d.v, 1⟩)
    | _ => none
  | .fld st j => match e.kind with
    | .tc (.ld ..) => some (some ⟨.fwl st j, d.v, 0⟩)
    | _ => none
  | .fdone 1 1 => some (some (erase (afterFinal p L g d.scheduler)))
  | .lse 0 => some (some (erase (afterLse p L g d.scheduler 0)))
  | _ => (Correction.succ p L g d.scheduler e).map (Option.map erase)

@[reducible] def code (p : Params) (L : Launch) (g : Nat) : Code kernel Assumptions.all L g where
  D := D
  init := ⟨.setmax, {}, 0⟩
  pc := (·.site.pc)
  sub := (·.k.val)
  inv := fun d => d.k = 0 ∨ d.site.midOk d.k
  facts := facts p L g
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
