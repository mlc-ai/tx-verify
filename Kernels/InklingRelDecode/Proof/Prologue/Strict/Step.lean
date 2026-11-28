-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Wf
public import Lemmas.Flow.StepsQ
public import Lemmas.Flow.StepsQLdW
import Lemmas.Flow.Next

@[expose] public section

/-! # The strict steps of the prologue's sites (`StepForQ` of the value machine) -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem typed_nil' {t : TState} : Typed ([] : Env) t := fun r tg h => by simp at h

/-- **The setmaxnreg** strictly steps to the first request load. -/
theorem step_sMax (d : Data.D) (hs : d.c.site = .sMax) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, v⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨⟨rfl, rfl, rfl⟩, hpay⟩ := hinv
  refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨⟨.sMax, b32 0, b32 0, b32 0, won, bcast⟩, v⟩)
    (dn := ⟨⟨.ld 0, b32 0, b32 0, b32 0, won, bcast⟩, v⟩) Flow.code_27
    (fun h => fires_next (by trivial) h) (fun _ => rfl) rfl rfl rfl rfl
    ⟨⟨rfl, rfl, rfl⟩, ⟨fun h => by change 41 ≤ 34 at h; omega,
      fun h => by change 130 ≤ 34 at h; omega⟩⟩
    (fun _ _ => typed_nil')
    (by change Code.afterWrites proQt 27 [] [] = true; decide +kernel)
    (dFacts_seg (pre := []) (sMax_span won bcast v)) e ins hat ⟨⟨rfl, rfl, rfl⟩, hpay⟩ hc hq hw hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
