-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.ClassPcs
public import Lemmas.Kernel.Safety.GuardKey

/-! # Sites at the positions of an instruction class; keyed polls

`site_pcs` decides which sites of a site type sit at listed positions, with constructors that
take `Fin` and `Bool` parameters. `PollObjAt.of_uniform`: one object per position is the case of
a constant key. -/

namespace PTX.Tests.SitePcs
open PTX PTX.Frame

inductive Site
  | a
  | b (i : Fin 3)
  | c (i : Fin 2) (x : Bool)
  deriving DecidableEq

def Site.pc : Site → Nat
  | .a => 4
  | .b i => 10 + i.val
  | .c i x => 20 + 2 * i.val + (if x then 1 else 0)

example : ∀ s : Site, s.pc ∈ [4, 11, 23] → s ∈ [.a, .b 1, .c 1 true] := by site_pcs

example : ∀ s : Site, s.pc ∈ [5, 13] → s ∈ ([] : List Site) := by site_pcs

example {L : Launch} {X : Execution} (h : PollObjUniform L X) : PollObjAt L X (fun i => i.2) :=
  PollObjAt.of_uniform h _

end PTX.Tests.SitePcs
