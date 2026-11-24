-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Clock
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Glue

@[expose] public section

/-! # The times of the output warp's states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The output warp -/

namespace Out

/-- The sites whose event is a warp collective. -/
def coll (s : Epilogue.Site) : Bool := s.shfl || s.ballot

/-- The sites of the second pass. -/
def late : Epilogue.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .exit l => l
  | _ => false

/-- The sites between the choice of the tile and the second pass. -/
def tail : Epilogue.Site → Bool
  | .q0 | .q1 | .ready _ | .store _ _ | .commit _ | .drain _ | .free _ => true
  | _ => false

/-- The tail's offsets: the request's two reads, then per stage its ready poll, four stores, the
commit, the read wait and the free. -/
def tailOff : Epilogue.Site → Nat
  | .q1 => 1
  | .ready st => 2 + 8 * st.val
  | .store st b => 3 + 8 * st.val + b.val
  | .commit st => 7 + 8 * st.val
  | .drain st => 8 + 8 * st.val
  | .free st => 9 + 8 * st.val
  | _ => 0

/-- **The time of an output-warp state** with ghost counts `n`. -/
def time (p : Params) (d : Epilogue.D) (n : Cls → Nat) : Nat :=
  if d.site = .start then scanBase
  else if tail d.site then tailBase p + tailOff d.site
  else passTime (if late d.site then endBase p else scanBase) (collCount n) (coll d.site)

theorem tailOff_lt (s : Epilogue.Site) : tailOff s < 18 := by
  cases s <;> simp only [tailOff] <;> omega

/-- A tail state is in the tail's slot. -/
theorem time_tail {p : Params} {d : Epilogue.D} {n : Cls → Nat} (h : tail d.site = true) :
    tailBase p ≤ time p d n ∧ time p d n < endBase p := by
  have := tailOff_lt d.site
  have hs : d.site ≠ .start := fun hs => by simp [hs, tail] at h
  simp only [time, h, hs, ↓reduceIte, endBase, span]
  omega

/-- The ready poll of stage `st`. -/
theorem time_ready {p : Params} {d : Epilogue.D} {n : Cls → Nat} {st : Fin 2}
    (h : d.site = .ready st) : time p d n = tailBase p + 2 + 8 * st.val := by
  simp only [time, h, tail, tailOff, reduceCtorEq, ↓reduceIte]
  omega

end Out


namespace Out

/-- The ballot of the pass before a site: at the two reads after it. -/
def ballots (s : Epilogue.Site) : Nat :=
  match s with | .pre _ | .tiles _ => 1 | _ => 0

end Out

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
