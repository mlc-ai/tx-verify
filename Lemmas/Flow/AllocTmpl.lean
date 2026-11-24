-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The events of a Tensor Memory allocation

A proof tool. With its operands known, the allocation instruction fires at its first sub-step
the request for its columns (`tcAlloc_tmpl0`), and at its second the store of the returned
address into its destination word (`tcAlloc_tmpl1`). -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- The allocation's first sub-step: the request, continuing into the store on lane 0. -/
theorem tcAlloc_tmpl0 {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {grp : CtaGroup}
    {base nc : Nat} {a : Nat} (hb : L.block % 32 = 0) (hr : t.regs base = some (b32 a))
    (ha : a < 2 ^ 32) (h4 : a % 4 = 0) (hn : t.regs nc = some (b32 512)) (hs : t.sub = 0) :
    eventTmpl A L g t (.tcAlloc grp base 0 (.reg nc)) =
      .tc (.resource grp (some ⟨.shared, g / L.block, a⟩) (.alloc 512))
        (if laneOf L g = 0 then { t with sub := 1 } else next t) := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, readBits_b32' hn, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  simp [Tmem.validColumns, h4, hs, ofExec]

/-- The allocation's second sub-step: the store of the address, with its column open. -/
theorem tcAlloc_tmpl1 {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {grp : CtaGroup}
    {base nc : Nat} {a : Nat} (hb : L.block % 32 = 0)
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h4 : a % 4 = 0)
    (hn : t.regs nc = some (b32 512)) (hs : t.sub = 1) :
    eventTmpl A L g t (.tcAlloc grp base 0 (.reg nc)) =
      .tcAllocStore ⟨.shared, g / L.block, a⟩ { t with pc := t.pc + 1, sub := 0 } := by
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, readBits_b32' hn, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  simp [Tmem.validColumns, h4, hs, ofExec]

/-- The bytes of a 32-bit integer rebuild to it. -/
theorem rebuild_b32 (x : Nat) : rebuild 3 ((b32 x).toBytes.map some) = .ok (b32 x) := by
  have he : (b32 x).toBytes.map some =
      some (b32 x, 0) :: (List.range 3).map (fun k => some ((b32 x).byteAt (k + 1))) := by
    simp [Value.toBytes, Value.bytes, List.range_succ_eq_map, Value.byteAt, b32]
  rw [he]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [Value.bytes, b32], he.symm⟩]
  rfl

end

end PTX.Flow
