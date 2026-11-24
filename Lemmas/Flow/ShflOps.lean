-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Next

@[expose] public section

/-! # The operands of a fired shuffle and ballot

A proof tool for event-shape tables. A full-mask `shfl.sync` whose operands read `av`, `bv` and `cv`
fires a shuffle event with these operands, whatever value it receives (`fires_shflTmpl`); a
full-mask ballot of predicate `pv` fires a ballot of `pv` with the full mask
(`fires_voteTmpl`). -/

namespace PTX.Flow
open PTX

variable {L : Launch} {g : Nat} {t : TState}

/-- **A full-mask shuffle fires with the operands it reads.** -/
theorem fires_shflTmpl {mode : ShflMode} {d : Nat} {p : Option Nat} {a b c mask : Opnd}
    {pc : Nat} {e : Event} {o : Option TState} {av : Value} {bv cv m : BitVec 64}
    (hm : readBits L g t 32 mask = .ok m) (ha : readValue L g t 32 a = .ok av)
    (hb : readBits L g t 32 b = .ok bv) (hc : readBits L g t 32 c = .ok cv)
    (hfull : m.toNat = 2 ^ 32 - 1) (hblk : L.block % 32 = 0) (hav : av.bytes = 4)
    (hf : Fires pc (shflTmpl L g t mode d p a b c mask) e o) :
    ∃ recv ok, e = ⟨pc, .shfl mode av bv.toNat cv.toNat recv ok⟩ := by
  simp only [shflTmpl, hm, ha, hb, hc, hfull, hblk, hav, and_self, ↓reduceIte, Fires] at hf
  obtain ⟨recv, ok, h, -⟩ := hf
  exact ⟨recv, ok, h⟩

/-- **A full-mask ballot fires with the full mask and the predicate it reads.** -/
theorem fires_voteTmpl {d a : Nat} {neg : Bool} {mask : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {m : BitVec 64} {pv : Bool}
    (hm : readBits L g t 32 mask = .ok m) (hp : readPred L g t (.reg a) = .ok pv)
    (hfull : m.toNat = 2 ^ 32 - 1) (hblk : L.block % 32 = 0)
    (hf : Fires pc (voteTmpl L g t d a neg mask) e o) :
    ∃ b, e = ⟨pc, .vote (2 ^ 32 - 1) (pv != neg) b⟩ := by
  simp only [voteTmpl, hm, hp, hfull, hblk, and_self, ↓reduceIte, Fires] at hf
  obtain ⟨b, h, -⟩ := hf
  exact ⟨b, h⟩

end PTX.Flow
