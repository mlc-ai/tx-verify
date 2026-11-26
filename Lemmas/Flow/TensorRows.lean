-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorCoords
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The origin and rows of a gather4 load

A proof tool. A gather4 tensor load whose five coordinate operands are registers holding 32-bit
values records the first as its box's origin and the other four as its row coordinates
(`tensorLoadCopy_rows`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A 32-bit register reads as its low 32 bits. -/
theorem readBits_bits32 {L : Launch} {g : Nat} {t : TState} {r : Nat} {x : BitVec 64}
    (hr : t.regs r = some (.bits 32 x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure]

/-- **A gather4 load's origin and rows** are its coordinate registers' 32-bit words. -/
theorem tensorLoadCopy_rows {L : Launch} {g : Nat} {t : TState} {cl grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {r0 r1 r2 r3 r4 : Nat} {x0 x1 x2 x3 x4 : BitVec 64}
    {a : Nat} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t cl grp dst off map
      [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4] mb moff .fourRows = .ok (a, s))
    (h0 : t.regs r0 = some (.bits 32 x0)) (h1 : t.regs r1 = some (.bits 32 x1))
    (h2 : t.regs r2 = some (.bits 32 x2)) (h3 : t.regs r3 = some (.bits 32 x3))
    (h4 : t.regs r4 = some (.bits 32 x4)) :
    s.origin 0 = (BitVec.ofNat 32 (truncBits 32 x0).toNat).toInt ∧
      s.rows = some (fun j : Fin 4 => (BitVec.ofNat 32 (truncBits 32
        (if j.val = 0 then x1 else if j.val = 1 then x2 else if j.val = 2 then x3
          else x4)).toNat).toInt) := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    List.mapM_cons, List.mapM_nil, readBits_bits32 h0, readBits_bits32 h1, readBits_bits32 h2,
    readBits_bits32 h3, readBits_bits32 h4] at h
  rcases hm : tensorMap L g t map [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4] .fourRows with
    f | ⟨a'', outer, d⟩ <;> rw [hm] at h
  · cases h
  rcases hd : sharedEffAddr L g t cl dst off with f | dl <;> simp only [hd] at h
  · cases h
  all_goals repeat' (split at h <;> (try (cases h; done)))
  all_goals cases h
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | (simp; done)
    | (simp only [TensorMode.rowCoordinates, Option.some.injEq]; funext j; fin_cases j <;> simp)

end

end PTX.Flow
