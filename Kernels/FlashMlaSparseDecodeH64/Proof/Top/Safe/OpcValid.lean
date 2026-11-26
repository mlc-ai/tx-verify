-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Result.RsOldAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OpcKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LdWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RsLdLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutLdLen

@[expose] public section

/-! # An accumulator load keeps warpgroup 0's trace valid

The load at a pc of `w0OPcs` (the rescale arm's and the epilogue's chunk loads) reads 64 words
that read as single-precision numbers (`rs_ld_word_at`, `old_ld_word_at`, from the words of the
events before the load in the tcgen05 order): the accumulator words of the block are valid. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The words of an accumulator load** (valid rows): 64 words that read as numbers. -/
theorem w0_pay_opc (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hw : warp L g < 4)
    (hpc : e.pc ∈ w0OPcs)
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (hEb : ∀ w, (w = (g, k) ∨ Relation.TransGen (TcMma.TcStep L X) w (g, k)) →
      MmaElemAt X w)
    :
    ∃ vals, w0TcVals e = some vals ∧ vals.length = 64 ∧
      ∃ O : Nat → ℝ, ∀ i < 64, Rd (vals.getD i (.pred false)) (O i) := by
  obtain ⟨a, vals, c, hk, ha, hpcc⟩ := wg0_opcKind_hub hp hX hFw he hub hpc
  have he0 := he
  obtain ⟨pc, kd⟩ := e
  simp only at hk hpc hpcc
  subst hk
  have hlen : vals.length = 64 := by
    rcases hpcc with h1 | h1
    · exact rsLdLen hp hX he0 rfl (by rw [h1]; fin_cases c <;> simp)
    · exact outLdLen hp hX he0 rfl (by rw [h1]; fin_cases c <;> simp)
  have hx : ∀ i < 64, ∃ x : ℝ, vals.getD i (.pred false) = .float .f32 x := by
    intro i hi
    have hil : i < vals.length := by omega
    rcases hpcc with h1 | h1
    · subst h1
      obtain ⟨r, h1r, hr⟩ := wg0_rldPlace hp hX hFw c he0 hw
      obtain ⟨-, x, hx, -⟩ := rs_ld_word_at hp hIn hX hFw hbelow hEb he0 hil h1r hr
      exact ⟨x, by rw [List.getD_eq_getElem?_getD, hx]; rfl⟩
    · obtain ⟨jw, p0, hjw, hpoll⟩ := wg0_old_poll hp hX hFw hw he0
        ⟨c.val, c.isLt, h1⟩ (by simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
                                omega)
      obtain ⟨-, x, hx, -⟩ := old_ld_word_at hp hIn hX hFw hbelow hEb he0
        (by rw [ha]; have := c.isLt; omega) hil hjw hpoll
      exact ⟨x, by rw [List.getD_eq_getElem?_getD, hx]; rfl⟩
  have hx' : ∀ i, ∃ x : ℝ, i < 64 → vals.getD i (.pred false) = .float .f32 x := fun i => by
    by_cases hi : i < 64
    · obtain ⟨x, hxx⟩ := hx i hi
      exact ⟨x, fun _ => hxx⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose O hO using hx'
  exact ⟨vals, rfl, hlen, O, fun i hi => by rw [hO i hi]; exact rd_float_f32 _⟩

/-- **An accumulator load keeps the trace valid.** -/
theorem w0Valid_snoc_opc (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hw : warp L g < 4) (hpc : e.pc ∈ w0OPcs)
    (hbelow : ∀ w e', X.get w = some e' → Relation.TransGen (TcMma.TcStep L X) w (g, k) →
      TmRace.TmClaim L X w ∧ TmRace.RfClaim L X w)
    (hEb : ∀ w, (w = (g, k) ∨ Relation.TransGen (TcMma.TcStep L X) w (g, k)) →
      MmaElemAt X w)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  obtain ⟨vals, hv, hpay⟩ := w0_pay_opc hp hIn hX hFw he hub hw hpc hbelow hEb
  rw [trace_take_succ he]
  exact w0Core_opc hp.scalePos hpc hv hpay h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
