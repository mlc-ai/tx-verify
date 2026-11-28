-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.MExact
public import Kernels.InklingRelDecode.Proof.Lib.SoftWords
import Lemmas.Flow.Step.RuleStep
import Lemmas.Flow.W0Reads

@[expose] public section

/-! # The running sum of the rounds is the fold's

The sum a lane carries (register 1915) takes, at pc 950, the fused product of its old value, the
rescale factor and the round's sum (register 1531, the lane's own sum and its partner's, added at
pc 2235). On exact words, the carried maximum and sum after the rounds are `SoftFold.run`'s. A
round's words are `Lib.Rw`: the halves' maxima and the two sums. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open Lib.SoftFold Classical

set_option maxRecDepth 100000
noncomputable section

theorem lmAfter_fst (c : Value) (rs : List Lib.Rw) :
    (Lib.lmAfter c rs).1 = mAfter c (rs.map fun w => (w.a, w.b)) := by
  have key : ∀ (rs : List Lib.Rw) (p : Value × Value),
      (rs.foldl (Lib.lmNext c) p).1 = (rs.map fun w => (w.a, w.b)).foldl
        (fun m q => Lib.mNext c m (Lib.mxWord m q.1 q.2)) p.1 := by
    intro rs
    induction rs with
    | nil => intro p; rfl
    | cons w rs ih => intro p; exact ih _
  exact key rs _

theorem ev_fma_rr {fz : Bool} {d a b c : Value} {x y z : ℝ} (ha : Rd a x) (hb : Rd b y)
    (hc : Rd c z) : Ev (okVal d (floatE (fmaI .rn fz) [a, b, c])) ((x * y + z : ℝ) : EReal) := by
  have h : (mulEReal (x : EReal) (y : EReal)).bind (addEReal · (z : EReal)) =
      some (((x * y + z : ℝ)) : EReal) := by
    rw [mulEReal_coe, Option.bind_some, addEReal_coe]
  exact ⟨by rw [okVal_ok (fmaE_reads ha hb hc h), erealValue_coe], EReal.coe_ne_top _⟩

/-- The sum of the lane's and its partner's sums, fused with the old sum and the factor. -/
theorem lNext_ev {l f s r : Value} {x y u w : ℝ} (hl : Rd l x) (hf : Rd f y) (hs : Ev s (u : EReal))
    (hr : Ev r (w : EReal)) : Ev (Lib.lNext l f s r) ((x * y + (u + w) : ℝ) : EReal) := by
  have hsum := ev_add (fz := false) (d := b32 0) hs hr
  exact ev_fma_rr hl hf hsum.read

theorem lmNext_ev {c : Value} {sc : ℝ} (hc : Ev c sc) (hpos : 0 < sc) {p : Value × Value}
    {st : St} {w : Lib.Rw} {blk : List (ℝ × ℝ)} (hm : Ev p.1 st.m) (hl : Rd p.2 (st.l : EReal))
    (h : Lib.RoundOk sc st w blk) :
    Ev (Lib.lmNext c p w).1 (step sc blk st).m ∧
      Rd (Lib.lmNext c p w).2 ((step sc blk st).l : EReal) := by
  obtain ⟨aE, bE, u, v, ha, hb, hmax, hs, hr, hsum⟩ := h
  refine ⟨round_ev hc hpos hm ha hb hmax, ?_⟩
  have hmx := mxWord_ev hm ha hb
  rw [max_assoc, hmax] at hmx
  obtain ⟨-, hk, hal⟩ := alpha_exact hc hpos hm hmx
  have := (lNext_ev hl hal hs hr).read
  rw [Lib.step_l, ← hsum]
  exact this

/-- **The carried maximum and sum after the rounds are the fold's.** -/
theorem lmAfter_ev {c : Value} {sc : ℝ} (hc : Ev c sc) (hpos : 0 < sc) :
    ∀ (rs : List Lib.Rw) (bs : List (List (ℝ × ℝ))) (p : Value × Value) (st : St),
      Ev p.1 st.m → Rd p.2 (st.l : EReal) →
      (∀ j st', j < rs.length → st' = (bs.take j).foldl (fun s b => step sc b s) st →
        ∀ w blk, rs[j]? = some w → bs[j]? = some blk → Lib.RoundOk sc st' w blk) →
      rs.length = bs.length →
      Ev (rs.foldl (Lib.lmNext c) p).1 (bs.foldl (fun s b => step sc b s) st).m ∧
      Rd (rs.foldl (Lib.lmNext c) p).2 ((bs.foldl (fun s b => step sc b s) st).l : EReal) := by
  intro rs
  induction rs with
  | nil =>
    intro bs p st hm hl _ hlen
    obtain rfl : bs = [] := List.length_eq_zero_iff.mp hlen.symm
    exact ⟨hm, hl⟩
  | cons w rs ih =>
    intro bs p st hm hl h hlen
    obtain ⟨blk, bs, rfl⟩ : ∃ blk bs', bs = blk :: bs' := by
      cases bs with
      | nil => simp at hlen
      | cons b bs => exact ⟨b, bs, rfl⟩
    have h0 := h 0 st (by simp) rfl w blk rfl rfl
    obtain ⟨hm1, hl1⟩ := lmNext_ev hc hpos hm hl h0
    refine ih bs _ _ hm1 hl1 (fun j st' hj he w' blk' hw hb => ?_) (by simpa using hlen)
    exact h (j + 1) st' (by simpa using hj) (by simpa using he) w' blk' hw hb

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
