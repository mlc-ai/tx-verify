-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PexAsync
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # The P exchange is ordered

A conflict at a byte of `pExchange` is between two accesses of warpgroup 0's threads (`pex_cls`,
`pex_ord`: the barriers' counts) or between a thread's write (a peer store or a P store) and
the asynchronous operand read of a PV MMA (`async_region`: the only asynchronous access of the P
tile; `pex_tm`: the score ring). Two reads are no conflict. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hBar : BarRows P L X) (hR : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

omit hR hI hB in
/-- **An asynchronous access of the P tile** is a PV MMA's read of operand A. -/
private theorem pex_async {g k : Nat} {p : AsyncCopy.Part} {a : Acc} {w : Bool} {l : Loc} {c : Nat}
    (hi : X.Intent (.async (g, k) p) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c .pExchange l) :
    w = false ∧ ∃ pc bb s acc mask idx, X.get (g, k) = some ⟨pc, .tc (.mma bb s acc mask)⟩ ∧
      bb < 256 ∧ MbarRow.MmaAt L g pc ∧ p = .mmaRead false idx ∧
      MemRow.LocIn L (g / L.block) .pExchange l ∧ X.MmaFootprint (g, k) false idx l := by
  rcases async_region hp hX hFw hi hc hl.1 with ⟨r, hr⟩ | ⟨hr, pc, bb, s, acc, mask, idx, hget, hbb,
    hat, hp', hfp⟩ | ⟨r, hr, -⟩
  · exact absurd (locIn_eq hr hl).2 (by simp)
  · subst hp'
    exact ⟨hi.1, pc, bb, s, acc, mask, idx, hget, hbb, hat, rfl, hr, hfp⟩
  · exact absurd (locIn_eq hr hl).2 (by simp)

include hBar in
/-- **The P exchange is ordered.** -/
theorem pExchange_ordered : RegionOrdered L X .pExchange := by
  intro e f a b l hcon ha hb hl _
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hcon
  obtain ⟨c, hlc⟩ := hl
  have lift : ∀ {x y : EvId}, baseCausality L X x y →
      ByteCausality L X l (.thread x) (.thread y) := fun h => .direct (.of_base L h)
  cases e with
  | thread x =>
    obtain ⟨g, k⟩ := x
    have he' : X.Access (g, k) a we := he
    obtain ⟨e1, hg, hwg⟩ := pex_cls hp hX hFw he' ha hlc
    cases f with
    | thread y =>
      obtain ⟨h, j⟩ := y
      have hf' : X.Access (h, j) b wf := hf
      obtain ⟨f1, hh, -⟩ := pex_cls hp hX hFw hf' hb hlc
      rcases pex_ord hp hX hFw hBar hg hh hw with rfl | h1 | h1
      · exact same_thread he' hf' (fun h' => hne (by rw [h'])) hov l
      · exact .inl (lift h1)
      · exact .inr (lift h1)
    | async y q =>
      obtain ⟨gi, ki⟩ := y
      obtain ⟨hwf, pc, bb, s, acc, mask, idx, hget, hbb, hat, rfl, hlg, hfp⟩ :=
        pex_async hp hX hFw hf hb hlc
      subst hwf
      have hwe : we = true := by rcases hw with h | h <;> simp_all
      subst hwe
      obtain ⟨bs, hwr⟩ := hwg rfl
      exact pex_tm hp hX hFw hR hI hB hg hwr ha hget hbb hat hlg (hg.cta ▸ rfl) hfp
  | async x p =>
    obtain ⟨gi, ki⟩ := x
    obtain ⟨hwe, pc, bb, s, acc, mask, idx, hget, hbb, hat, rfl, hlg, hfp⟩ :=
      pex_async hp hX hFw he ha hlc
    subst hwe
    cases f with
    | thread y =>
      obtain ⟨h, j⟩ := y
      have hf' : X.Access (h, j) b wf := hf
      obtain ⟨f1, hh, hwh⟩ := pex_cls hp hX hFw hf' hb hlc
      have hwf : wf = true := by rcases hw with h | h <;> simp_all
      subst hwf
      obtain ⟨bs, hwr⟩ := hwh rfl
      exact (pex_tm hp hX hFw hR hI hB hh hwr hb hget hbb hat hlg (hh.cta ▸ rfl) hfp).symm
    | async y q =>
      obtain ⟨hwf, -⟩ := pex_async hp hX hFw hf hb hlc
      subst hwf
      rcases hw with h | h <;> cases h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
