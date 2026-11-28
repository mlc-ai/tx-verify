-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryAddr
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Query
import Kernels.InklingRelDecode.Proof.Prologue.QLoadPair
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

def qSiteAt (n : Nat) : Site := if h : n<64 then .ldq ⟨n,h⟩ else .stq 0 0

theorem after_query_cross {Q L g w d} (j : Fin 64) :
    SegU kernel Assumptions.all L g (queryPc j+1) (facts Q L g w d (queryPc j))
      (qSiteAt (j.val+1)).pc (facts Q L g w d (qSiteAt (j.val+1)).pc) := by
  by_cases last : j = 63
  · subst j; exact first_store_addr
  · have frames : ∀ j : Fin 64, j ≠ 63 → crossCheck (queryPc j) (queryPc j+1)
        (qSiteAt (j.val+1)).pc := by decide +kernel
    exact cross (frames j last)

private theorem skip_one {Q L g w d} (j : Fin 64) (off : queryOn (g%L.block) (j.val/16) d = false) :
    SegU kernel Assumptions.all L g (queryPc j) (facts Q L g w d (queryPc j))
      (qSiteAt (j.val+1)).pc (facts Q L g w d (qSiteAt (j.val+1)).pc) := by
  have val := query_value (Q := Q) (L := L) (g := g) (w := w) (d := d) j
  rw [off] at val
  have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
    (qLoadPair (L := L) (g := g) j).2 (mem_factsFrom_eq (query_live j) val) rfl
  exact (SegU.of_seg skip).comp (after_query_cross j)

/-- Skip the predicated loads between a group boundary and the next enabled group.
Index 64 denotes the first vector store. -/
theorem skip_queries {Q L g w d lo hi} (ord : lo ≤ hi) (bound : hi ≤ 64)
    (off : ∀ n, lo ≤ n → n < hi → queryOn (g%L.block) (n/16) d = false) :
    SegU kernel Assumptions.all L g (qSiteAt lo).pc (facts Q L g w d (qSiteAt lo).pc)
      (qSiteAt hi).pc (facts Q L g w d (qSiteAt hi).pc) := by
  induction hi,ord using Nat.le_induction with
  | base => exact fun t ht => .inl ⟨t,.refl,ht⟩
  | succ k hk ih =>
    have lt : k < 64 := by omega
    have one := skip_one (Q := Q) (w := w) ⟨k,lt⟩ (off k hk (by omega))
    apply (ih (by omega) (fun n hn hl => off n hn (by omega))).comp
    simpa only [qSiteAt,dite_eq_left lt,queryPc] using one

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
