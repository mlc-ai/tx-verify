-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictWalkD
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexEntry
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The strict parameter prefix of the index warp

`ixq_entry`: `Index/../Lib/IndexEntry.lean`'s `ixw_entry` as a strict segment under `QT ixQt`:
from pc 2332 with the entry registers to the first event. The `ld.param` pieces write control
registers (tags untouched: `ix_ldpQ`), except the page size `%r497` of pc 2349, whose nonzero tag
(`Pre.pagePos`) the invariant asks for from pc 2350 (`ix_ldpQnz`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc PTX.Flow.Tagged

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A scalar `ld.param` whose register is no tagged register of the invariant. -/
theorem ix_ldpQ (hp : Pre P L m) (hP : Plain L g) {pc d off x n b : Nat} {ty : DType}
    {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304) (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : d ∉ F.map Prod.fst)
    (hB : frameB ((kernel.code.drop pc).take 1) ((ixQt (pc + 1)).map Prod.fst) = true)
    (hq : tagsIn (ixQt (pc + 1)) (ixQt pc) = true) (hr : pc + 1 ≤ 2600) (hl : 2332 ≤ pc)
    (rest : SegQ kernel Assumptions.all L g (QT ixQt) (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) b G) :
    SegQ kernel Assumptions.all L g (QT ixQt) pc F b G :=
  SegQ.comp (SegQ.of_seg_frame rulesFrame (seg_ldp hp hc hty hal hoff hf h2991
    fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq)) (by omega)
    (by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hc; omega) (by omega)
    (hP.segs.mono hl hr) hB hq) rest

/-- A positive 32-bit parameter loads as a nonzero word. -/
theorem pw_nz {x : Nat} (h0 : 0 < x) (h1 : x < 2 ^ 32) : (pw x).toNat % 2 ^ 32 ≠ 0 := by
  have h : leNat x 0 4 = x := by
    rw [leNat_eq]; norm_num; omega
  simp only [pw, h, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt h1]
  omega

/-- The invariant at pc 2350 without the page size's nonzero tag. -/
noncomputable def ixQtP (pc : Nat) : Env := if pc = 2350 then (ixQt 2350).dropLast else ixQt pc

theorem ixQt_2350 : ixQt 2350 = (ixQt 2350).dropLast ++ [(497, .nz 32)] := by
  decide +kernel

theorem lookup_append_single {l : Env} {a : Nat × Tag} {r : Nat} {tg : Tag}
    (h : (l ++ [a]).lookup r = some tg) : l.lookup r = some tg ∨ (a.1 = r ∧ a.2 = tg) := by
  induction l with
  | nil =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.nil_append, List.lookup] at h
    cases hc : (r == a1) <;> simp [hc] at h
    exact Or.inr ⟨(beq_iff_eq.mp hc).symm, h⟩
  | cons q l ih =>
    simp only [List.cons_append, List.lookup] at h ⊢
    split at h
    · exact Or.inl h
    · exact ih h

/-- **The page size's load** (pc 2349): the register's nonzero tag from `Pre.pagePos`. -/
theorem ix_ldp497 (hp : Pre P L m) (hP : Plain L g) {b : Nat} {F G : List (Nat × Value)}
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : 497 ∉ F.map Prod.fst)
    (rest : SegQ kernel Assumptions.all L g (QT ixQt) 2350
      ((497, .bits 32 (pw P.page)) :: F) b G) :
    SegQ kernel Assumptions.all L g (QT ixQt) 2349 F b G := by
  refine SegQ.comp ?_ rest
  have hz : (pw P.page).toNat % 2 ^ 32 ≠ 0 :=
    pw_nz hp.pagePos (by have := hp.pageFits; have := hp.blockStrideRange; omega)
  have base : SegQ kernel Assumptions.all L g (QT ixQtP) 2349 F 2350
      ((497, .bits 32 (pw P.page)) :: F) :=
    SegQ.of_seg_frame (qt := ixQtP) rulesFrame (seg_ldp (d := 497) (off := 36) (x := P.page)
      (n := 4) (ty := .int .b 32) hp Flow.code_2349 (by decide) (by decide) (by decide)
      (by simp [p0fields]) h2991 fun _ hq he => hd (by rw [← he]; exact List.mem_map_of_mem hq))
      (by omega) (by decide) (by omega) (hP.segs.mono (by omega) (by omega))
      (by decide +kernel) (by decide +kernel)
  refine SegQ.map base (fun t ht hq => ?_) (fun t ht hq => ?_)
  · simpa [QT, ixQtP, ht.1] using hq
  · have hQ : Typed (ixQtP 2350) t := by simpa [QT, ht.1] using hq
    have hQ' : Typed ((ixQt 2350).dropLast) t := by simpa [ixQtP] using hQ
    have hn := typed_nz_of_fact (t := t) (r := 497) (w := 32)
      (x := BitVec.ofNat 64 (leNat P.page 0 4))
      (List.mem_cons_self ..) hz (atHolds ht)
    simp only [QT, ht.1]
    intro r tg hr
    rw [ixQt_2350] at hr
    rcases lookup_append_single hr with h | ⟨h1, h2⟩
    · exact hQ' r tg h
    · subst h1; subst h2; exact hn 497 _ (by simp [List.lookup])

/-- A two-word `ld.param` whose registers are no tagged registers of the invariant. -/
theorem ix_ldp2Q (hp : Pre P L m) (hP : Plain L g) {pc d1 d2 off x y b : Nat}
    {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldp2Ins off d1 d2)) (hal : off % 8 = 0)
    (hoff : off + 8 ≤ 304) (hx : (off, x, 4) ∈ p0fields P L) (hy : (off + 4, y, 4) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F)
    (hd : freshKeys [(d1, .bits 32 (BitVec.ofNat 64 (leNat x 0 4))),
      (d2, .bits 32 (BitVec.ofNat 64 (leNat y 0 4)))] F = true)
    (hB : frameB ((kernel.code.drop pc).take 1) ((ixQt (pc + 1)).map Prod.fst) = true)
    (hq : tagsIn (ixQt (pc + 1)) (ixQt pc) = true) (hr : pc + 1 ≤ 2600) (hl : 2332 ≤ pc)
    (rest : SegQ kernel Assumptions.all L g (QT ixQt) (pc + 1)
      ((d2, .bits 32 (BitVec.ofNat 64 (leNat y 0 4))) ::
        (d1, .bits 32 (BitVec.ofNat 64 (leNat x 0 4))) :: F) b G) :
    SegQ kernel Assumptions.all L g (QT ixQt) pc F b G :=
  SegQ.comp (SegQ.of_seg_frame rulesFrame (seg_ldp2 hp hc hal hoff hx hy h2991 hd) (by omega)
    (by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hc; omega) (by omega)
    (hP.segs.mono hl hr) hB hq) rest

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
