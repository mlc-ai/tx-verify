-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # The MMA before a QK MMA is the QK MMA before it in its block

QK MMA `k ≥ 1` (at `qkPc k`) is preceded, in the MMA lane's trace, by QK MMA `k - 1` (at
`qkPc (k - 1)`, D at 400) with no MMA between them (`mma_qkPrev`): the lane's MMA count before
an MMA is `24 r + slot`, QK MMA `k` has slot `k`, and the event with count `24 r + k - 1` is the
one with that slot. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

omit hp hX hFw in
private theorem cls_mma (e : Event) : Mma.cls .mma e = isMmaIssue e := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | tc t => cases t <;> simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]
  | _ => simp [Mma.cls, Mma.inRole, Mma.kindOf, isMmaIssue]

omit hp hX hFw in
private theorem issues_eq (xs : List Event) : xs.countP (Mma.cls .mma) = mmaIssues xs :=
  List.countP_congr fun e _ => by rw [cls_mma]

/-- The slot of an MMA of the lane: QK slot `k` at `qkPc k`, or a PV slot. -/
theorem mma_slot_pc {i pc dc : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hx : X.get (g, i) = some ⟨pc, .tc (.mma dc s acc mask)⟩)
    (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ r k, k < 24 ∧ mmaIssues ((X.tr g).take i) = 24 * r + k ∧
      ((k < 16 ∧ TmemRow.qkPc k = pc ∧ dc = 400) ∨
        (16 ≤ k ∧ k - 16 < 8 ∧ TmemRow.pvPc (k - 16) = pc ∧ dc = 128 * ((k - 16) % 2))) := by
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw hx (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX hx)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s => exact absurd rfl (hl s)
  case qk k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    obtain ⟨⟨hd, -, -⟩, -⟩ := hE
    have hk := k.isLt
    refine ⟨cnt.toNat, k.val, by omega, ?_, .inl ⟨by omega, hpc.symm, hd⟩⟩
    rw [← issues_eq, hn _ (by simp)]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
      show ¬ 2 + k.val ≤ 1 by omega, show 2 + k.val ≤ 18 by omega]
  case pv k =>
    obtain ⟨⟨-, -, -, -, hcnt, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    obtain ⟨⟨hd, -, -⟩, -⟩ := hE
    have hk := k.isLt
    refine ⟨cnt.toNat, 16 + k.val, by omega, ?_, .inr ⟨by omega, by omega, ?_, ?_⟩⟩
    · rw [← issues_eq, hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
        show ¬ 21 + k.val ≤ 1 by omega, show ¬ 21 + k.val ≤ 18 by omega,
        show ¬ 21 + k.val ≤ 20 by omega]
      omega
    · rw [show 16 + k.val - 16 = k.val by omega]
      simp only [Mma.Site.pc, TmemRow.pvPc] at hpc ⊢
      omega
    · rw [hd, show 16 + k.val - 16 = k.val by omega]

omit hp hX hFw in
/-- The `c`-th MMA issue of a prefix, with `c` earlier ones, if there are more than `c`. -/
theorem mma_with_count {i c : Nat} (h : c + 1 ≤ mmaIssues ((X.tr g).take i)) :
    ∃ j < i, ∃ pc dc s acc mask, X.get (g, j) = some ⟨pc, .tc (.mma dc s acc mask)⟩ ∧
      1853 ≤ pc ∧ pc ≤ 2160 ∧ mmaIssues ((X.tr g).take j) = c := by
  obtain ⟨j, x, hj, hx, hcnt⟩ := MbarRing.Slot.exists_nth_countP isMmaIssue
    (xs := (X.tr g).take i) h
  have hlen := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_take] at hlen
  have hji : j < i := by omega
  have hxj : (X.tr g)[j]? = some x := by
    rw [List.getElem?_take_of_lt hji] at hj
    exact hj
  have hcnt' : mmaIssues ((X.tr g).take j) = c := by
    rw [List.take_take, Nat.min_eq_left hji.le] at hcnt
    exact hcnt
  obtain ⟨pc, kd⟩ := x
  simp only [isMmaIssue, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨hr, hk⟩ := hx
  cases kd with
  | tc t =>
    cases t with
    | mma dc s acc mask => exact ⟨j, hji, pc, dc, s, acc, mask, hxj, hr.1, hr.2, hcnt'⟩
    | _ => simp at hk
  | _ => simp at hk

/-- **The count of a QK MMA**: QK MMA `k` is the `24 r + k`-th MMA issue of the lane. -/
theorem mma_qkCount {i k : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s acc mask)⟩) (hk : k < 16) :
    ∃ r, mmaIssues ((X.tr g).take i) = 24 * r + k := by
  have hrg : 1853 ≤ TmemRow.qkPc k ∧ TmemRow.qkPc k ≤ 2160 := by
    simp only [TmemRow.qkPc]; split <;> omega
  obtain ⟨r, k', hk', hn, hcase⟩ := mma_slot_pc hp hX hFw hx ⟨by omega, by omega⟩
  have hkk : k' = k := by
    rcases hcase with ⟨-, h2, -⟩ | ⟨-, -, h2⟩
    · simp only [TmemRow.qkPc] at h2
      split_ifs at h2 <;> omega
    · simp only [TmemRow.qkPc, TmemRow.pvPc] at h2
      split_ifs at h2 <;> omega
  subst hkk
  exact ⟨r, hn⟩

/-- **The MMA before QK MMA `k`**: for `1 ≤ k < 16`, the lane's MMA event before the QK MMA `k`
at index `i` is QK MMA `k - 1` (at `qkPc (k - 1)`, D at 400): an event `j < i`, with no MMA of
the role's pcs strictly between `j` and `i`. -/
theorem mma_qkPrev {i k : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s acc mask)⟩)
    (hk1 : 1 ≤ k) (hk : k < 16) :
    ∃ j < i, (∃ s' acc' mask', X.get (g, j) =
        some ⟨TmemRow.qkPc (k - 1), .tc (.mma 400 s' acc' mask')⟩) ∧
      (∃ r, mmaIssues ((X.tr g).take i) = 24 * r + k ∧
        mmaIssues ((X.tr g).take j) = 24 * r + (k - 1)) ∧
      ∀ j', j < j' → j' < i → ∀ e, X.get (g, j') = some e →
        ¬ (1853 ≤ e.pc ∧ e.pc ≤ 2160 ∧
          ∃ dc s' acc' mask', e.kind = .tc (.mma dc s' acc' mask')) := by
  have hrg : ∀ k, k < 16 → 1853 ≤ TmemRow.qkPc k ∧ TmemRow.qkPc k ≤ 2160 := by
    intro k hk; simp only [TmemRow.qkPc]; split <;> omega
  obtain ⟨r, k', hk', hn, hcase⟩ := mma_slot_pc hp hX hFw hx
    ⟨by have := hrg k hk; omega, by have := hrg k hk; omega⟩
  have hkk : k' = k := by
    rcases hcase with ⟨-, h2, -⟩ | ⟨-, -, h2⟩
    · simp only [TmemRow.qkPc] at h2
      split_ifs at h2 <;> omega
    · simp only [TmemRow.qkPc, TmemRow.pvPc] at h2
      split_ifs at h2 <;> omega
  subst hkk
  have hni : mmaIssues ((X.tr g).take i) = 24 * r + k' := hn
  obtain ⟨j, hji, pc', dc', s', acc', mask', hget, hin1, hin2, hcnt⟩ :=
    mma_with_count (g := g) (X := X) (i := i) (c := 24 * r + k' - 1) (by omega)
  have hin : 1850 ≤ pc' ∧ pc' < 2162 := ⟨by omega, by omega⟩
  obtain ⟨r', k'', hk'', hnj, hcase'⟩ := mma_slot_pc hp hX hFw hget hin
  have hnj' : mmaIssues ((X.tr g).take j) = 24 * r' + k'' := hnj
  have e1 : 24 * r' + k'' = 24 * r + k' - 1 := hnj'.symm.trans hcnt
  have hr' : r' = r ∧ k'' = k' - 1 := by clear hcase' hcase; omega
  obtain ⟨rfl, rfl⟩ := hr'
  rcases hcase' with ⟨-, h2, h3⟩ | ⟨h1, -⟩
  · subst h3
    refine ⟨j, hji, ⟨s', acc', mask', ?_⟩, ⟨r', ?_, ?_⟩,
      fun j' hj1 hj2 e he ⟨hl, hh, dc, s2, a2, m2, hke⟩ => ?_⟩
    · rw [hget, h2]
    · exact hni
    · omega
    · obtain ⟨pce, ke⟩ := e
      simp only at hl hh hke
      subst hke
      have hcls : isMmaIssue ⟨pce, .tc (.mma dc s2 a2 m2)⟩ = true := by
        simp [isMmaIssue]
        omega
      have hxc : isMmaIssue ⟨pc', .tc (.mma 400 s' acc' mask')⟩ = true := by
        simp [isMmaIssue]
        omega
      have hstep : ∀ n e', X.get (g, n) = some e' → mmaIssues ((X.tr g).take (n + 1)) =
          mmaIssues ((X.tr g).take n) + (if isMmaIssue e' then 1 else 0) := by
        intro n e' hne
        have h1 : (X.tr g)[n]? = some e' := hne
        simp only [mmaIssues, List.take_add_one, h1, List.countP_append]
        simp
      have hmono : ∀ a b, a ≤ b → mmaIssues ((X.tr g).take a) ≤ mmaIssues ((X.tr g).take b) :=
        fun a b hab => (List.take_sublist_take_left hab).countP_le
      have h1 := hstep j _ hget
      have h2 := hstep j' _ he
      have h3 := hmono (j + 1) j' hj1
      have h4 := hmono (j' + 1) i hj2
      simp only [hcls, hxc, ite_true] at h1 h2
      clear hcase
      omega
  · omega

omit hp hX hFw in
/-- **An MMA issue adds one to the lane's issue count**: the count before an earlier MMA issue
is below the count before a later event. -/
theorem mmaIssues_lt {j i pc dc : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hj : X.get (g, j) = some ⟨pc, .tc (.mma dc s acc mask)⟩) (hr : 1853 ≤ pc ∧ pc ≤ 2160)
    (hji : j < i) :
    mmaIssues ((X.tr g).take j) + 1 ≤ mmaIssues ((X.tr g).take i) := by
  have hcls : isMmaIssue ⟨pc, .tc (.mma dc s acc mask)⟩ = true := by
    simp [isMmaIssue]
    omega
  have h1 : (X.tr g)[j]? = some ⟨pc, .tc (.mma dc s acc mask)⟩ := hj
  have h2 : mmaIssues ((X.tr g).take (j + 1)) = mmaIssues ((X.tr g).take j) + 1 := by
    simp only [mmaIssues, List.take_add_one, h1, List.countP_append]
    simp [hcls]
  have h3 : mmaIssues ((X.tr g).take (j + 1)) ≤ mmaIssues ((X.tr g).take i) :=
    (List.take_sublist_take_left hji).countP_le
  omega

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
