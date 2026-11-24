-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaGatherCounts
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Tensor issue origins in the frozen kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingTensorEvents

open PTX PTX.Proof PTX.Flow

local macro "decide_site" : tactic =>
  `(tactic| first
    | (intro _; rename_i k; exact ⟨k, rfl⟩)
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private def loads : List Nat := Flow.tensorCopy.toList.drop 4

set_option maxRecDepth 100000 in
private theorem tensor_sites : OpPcsFast kernel.code tensorOp loads = true := by
  decide +kernel

variable {P : Params}

private theorem tensor_pc_of_fired {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event}
    {o : Option TState} {addr : Nat} {sp : TensorCopy.Spec}
    (hf : (Machine.machine P L g).Fired (some d) e o) (hk : e.kind = .tensorIssue addr sp) :
    (Machine.code P L g).pc d ∈ loads := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    obtain ⟨he, _⟩ := hf
    rw [he] at hk
    contradiction
  | some ins =>
    rw [hc] at hf
    cases hOp : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor hOp) hf addr sp hk).elim
    · exact OpPcsFast.mem tensor_sites hc hOp

private theorem fired_at_code {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event}
    {o : Option TState} {ins : Instr} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hc : kernel.code[(Machine.code P L g).pc d]? = some ins) :
    ∃ t, (Machine.code P L g).AtD d t ∧
      Fires ((Machine.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Machine.code P L g).AtD d t at hat
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hat.1, hc] at hf
  exact ⟨t, hat, hf⟩


/-- Tensor loads issue only at query or raw-gather sites. -/
def IssueSite : Machine.ThreadD → Prop
  | .mma q => ∃ k, q.site = .qLoad k
  | .tma q => ∃ k, q.site = .issue k
  | _ => False

theorem issue_site {L : Launch} {g : Nat} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {addr : Nat} {sp : TensorCopy.Spec} (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .tensorIssue addr sp) :
    IssueSite d := by
  have hm := tensor_pc_of_fired hf hk
  clear * - d hm
  cases d
  case prologue q =>
    change q.pc ∈ _ at hm
    change False
    cases q <;> revert hm <;> decide_site
  case wg0 q =>
    change q.site.pc ∈ _ at hm
    simp only [IssueSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case mma q =>
    change q.site.pc ∈ _ at hm
    simp only [IssueSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case tma q =>
    change q.site.pc ∈ _ at hm
    simp only [IssueSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case index q =>
    change q.site.pc ∈ _ at hm
    simp only [IssueSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case wg2 q =>
    change q.site.pc ∈ _ at hm
    simp only [IssueSite]
    generalize hq : q.site = site at hm ⊢
    clear hq q
    cases site <;> revert hm <;> decide_site
  case idle q =>
    change q.pc ∈ _ at hm
    change False
    cases q <;> revert hm <;> decide
  case head =>
    change 1843 ∈ _ at hm
    exact (by decide : 1843 ∉ loads) hm
  case done =>
    change 3611 ∈ _ at hm
    exact (by decide : 3611 ∉ loads) hm

private theorem query_mbar {L : Launch} {g pc dst : Nat} {mem0 : Mem0} {cs : List Opnd} {t : TState}
    {e : Event} {o : Option TState} {a : Nat} {sp : TensorCopy.Spec} (hpre : Pre P L mem0)
    (h811 : t.regs 811 = some (b32 (Wg1Mma.qTmaAddr L)))
    (h3059 : t.regs 3059 = some (b64 Wg1Mma.qCachePolicy))
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.cpTensor true false dst 0 (.reg 3058)
      cs 811 0 none .tile (some (.reg 3059)))) e o) (he : e.kind = .tensorIssue a sp) :
    sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ := by
  have hp := readBits_b64 (L := L) (g := g) h3059 (by decide)
  change Fires pc (tensorTmpl L g t (.cpTensor true false dst 0 (.reg 3058)
    cs 811 0 none .tile (some (.reg 3059)))) e o at hf
  have hT : tensorTmpl L g t (.cpTensor true false dst 0 (.reg 3058)
      cs 811 0 none .tile (some (.reg 3059))) =
      tensorTmpl L g t (.cpTensor true false dst 0 (.reg 3058) cs 811 0 none .tile) := by
    simp [tensorTmpl, cachePolicyRead, hp, bind, Except.bind, pure, Except.pure]
  rw [hT] at hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t)
    (ca := true) (grp := false) (dst := dst) (off := 0) (map := .reg 3058) (cs := cs)
    (mb := 811) (moff := 0) (lm := .tile) with ⟨f, hub⟩ | ⟨a', s', hIssue⟩
  · rw [hub] at hf
    rw [congrArg Event.kind hf.1] at he
    cases he
  · rw [hIssue] at hf
    obtain ⟨rfl, _⟩ := hf
    cases he
    have hs := (tensorLoadCopy_ok (tensorTmpl_unicast_issue hIssue).1).2.1
    rw [Wg1Mma.qTmaAddr_eq] at h811
    have hb : L.sharedBase + 222776 < 2 ^ 32 := by
      have := sharedBase_lt hpre
      omega
    have hm := mbarClusterLoc_b32 (L := L) (g := g) h811 hb
      (Wg2.sharedAddr_align hpre (by decide : 222776 % 8 = 0))
    change mbarClusterLoc L g t 811 0 = .ok _ at hs
    rw [hm] at hs
    exact (Except.ok.inj hs).symm

/-- Tensor issues come from a gather of the TMA role or a load of the fixed query object. -/
theorem issue_source {L : Launch} {g a : Nat} {mem0 : Mem0} {d : Machine.ThreadD} {e : Event}
    {o : Option TState} {sp : TensorCopy.Spec} (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some d) e o) (he : e.kind = .tensorIssue a sp) :
    sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ ∨
      ∃ q k, d = .tma q ∧ q.site = .issue k ∧
        a = P.param1Base + Wg1Tma.kvOff q ∧
        sp.sharedBase = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.issueDst (q.block % 2) k.val⟩ ∧
        sp.mbar = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (q.block % 2)⟩ ∧
        TensorTransfer.bytes sp.descriptor = 2304 := by
  have hs := issue_site hf he
  cases d
  case mma q =>
    obtain ⟨k, hk⟩ := hs
    have operands {t : TState} {n : Nat}
        (hat : (Wg1Mma.code P L g).AtD q t) (hcode : q.site.pc = n)
        (h1 : 811 ∈ Flow.live n) (h2 : 3059 ∈ Flow.live n) :
        t.regs 811 = some (b32 (Wg1Mma.qTmaAddr L)) ∧
          t.regs 3059 = some (b64 Wg1Mma.qCachePolicy) := by
      constructor
      · simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using
          Wg1Mma.atD_reg hat hcode h1
      · simpa [Wg1Mma.valueOf, Wg1Mma.values, PTX.Flow.lookupLit, Option.getD_some] using
          Wg1Mma.atD_reg hat hcode h2
    left
    fin_cases k
    · have hpc : q.site.pc = 1906 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_4)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1909 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_5)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1912 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_6)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1915 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_7)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1918 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_8)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1921 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_9)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1924 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_10)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
    · have hpc : q.site.pc = 1927 := by rw [hk]; rfl
      obtain ⟨t, hat, hfire⟩ := fired_at_code hf (by
        change kernel.code[q.site.pc]? = some _
        simpa only [hpc] using Flow.code_tensorCopy_11)
      change (Wg1Mma.code P L g).AtD q t at hat
      obtain ⟨h1, h2⟩ := operands hat hpc (by decide +kernel) (by decide +kernel)
      exact query_mbar hpre h1 h2 hfire he
  case tma q =>
    obtain ⟨k, hk⟩ := hs
    exact .inr ⟨q, k, rfl, hk, TmaGatherCounts.gather_event_fields hpre hk hf he⟩
  all_goals exact hs.elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingTensorEvents
