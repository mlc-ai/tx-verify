-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaRawTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # Counting the gather issues by raw-slot generation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaGatherCounts

open PTX PTX.Flow Ledger
open Wg1Tma (D)

private noncomputable def rawLoc (L : Launch) (g : Nat) (slot : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff slot.val⟩

/-- A gather site within or after the block loop. -/
def blockStarted : Wg1Tma.Site → Bool
  | .elect | .lenOrig | .lenExtra | .waitQ | .waitLast => false
  | _ => true

private def gathered : Wg1Tma.Site → Nat
  | .coord k _ => k.val - 1
  | .issue k => k.val
  | .rawReady | .coordFree => 16
  | _ => 0

private def priorBlocks (d : D) : Nat := if blockStarted d.site then d.block else 0

private def numIssued (slot : Fin 2) (d : D) : Nat :=
  16 * ringUses 2 slot (priorBlocks d) + if d.block % 2 = slot.val then gathered d.site else 0

private def counts (L : Launch) (g : Nat) (slot : Fin 2) (d : D) (n : Cls → Nat) : Prop :=
  n (.issue (rawLoc L g slot)) = numIssued slot d

/-- An actual gather records its selected descriptor and its four-row destination in this
block's raw buffer, and it notifies that buffer's ready object with 2304 bytes. -/
theorem gather_event_fields {P : Params} {L : Launch} {g a : Nat} {mem0 : Mem0}
    {d : D} {k : Fin 16} {e : Event} {o : Option TState} {spec : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hsite : d.site = .issue k)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o)
    (he : e.kind = .tensorIssue a spec) :
    a = P.param1Base + Wg1Tma.kvOff d ∧
    spec.sharedBase =
      ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.issueDst (d.block % 2) k.val⟩ ∧
    spec.mbar = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩ ∧
    TensorTransfer.bytes spec.descriptor = 2304 := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := hf
  change (Wg1Tma.code P L g).AtD d t at hat
  change Wg1Tma.Inv P L g d at hi
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hcode : kernel.code[d.site.pc]? = some (Wg1Tma.issueInstr k) := by
    rw [hsite]
    exact Wg1Tma.issueInstr_code k
  rw [hcode, hat.1] at hf
  have hbuf := hi.buf_eq (by rw [hsite]; intro h; cases h)
    (by rw [hsite]; intro h; cases h)
  rw [← hbuf]
  exact Wg1Tma.gather_issue_fields hpre hsite hat hi hf he

private theorem counts_snoc {L : Launch} {g : Nat} {slot : Fin 2}
    {e : Event} {n : Cls → Nat} {d d' : D} (h : counts L g slot d n)
    (hstep : numIssued slot d' = numIssued slot d + if issuesTo (rawLoc L g slot) e then 1 else 0) :
    counts L g slot d' (bump n e) := by
  simp only [counts, bump_apply, Cls.test] at h ⊢
  rw [h, hstep]
  congr

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem counts_step {slot : Fin 2} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (hc : counts L g slot d n)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o)
    (hn : Wg1Tma.next P L g d e = some (some d')) :
    counts L g slot d' (bump n e) := by
  apply counts_snoc hc
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg1Tma.next, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case elect.elect =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    unfold Wg1Tma.firstLenSite
    split
    · split <;> simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
    · simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case lenOrig.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    split <;> simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case waitQ.wait m p ok acq sc =>
    cases ok <;> cases hn <;>
      simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case waitLast.wait m p ok acq sc =>
    have hpos := Nat.ne_of_gt (totalBlocks_pos d.len0 d.len1)
    simp only [hpos, ↓reduceIte] at hn
    cases ok <;> cases hn <;>
      simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk, Wg1Tma.beginLoop]
  case waitCoord.wait m p ok acq sc =>
    cases ok <;> cases hn <;>
      simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case waitFree.wait m p ok acq sc =>
    cases ok <;> cases hn <;>
      simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case coord.rd =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    unfold Wg1Tma.afterCoord
    have hn' : issuesTo (rawLoc L g slot) e = false := by simp [issuesTo, hk]
    rw [hn']
    split
    · simp [numIssued, priorBlocks, hd, blockStarted, gathered]
    · split <;> simp_all [numIssued, priorBlocks, blockStarted, gathered]
  case issue.tensorIssue k a spec =>
    have hloc := (gather_event_fields hpre hd hf hk).2.2.1
    have he : issuesTo (rawLoc L g slot) e = decide (d.block % 2 = slot.val) := by
      simp [issuesTo, hk, hloc, rawLoc, Wg1Tma.rawReadyOff]
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    unfold Wg1Tma.afterIssue
    have hlt := k.isLt
    by_cases hold : d.block % 2 = slot.val
    · simp only [he, hold, decide_true, ↓reduceIte]
      split_ifs <;>
        simp [numIssued, priorBlocks, hd, blockStarted, gathered, hold] <;> omega
    · simp only [he, hold, decide_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> simp [numIssued, priorBlocks, hd, blockStarted, hold]
  case rawReady.arrive =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]
  case coordFree.arrive =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    unfold Wg1Tma.afterFree
    split
    all_goals
      by_cases hslot : d.block % 2 = slot.val
      all_goals
        simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk,
          ringUses_succ slot.isLt,
          hslot]
    all_goals omega
  case barrier.bar =>
    split at hn <;> cases hn <;>
      simp [numIssued, priorBlocks, hd, blockStarted, gathered, issuesTo, hk]

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) : counts L g slot d (count es i) := by
  refine Ledger.tma (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  simp [counts, numIssued, Wg1Tma.init, priorBlocks, blockStarted, gathered,
    hn _ ⟨_, .inr (.inr rfl)⟩, ringUses_zero slot.isLt]
  by_cases h0 : (0 : Nat) = slot.val <;> simp [h0]

/-- At a gather site, the issue ordinal on its buffer is sixteen times the generation plus its
index within that generation. -/
theorem composed_issue_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D} {k : Fin 16}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .issue k) :
    (es.take i).countP
      (issuesTo ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩) =
        16 * (d.block / 2) + k.val := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  have h := counts_at hpre slot ht hs
  change count es i (.issue (rawLoc L g slot)) = _
  rw [h, numIssued, priorBlocks, hd]
  simp [blockStarted, gathered, slot,
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]

/-- The role issued all sixteen gathers of each preceding block, on that block's slot. -/
theorem composed_prior_issues (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hb : blockStarted d.site = true) :
    16 * ((d.block + (1 - slot.val)) / 2) ≤ (es.take i).countP
      (issuesTo ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff slot.val⟩) := by
  change _ ≤ count es i (.issue (rawLoc L g slot))
  rw [counts_at hpre slot ht hs]
  simp [numIssued, priorBlocks, hb, ringUses]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaGatherCounts
