-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

@[expose] public section

/-!
# Keep test: a generic store before a bulk store needs `fence.proxy.async` (MEM-MODEL-CAUSALITY)

One thread stores a word to shared memory and then issues a bulk store (`cp.async.bulk`, performed
by the TMA unit in the async proxy) that reads the same four bytes and writes them to global
memory:

```
st.shared.u32 [s], 1;
fence.proxy.async.shared::cta;             // only in the fenced program
cp.async.bulk.global.shared::cta.bulk_group [g], [s], 4;
exit;
```

* `unfenced_unsafe`: without the fence the store and the copy's source read are a data race
  (`Race`): they use different proxies, so they are not morally strong, and nothing orders the
  generic store before the async-proxy read (§9.7.15.4, MEM-MODEL-CAUSALITY: from a thread access
  to an async-proxy access only `ProxyBefore` orders).
* `fenced_no_race`: with the fence no pair of accesses of the execution is a data race: the fence
  lies between the store and the issue in program order and covers the shared bytes of the CTA,
  so `ProxyBefore` orders the store before the read.

The executions contain the issue of the copy without its effects; `Conflict` and `Race` read the
footprints of pending accesses, so the effects do not change the verdict.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

namespace ProxyFence

/-- One CTA of one thread. -/
def L1 : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- The four shared bytes `s` at offset 0 of CTA 0. -/
def sA : Acc := { loc := ⟨.shared, 0, 0⟩, size := 4 }
/-- The four global bytes `g` at address 64. -/
def gA : Acc := { loc := ⟨.global, 0, 64⟩, size := 4 }
def one : List Byte := (Value.bits 32 1).toBytes

/-- `cp.async.bulk.global.shared::cta.bulk_group [g], [s], 4`. -/
def spec : AsyncCopy.Spec := { src := sA, dst := gA, completion := .bulkGroup }

/-- `fence.proxy.async.shared::cta`. -/
def fenceK : Kind := .fenceProxy (.async (some (.shared .cta))) none

/-- The trace of the thread, without or with the fence. -/
def trace : Bool → List Event
  | false => [⟨0, .wr sA one⟩, ⟨1, .copy spec⟩, ⟨2, .exit⟩]
  | true => [⟨0, .wr sA one⟩, ⟨1, fenceK⟩, ⟨2, .copy spec⟩, ⟨3, .exit⟩]

/-- The trace position of the copy. -/
def copyAt (fence : Bool) : Nat := if fence then 2 else 1

def X (fence : Bool) : Execution where
  tr g := if g = 0 then trace fence else []
  rf _ _ := none

/-- Every event of the execution is the store, the fence, the copy or the exit. -/
theorem get_cases {fence : Bool} {e : EvId} {pc : Nat} {k : Kind}
    (h : (X fence).get e = some ⟨pc, k⟩) :
    (e = (0, 0) ∧ k = .wr sA one) ∨ (fence = true ∧ e = (0, 1) ∧ k = fenceK) ∨
      (e = (0, copyAt fence) ∧ k = .copy spec) ∨ k = .exit := by
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst hg
    cases fence <;> rcases i with _ | _ | _ | _ | i <;>
      simp [Execution.get, X, trace, copyAt] at h ⊢ <;> simp [← h]
  · simp [Execution.get, X, hg] at h

/-- No event of the execution is a wait of any kind. -/
theorem no_wait {fence : Bool} {w : EvId} {pc : Nat} {k : Kind}
    (h : (X fence).get w = some ⟨pc, k⟩)
    (hk : (∃ m q ok acq sc, k = .wait m q ok acq sc) ∨ (∃ m n, k = .bulkWait m n) ∨
      ∃ n, k = .asyncWait n) : False := by
  rcases get_cases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | rfl <;> simp [fenceK] at hk

/-- No asynchronous access is observed finished: there is no wait. -/
theorem not_asyncFinished {fence : Bool} {i w : EvId} {p : AsyncCopy.Part} :
    ¬ AsyncFinished L1 (X fence) i p w := by
  rintro (⟨k, -, hw, -⟩ | ⟨ws, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -⟩)
  · cases k with
    | bulk mode =>
      obtain ⟨pc, r, hw, -⟩ := hw
      exact no_wait hw (.inr (.inl ⟨_, _, rfl⟩))
    | cpAsync =>
      obtain ⟨pc, r, hw, -⟩ := hw
      exact no_wait hw (.inr (.inr ⟨_, rfl⟩))
  · exact no_wait hw (.inl ⟨_, _, _, _, _, rfl⟩)

private theorem no_mma {fence : Bool} (i : EvId) (d : Nat) (s : TcMma.OperandSpec)
    (accum : Bool) (mask : List Nat) : ¬ (X fence).MmaIssue i d s accum mask := by
  rintro ⟨pc, h⟩
  rcases get_cases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h <;> simp [fenceK] at h

private theorem no_cp {fence : Bool} (i : EvId) (spec : TcCopy.Spec) :
    ¬ (X fence).CpIssue i spec := by
  rintro ⟨pc, h⟩
  rcases get_cases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h <;> simp [fenceK] at h

/-- The copy is performed in the async proxy. -/
theorem not_genericCopy {fence : Bool} {i : EvId} : ¬ GenericCopy (X fence) i := by
  rintro ⟨s, ⟨pc, hc⟩, hg⟩
  rcases get_cases hc with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h <;> simp [fenceK] at h
  subst h
  simp [spec] at hg

theorem covers_sA : sA.Covers sA.loc := by
  simp [sA, Acc.Covers, Loc.InRange]

/-- The store and the copy's source read conflict. -/
theorem conflict (fence : Bool) :
    Conflict (X fence) (.thread (0, 0)) (.async (0, copyAt fence) (.read .copy)) sA sA := by
  refine ⟨by simp, true, false, .inr (.inl ⟨one, ⟨0, ?_⟩, rfl⟩),
    ⟨rfl, .inl ⟨spec, ⟨copyAt fence, ?_⟩, rfl⟩⟩, .inl rfl, sA.loc, covers_sA, covers_sA⟩ <;>
    cases fence <;> rfl

/-- Without the fence the store and the copy's source read are a data race. -/
theorem unfenced_race : Race L1 (X false) := by
  refine ⟨.thread (0, 0), .async (0, 1) (.read .copy), sA, sA, sA.loc, conflict false,
    ⟨rfl, rfl⟩, covers_sA, ?_, ?_, ?_, ?_⟩
  · rintro ⟨-, hg, -⟩
    exact not_genericCopy (hg.mp trivial)
  · rw [ByteCausality.direct_iff_of_no_operand no_mma no_cp,
      modelCausality_thread_async_of_not_generic L1 not_genericCopy]
    rintro ⟨-, fence, sp, scope, ⟨pc, hf⟩, -⟩
    rcases get_cases hf with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | h <;> simp_all
  · rw [ByteCausality.direct_iff_of_no_operand no_mma no_cp]
    rintro ⟨-, w, hw, -⟩
    exact not_asyncFinished hw
  · rintro ⟨-, ⟨h, -⟩, -⟩
    simp [AsyncCopy.Part.writes] at h

/-- The unfenced program is unsafe. -/
theorem unfenced_unsafe (K : Kernel) (A : List Assumption) (mem0 : Mem0) :
    Unsafe L1 K A mem0 (X false) :=
  .inr (.inr (.inl unfenced_race))

/-- The accesses of the fenced execution: the store, the copy's source read and the copy's
destination write. -/
theorem intent_cases {e : AsyncCopy.Ref} {a : Acc} {w : Bool} (h : (X true).Intent e a w) :
    (e = .thread (0, 0) ∧ a = sA) ∨ (e = .async (0, 2) (.read .copy) ∧ a = sA ∧ w = false) ∨
      (e = .async (0, 2) (.write .copy) ∧ a = gA) := by
  have copy : ∀ {i : EvId} {s : AsyncCopy.Spec}, (X true).Copy i s → i = (0, 2) ∧ s = spec := by
    rintro i s ⟨pc, hc⟩
    rcases get_cases hc with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hi, h⟩ | h <;> simp [fenceK] at h
    exact ⟨hi, h⟩
  cases e with
  | thread i =>
    refine .inl ⟨?_, ?_⟩ <;>
    rcases h with ⟨bs, ⟨pc, hr⟩, -⟩ | ⟨bs, ⟨pc, hr⟩, -⟩ | ⟨o, n, pc, hr⟩ <;>
      rcases get_cases hr with ⟨hi, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h <;> simp_all [fenceK]
  | async i p =>
    obtain ⟨rfl, hf⟩ := h
    have noev : ∀ {pc : Nat} {k : Kind}, (X true).get i = some ⟨pc, k⟩ → (∀ s, k ≠ .copy s) →
        (∀ a, k ≠ .wr a one) → k ≠ fenceK → k ≠ .exit → False := by
      intro pc k hk h1 h2 h3 h4
      rcases get_cases hk with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | rfl <;> simp_all
    cases p <;> (try rename_i s; cases s) <;> simp only [Execution.AsyncFootprint] at hf
    all_goals first
      | (obtain ⟨-, ⟨_, _, _, _, ⟨pc, hk⟩, -⟩ | ⟨_, _, _, ⟨pc, hk⟩, -⟩⟩ := hf <;>
         exact (noev hk (by simp) (by simp) (by simp [fenceK]) (by simp)).elim)
      | (rcases hf with ⟨s, hc, rfl⟩ | ⟨pc, hk⟩
         · obtain ⟨rfl, rfl⟩ := copy hc
           exact .inr (.inl ⟨rfl, rfl, rfl⟩)
         · exact (noev hk (by simp) (by simp) (by simp [fenceK]) (by simp)).elim)
      | (obtain ⟨s, hc, -, rfl⟩ := hf
         obtain ⟨rfl, rfl⟩ := copy hc
         exact .inr (.inr ⟨rfl, rfl⟩))
      | (obtain ⟨s, hc, hj⟩ := hf
         obtain ⟨-, rfl⟩ := copy hc
         simp [spec, AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets] at hj)
      | (obtain ⟨s, r, hc, hw, -⟩ := hf
         obtain ⟨-, rfl⟩ := copy hc
         simp [spec] at hw)
      | (obtain ⟨_, _, ⟨pc, hk⟩, -⟩ := hf
         exact (noev hk (by simp) (by simp) (by simp [fenceK]) (by simp)).elim)

/-- With the fence the store precedes the copy's source read at each byte of `s`: the fence lies
between them in program order and covers the shared bytes of the CTA (`ProxyBefore`). -/
theorem fenced_before {l : Loc} (hl : sA.Covers l) :
    modelCausality L1 (X true) l (.thread (0, 0)) (.async (0, 2) (.read .copy)) := by
  refine ⟨⟨sA, false, ⟨rfl, .inl ⟨spec, ⟨2, rfl⟩, rfl⟩⟩, hl⟩, .inl ⟨(0, 1), some (.shared .cta),
    none, ⟨1, rfl⟩, by decide, ⟨hl.1, hl.2.1⟩, ⟨by decide, by decide, rfl⟩, .single (.inl ?_),
    .single (.inl ?_)⟩⟩ <;>
    refine ⟨rfl, by decide, by decide, ?_⟩ <;>
    simp [SameAccess, Execution.get, X, trace, fenceK, Event.acc]

/-- With the fence no two accesses of the execution are a data race. -/
theorem fenced_no_race : ¬ Race L1 (X true) := by
  rintro ⟨e, f, a, b, l, ⟨hne, we, wf, he, hf, hw, l', hl1, hl2⟩, -, hcov, -, h1, h2, -⟩
  rcases intent_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases intent_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact hne rfl
    | exact h1 (.direct (fenced_before hcov))
    | exact h2 (.direct (fenced_before hcov))
    | (simp [Acc.Covers, Loc.InRange, sA, gA] at hl1 hl2; simp [hl1.1] at hl2)

end ProxyFence

end

end PTX.Tests.Progress
