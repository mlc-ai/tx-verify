-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Mathlib.Tactic

/-!
# Litmus tests of the memory model with `atom` and `red` (MEM-ATOMICITY, ERR-DATA-RACE,
MEM-RELEASE-ACQUIRE)

* §8.10.3 Litmus Test 1: two morally strong `atom.sys.inc` of `x = 0`. In every execution that
  satisfies MEM-READS-FROM and MEM-ATOMICITY, one of them reads 0 from W0 and the other reads 1 from
  the first, so the last one writes 2 and follows the first in coherence order ("FINAL STATE : x ==
  2").
* An `atom` and a plain `st` of the same word in two threads are not morally strong: unordered,
  they are a race.
* §8.11.1 message passing with `red`: the `red` does not acquire, so nothing synchronizes the two
  threads and the outcome `%r1 == 0 AND flag == 2` is not excluded; with an acquiring `atom`
  instead, the release store synchronizes with it and the load cannot read the initial `x`.
-/

namespace PTX.Tests.AtomicLitmus
noncomputable section

/-! ## Litmus Test 1 -/

/-- Two threads in two CTAs; `.sys` includes both. -/
private def L : Launch := { grid := 2, block := 1, params := fun _ => none }
private def x : Loc := ⟨.global, 0, 0⟩
/-- `atom.sys.inc.u32` at `x` with the operand `0xffffffff`, so `inc` adds one (THREAD-ATOMIC). -/
private def a : Acc := { loc := x, size := 4, relaxed := true, scope := .sys }
/-- The bytes an `inc` writes from the bytes it read (THREAD-ATOMIC-OP). -/
private def incF (old : List (Option Byte)) : Exec (List Byte) := do
  let v ← rmwValue [] .inc (.int .u 32) (← rebuild 3 old) [.bits 32 0xffffffff]
  pure v.toBytes
private def bytes (n : Nat) : List Byte := (Value.bits 32 (BitVec.ofNat 64 n)).toBytes
/-- `x` holds 0 at launch. -/
private def mem0 : Mem0 := fun l =>
  if l.space = .global ∧ l.cta = 0 ∧ l.addr < 4 then some ((bytes 0)[l.addr]?) else none
private def e0 : EvId := (0, 0)
private def e1 : EvId := (1, 0)

private theorem rebuild_bytes (n : Nat) :
    rebuild 3 ((bytes n).map some) = .ok (Value.bits 32 (BitVec.ofNat 64 n)) := by
  simp [bytes, rebuild, Value.toBytes, Value.bytes, List.range_succ, Value.byteAt]; rfl
private theorem inc0 : incF ((bytes 0).map some) = .ok (bytes 1) := by
  simp only [incF, rebuild_bytes]
  simp [rmwValue, Value.bitPattern, Value.bytes, Value.ofWidth, AtomOp.apply, bytes]; rfl
private theorem inc1 : incF ((bytes 1).map some) = .ok (bytes 2) := by
  simp only [incF, rebuild_bytes]
  simp [rmwValue, Value.bitPattern, Value.bytes, Value.ofWidth, AtomOp.apply, bytes]; rfl

section Litmus1
variable {X : Execution} {pc0 pc1 : Nat} {o0 o1 : List (Option Byte)}

private theorem rmw_of_get {e : EvId} {pc : Nat} {o : List (Option Byte)}
    (h : X.get e = some ⟨pc, .rmw a o (incF o).toOption⟩) : X.Rmw e a o (incF o).toOption :=
  ⟨pc, h⟩

private theorem strong (h0 : X.get e0 = some ⟨pc0, .rmw a o0 (incF o0).toOption⟩)
    (h1 : X.get e1 = some ⟨pc1, .rmw a o1 (incF o1).toOption⟩) {e f : EvId}
    (he : e = e0 ∨ e = e1) (hf : f = e0 ∨ f = e1) : RmwStrong L X (.thread e) (.thread f) := by
  have acc : ∀ g, g = e0 ∨ g = e1 → X.Access g a true := by
    rintro g (rfl | rfl)
    · exact Or.inr (Or.inr ⟨_, _, rmw_of_get h0⟩)
    · exact Or.inr (Or.inr ⟨_, _, rmw_of_get h1⟩)
  have hsc : ∀ g, g = e0 ∨ g = e1 → ∀ h, h = e0 ∨ h = e1 →
      StrongScoped L X (.thread g) a h.1 := by
    intro g hg h hh
    refine ⟨⟨true, acc g hg⟩, Or.inl rfl, ?_⟩
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
      simp [MbarScopeIncludes, a, L, Launch.threads, e0, e1]
  refine ⟨a, a, acc e he, acc f hf, Or.inr ⟨hsc e he f hf, hsc f hf e he⟩, Iff.rfl, a, a,
    rfl, rfl, rfl, rfl⟩

private theorem rmwAt {e : EvId} {pc : Nat} {o : List (Option Byte)}
    (h : X.get e = some ⟨pc, .rmw a o (incF o).toOption⟩) :
    X.RmwAt (.thread e) x 4 :=
  ⟨a, o, _, rmw_of_get h, rfl, rfl⟩

/-- The source of byte `k` of each `inc` is W0 or the other `inc`. -/
private theorem source (hA : AtomicOk L X)
    (h0 : X.get e0 = some ⟨pc0, .rmw a o0 (incF o0).toOption⟩)
    (h1 : X.get e1 = some ⟨pc1, .rmw a o1 (incF o1).toOption⟩)
    (hw : ∀ w a' bs, X.MemWrites w a' bs → a'.Overlap a → w = .thread e0 ∨ w = .thread e1)
    (hrf : RfWf mem0 X) {e f : EvId} {o : List (Option Byte)} {pc : Nat}
    (he : e = e0 ∨ e = e1) (hef : ∀ g, (g = e0 ∨ g = e1) → g ≠ e → g = f)
    (h : X.get e = some ⟨pc, .rmw a o (incF o).toOption⟩) {k : Nat} (hk : k < 4) :
    X.rf (.thread e) k = none ∨ X.rf (.thread e) k = some (.thread f) := by
  have hr : X.MemReads (.thread e) a o := Or.inr ⟨_, rmw_of_get h⟩
  have := (hrf _ _ _ hr).2 k hk
  cases hk' : X.rf (.thread e) k with
  | none => exact Or.inl rfl
  | some w =>
    rw [hk'] at this
    obtain ⟨a', bs', hw', hcov, -⟩ := this
    have hov : a'.Overlap a :=
      ⟨x.at k, hcov, by simp [Acc.Covers, Loc.InRange, Loc.at, a, x]; omega⟩
    rcases hw w a' bs' hw' hov with rfl | rfl
    · by_cases hg : e0 = e
      · subst hg
        exact absurd (.single ⟨x, 4, rmwAt h, rmwAt h, strong h0 h1 he he, k, 0, hk, hk'⟩)
          (hA.acyclic (.thread e0))
      · exact Or.inr (by rw [hef e0 (Or.inl rfl) hg])
    · by_cases hg : e1 = e
      · subst hg
        exact absurd (.single ⟨x, 4, rmwAt h, rmwAt h, strong h0 h1 he he, k, 0, hk, hk'⟩)
          (hA.acyclic (.thread e1))
      · exact Or.inr (by rw [hef e1 (Or.inr rfl) hg])

/-- Each byte of an `inc` that read every byte from W0 is the launch content 0. -/
private theorem old_initial (hrf : RfWf mem0 X) {e : EvId} {pc : Nat} {o : List (Option Byte)}
    (h : X.get e = some ⟨pc, .rmw a o (incF o).toOption⟩)
    (hk : ∀ k < 4, X.rf (.thread e) k = none) : o = (bytes 0).map some := by
  have hr : X.MemReads (.thread e) a o := Or.inr ⟨_, rmw_of_get h⟩
  obtain ⟨hlen, hb⟩ := hrf _ _ _ hr
  apply List.ext_getElem?
  intro k
  by_cases hk4 : k < 4
  · have := hb k hk4
    rw [hk k hk4] at this
    have hm : mem0 (a.loc.at k) = some ((bytes 0)[k]?) := by
      simp [mem0, a, x, Loc.at, hk4]
    rw [this _ hm]
    interval_cases k <;> rfl
  · have : o.length = 4 := hlen
    have hb4 : ((bytes 0).map some).length = 4 := rfl
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Each byte of an `inc` that read every byte from the other `inc` `w` is that write's byte. -/
private theorem old_from (hrf : RfWf mem0 X) {e w : EvId} {pc pcw : Nat}
    {o ow : List (Option Byte)} {n : List Byte}
    (h : X.get e = some ⟨pc, .rmw a o (incF o).toOption⟩)
    (hw : X.get w = some ⟨pcw, .rmw a ow (incF ow).toOption⟩) (hn : incF ow = .ok n)
    (hn4 : n.length = 4) (hk : ∀ k < 4, X.rf (.thread e) k = some (.thread w)) :
    o = n.map some := by
  have hr : X.MemReads (.thread e) a o := Or.inr ⟨_, rmw_of_get h⟩
  obtain ⟨hlen, hb⟩ := hrf _ _ _ hr
  apply List.ext_getElem?
  intro k
  by_cases hk4 : k < 4
  · have := hb k hk4
    rw [hk k hk4] at this
    obtain ⟨a', bs', hw', -, hbk⟩ := this
    rcases hw' with ⟨pc', hwr⟩ | ⟨old, pc', hrm⟩
    · rw [hw] at hwr; cases hwr
    · rw [hw] at hrm
      simp only [Option.some.injEq, Event.mk.injEq, Kind.rmw.injEq] at hrm
      obtain ⟨-, rfl, rfl, hbs⟩ := hrm
      rw [hn] at hbs
      cases hbs
      rw [hbk]
      simp [wbyte, a, x, Loc.at, List.getElem?_eq_getElem (show k < n.length by omega)]
  · have : o.length = 4 := hlen
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- §8.10.3 Litmus Test 1: whichever `inc` reads W0, the other reads its 1 and writes 2, and
the second follows the first in coherence order (`AtomicReads`, a `CoStep` edge). -/
theorem litmus1 (hA : AtomicOk L X)
    (h0 : X.get e0 = some ⟨pc0, .rmw a o0 (incF o0).toOption⟩)
    (h1 : X.get e1 = some ⟨pc1, .rmw a o1 (incF o1).toOption⟩)
    (hw : ∀ w a' bs, X.MemWrites w a' bs → a'.Overlap a → w = .thread e0 ∨ w = .thread e1)
    (hrf : RfWf mem0 X) :
    (AtomicReads L X (.thread e0) (.thread e1) ∧ incF o0 = .ok (bytes 1) ∧
      incF o1 = .ok (bytes 2)) ∨
    (AtomicReads L X (.thread e1) (.thread e0) ∧ incF o1 = .ok (bytes 1) ∧
      incF o0 = .ok (bytes 2)) := by
  have he0 : e0 = e0 ∨ e0 = e1 := Or.inl rfl
  have he1 : e1 = e0 ∨ e1 = e1 := Or.inr rfl
  have hne : e0 ≠ e1 := by decide
  have oth0 : ∀ g, (g = e0 ∨ g = e1) → g ≠ e0 → g = e1 := by rintro g (rfl | rfl) h <;> simp_all
  have oth1 : ∀ g, (g = e0 ∨ g = e1) → g ≠ e1 → g = e0 := by rintro g (rfl | rfl) h <;> simp_all
  have s0 := fun k (hk : k < 4) => source hA h0 h1 hw hrf he0 oth0 h0 hk
  have s1 := fun k (hk : k < 4) => source hA h0 h1 hw hrf he1 oth1 h1 hk
  -- `q` reading from `p` at byte `k` is an atomic read.
  have rd01 : ∀ k < 4, X.rf (.thread e1) k = some (.thread e0) →
      AtomicReads L X (.thread e0) (.thread e1) := fun k hk h =>
    ⟨x, 4, rmwAt h0, rmwAt h1, strong h0 h1 he0 he1, k, 0, hk, h⟩
  have rd10 : ∀ k < 4, X.rf (.thread e0) k = some (.thread e1) →
      AtomicReads L X (.thread e1) (.thread e0) := fun k hk h =>
    ⟨x, 4, rmwAt h1, rmwAt h0, strong h0 h1 he1 he0, k, 0, hk, h⟩
  have uniq : ∀ k < 4, X.rf (.thread e0) k ≠ X.rf (.thread e1) k := fun k hk =>
    hA.unique (.thread e0) (.thread e1) x 4 k (rmwAt h0) (rmwAt h1)
      (by simp [hne]) (strong h0 h1 he0 he1) hk
  have cyc : ¬ (AtomicReads L X (.thread e0) (.thread e1) ∧
      AtomicReads L X (.thread e1) (.thread e0)) := fun ⟨p, q⟩ =>
    hA.acyclic (.thread e0) (.tail (.single p) q)
  rcases s1 0 (by norm_num) with h10 | h10
  · -- e1 read byte 0 from W0, so e0 read it from e1: e1 is first.
    have h00 : X.rf (.thread e0) 0 = some (.thread e1) := by
      rcases s0 0 (by norm_num) with h | h
      · exact absurd (h.trans h10.symm) (uniq 0 (by norm_num))
      · exact h
    have all : ∀ k < 4, X.rf (.thread e1) k = none ∧ X.rf (.thread e0) k = some (.thread e1) := by
      intro k hk
      rcases s1 k hk with h | h
      · rcases s0 k hk with h' | h'
        · exact absurd (h'.trans h.symm) (uniq k hk)
        · exact ⟨h, h'⟩
      · exact absurd ⟨rd01 k hk h, rd10 0 (by norm_num) h00⟩ cyc
    have ho1 := old_initial hrf h1 fun k hk => (all k hk).1
    have hi1 : incF o1 = .ok (bytes 1) := by rw [ho1]; exact inc0
    have ho0 := old_from hrf h0 h1 hi1 rfl fun k hk => (all k hk).2
    refine Or.inr ⟨rd10 0 (by norm_num) h00, hi1, by rw [ho0]; exact inc1⟩
  · -- e1 read byte 0 from e0: e0 is first.
    have h00 : X.rf (.thread e0) 0 = none := by
      rcases s0 0 (by norm_num) with h | h
      · exact h
      · exact absurd ⟨rd01 0 (by norm_num) h10, rd10 0 (by norm_num) h⟩ cyc
    have all : ∀ k < 4, X.rf (.thread e0) k = none ∧ X.rf (.thread e1) k = some (.thread e0) := by
      intro k hk
      rcases s0 k hk with h | h
      · rcases s1 k hk with h' | h'
        · exact absurd (h.trans h'.symm) (uniq k hk)
        · exact ⟨h, h'⟩
      · exact absurd ⟨rd01 0 (by norm_num) h10, rd10 k hk h⟩ cyc
    have ho0 := old_initial hrf h0 fun k hk => (all k hk).1
    have hi0 : incF o0 = .ok (bytes 1) := by rw [ho0]; exact inc0
    have ho1 := old_from hrf h1 h0 hi0 rfl fun k hk => (all k hk).2
    refine Or.inl ⟨rd01 0 (by norm_num) h10, hi0, by rw [ho1]; exact inc1⟩

end Litmus1

/-! ## An `atom` and a plain store of the same word race -/

/-- A `.relaxed.sys` `atom` (thread 0) and a weak `st` (thread 1) of `x` with different values are
not morally strong, so when neither is ordered before the other they are a race. -/
example {X : Execution} {pc pc' : Nat} {o : List (Option Byte)} {n bs : List Byte}
    (h0 : X.get e0 = some ⟨pc, .rmw a o (some n)⟩)
    (h1 : X.get e1 = some ⟨pc', .wr { loc := x, size := 4 } bs⟩) (hne : n ≠ bs)
    (h01 : ¬ modelCausality L X x (.thread e0) (.thread e1))
    (h10 : ¬ modelCausality L X x (.thread e1) (.thread e0)) :
    Race L X := by
  refine ⟨.thread e0, .thread e1, a, { loc := x, size := 4 }, x,
    ⟨by simp [e0, e1], true, true, Or.inr (Or.inr ⟨o, some n, pc, h0⟩),
      Or.inr (Or.inl ⟨bs, ⟨pc', h1⟩, rfl⟩),
      Or.inl rfl, x, by simp [Acc.Covers, Loc.InRange, a, x], by simp [Acc.Covers, Loc.InRange, x]⟩,
    ⟨rfl, rfl⟩, by simp [Acc.Covers, Loc.InRange, a, x], ?_,
    fun h => h01 ((ByteCausality.direct_iff_of_global rfl).1 h),
    fun h => h10 ((ByteCausality.direct_iff_of_global rfl).1 h), ?_⟩
  · rintro ⟨⟨i, j, hi, hj, hij⟩ | ⟨-, ⟨-, hs, -⟩⟩, -⟩
    · cases hi; cases hj; simp [e0, e1] at hij
    · simp [Acc.Strong] at hs
  · intro hv
    exact hne (hv.2.2.2 n bs (Or.inr ⟨o, pc, h0⟩) (Or.inl ⟨pc', h1⟩))

/-! ## Message passing with `red` (§8.11.1) -/

private def xA : Acc := { loc := x, size := 4 }
private def flag : Loc := ⟨.global, 0, 4⟩
/-- `st.release.gpu.u32 [flag], 1`. -/
private def wFlag : Acc := { loc := flag, size := 4, release := true, scope := .gpu }
/-- `red.sys.global.add.u32 [flag], 1`: relaxed, and its read does not acquire (THREAD-ATOMIC). -/
private def redFlag : Acc := { loc := flag, size := 4, relaxed := true, scope := .sys }
/-- The same with `atom.acquire.sys.global.add.u32`. -/
private def atomFlag : Acc := { loc := flag, size := 4, acquire := true, scope := .sys }

/-- T1: `st [x], 42; st.release.gpu [flag], 1`. T2: the read-modify-write of `flag` reads 1 from
T1's release store and writes 2, and `ld.weak [x]` reads 0 from W0. -/
private def mp (rmw : Acc) : Execution where
  tr g := if g = 0 then [⟨0, .wr xA (bytes 42)⟩, ⟨1, .wr wFlag (bytes 1)⟩]
    else if g = 1 then [⟨0, .rmw rmw ((bytes 1).map some) (some (bytes 2))⟩,
      ⟨1, .rd xA ((bytes 0).map some)⟩]
    else []
  rf r _ := if r = .thread (1, 0) then some (.thread (0, 1)) else none

/-- Every event of the message-passing execution is a read, a write or a read-modify-write. -/
private theorem mp_kinds {rmw : Acc} {e : EvId} {ev : Event} (h : (mp rmw).get e = some ev) :
    (∃ a bs, ev.kind = .wr a bs) ∨ (∃ a bs, ev.kind = .rd a bs) ∨
      ∃ a o n, ev.kind = .rmw a o n := by
  obtain ⟨g, i⟩ := e
  simp only [Execution.get, mp] at h
  split_ifs at h
  · rcases i with _ | _ | i <;> simp at h <;> subst h <;> simp
  · rcases i with _ | _ | i <;> simp at h <;> subst h <;> simp
  · simp at h

/-- The `red` does not acquire, so no read of the execution synchronizes with a release write. -/
theorem mp_red_no_sync (e f : EvId) : ¬ synchronizesWith L (mp redFlag) e f := by
  rintro ⟨a', b, bs, cs, -, hr, -, hacq, -⟩
  obtain ⟨g, i⟩ := f
  rcases hr with ⟨pc, h⟩ | ⟨n, pc, h⟩ <;> simp only [Execution.get, mp] at h <;> split_ifs at h <;>
    rcases i with _ | _ | i <;> simp at h <;> (try obtain ⟨-, rfl, -⟩ := h) <;>
    simp_all [xA, redFlag]

/-- Threads 0 and 1 are in different CTAs and clusters and the execution has no barrier,
mbarrier or acquiring access, so happens-before relates events of one thread only. -/
theorem mp_red_baseCausality {e f : EvId} (h : baseCausality L (mp redFlag) e f) : e.1 = f.1 := by
  have step : ∀ e f, (po (mp redFlag) e f ∨ CtaBarSync L (mp redFlag) e f ∨
      MSync L (mp redFlag) e f ∨ ClusterSync L (mp redFlag) e f ∨
      WarpBarSync L (mp redFlag) e f ∨ synchronizesWith L (mp redFlag) e f ∨
      FenceSync L (mp redFlag) e f) → e.1 = f.1 := by
    intro e f hs
    rcases hs with hp | ⟨⟨-, -, hc⟩, -⟩ | ⟨x', w, m, rs, as, ⟨tx, cnt, pc, hx⟩, -⟩ |
      ⟨⟨-, -, hc⟩, -⟩ | ⟨i, j, ⟨⟨⟨-, -, hc⟩, -⟩, -⟩, -⟩ | hm | hf
    · exact hp.1
    · simpa [L] using hc
    · rcases mp_kinds hx with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
    · simp only [Launch.oneDim_clusterOfCta (L := L) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩] at hc
      simpa [L] using hc
    · simpa [L] using hc
    · exact absurd hm (mp_red_no_sync e f)
    · refine absurd hf (not_fenceSync_of_noFence (fun e sem s ⟨pc, hx⟩ => ?_) e f)
      rcases mp_kinds hx with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  induction h with
  | single hs => exact step _ _ hs
  | tail _ hs ih => exact ih.trans (step _ _ hs)

/-- The outcome `%r1 == 0 AND flag == 2` is not excluded: T1's store of `x` is not before T2's load
in the visibility order, so MEM-READ-AXIOMS do not stop the load from reading W0. -/
example : ¬ modelCausality L (mp redFlag) x (.thread (0, 0)) (.thread (1, 1)) := by
  rintro (hb | ⟨_, _, _, _, hr, _, _, _, _⟩)
  · exact absurd (mp_red_baseCausality hb) (by decide)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hzero, _⟩ := hr
    cases hzero

/-- With `atom.acquire` instead of `red`, the release store synchronizes with the `atom`, so T1's
store of `x` happens before T2's load. -/
theorem mp_atom_baseCausality : baseCausality L (mp atomFlag) (0, 0) (1, 1) := by
  have po0 : po (mp atomFlag) (0, 0) (0, 1) := by
    refine ⟨rfl, by decide, by simp [mp], fun hs => ?_⟩
    have := hs.2 1 le_rfl
    simp [Execution.get, mp, Event.acc, Acc.shift, xA, wFlag] at this
  have po1 : po (mp atomFlag) (1, 0) (1, 1) := by
    refine ⟨rfl, by decide, by simp [mp], fun hs => ?_⟩
    have := hs.2 1 le_rfl
    simp [Execution.get, mp, Event.acc, Acc.shift, xA, atomFlag] at this
  have sync : synchronizesWith L (mp atomFlag) (0, 1) (1, 0) :=
    ⟨wFlag, atomFlag, bytes 1, (bytes 1).map some, Or.inl ⟨1, by simp [Execution.get, mp]⟩,
      Or.inr ⟨some (bytes 2), 0, by simp [Execution.get, mp]⟩, rfl, rfl, rfl, rfl, by decide,
      by simp [MbarScopeIncludes, wFlag, L, Launch.threads],
      by simp [MbarScopeIncludes, atomFlag, L, Launch.threads], fun k _ => by simp [mp]⟩
  exact .tail (.tail (.single (Or.inl po0))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sync))))))) (Or.inl po1)

/-- So with `atom.acquire` the load cannot read the initial `x`: MEM-READ-AXIOMS reject the
execution. -/
example : ¬ Hidden L (mp atomFlag) := by
  intro h
  have := h (.thread (1, 1)) xA ((bytes 0).map some) 0 (.thread (0, 0)) xA (bytes 42)
    (Or.inl ⟨1, by simp [Execution.get, mp]⟩) (by decide) (Or.inl ⟨0, by simp [Execution.get, mp]⟩)
    (by simp [Acc.Covers, Loc.InRange, xA, Loc.at]) (.direct (.inl mp_atom_baseCausality))
  simp [mp] at this

end
end PTX.Tests.AtomicLitmus
