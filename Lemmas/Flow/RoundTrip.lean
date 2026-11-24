-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.MemTmpl
public import Lemmas.Clc.ClcCompleteConsistentReadFrame

@[expose] public section

/-! # A 128-bit value moved through two halves

A kernel that reads a 128-bit value from memory and moves it through two 64-bit halves
(`unpack` then `pack`) before using it continues with `joinValue` of the halves, or faults
in the `unpack`. `roundTrip128` names that outcome, so a site machine can branch on what the
code will actually use instead of on how the loaded bytes rebuild. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- The value a 128-bit `unpack` followed by the `pack` of its halves leaves, or `none` when
the `unpack` faults. -/
def roundTrip128 (v : Value) : Option Value :=
  if v.bytes = 16 ∧ (splitValue 128 v).1.bytes = 8 ∧ (splitValue 128 v).2.bytes = 8 then
    some (joinValue (splitValue 128 v).1 (splitValue 128 v).2)
  else none

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- No assumption of `A` names the 128-bit unpack of a register into two halves. -/
def NoUnpack128 (A : List Assumption) : Prop :=
  ∀ (lo hi src : Nat) (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A,
    a.localRule L g t (.move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg src]⟩) = none

/-- No assumption of `A` names the 128-bit pack of two halves into one register. -/
def NoPack128 (A : List Assumption) : Prop :=
  ∀ (d lo hi : Nat) (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A,
    a.localRule L g t (.move ⟨.pack, .int .b 128, [some d], [.reg lo, .reg hi]⟩) = none

/-- The `unpack` of a value whose round trip succeeds. -/
theorem out_unpack128 {t : TState} {pc : Nat} {lo hi r : Nat} {v w : Value}
    (hc : K.code[pc]? = some ⟨none,
      .move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg r]⟩⟩)
    (hpc : t.pc = pc)
    (hf : t.fault = none) (hr : t.regs r = some v) (hq : roundTrip128 v = some w)
    (hN : NoUnpack128 A)
    (hS : Assumption.SegFreePc A pc := by seg_free_pc) :
    out K A L g t =
      .tau (PTX.next (setReg (setReg t lo (splitValue 128 v).1) hi (splitValue 128 v).2)) := by
  unfold roundTrip128 at hq
  split_ifs at hq with hb
  obtain ⟨h16, h1, h2⟩ := hb
  simp [out, hf, hpc, hc, guardHolds, Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap,
    List.isEmpty_nil, ↓reduceIte, hS.exec, execLocalRule_of_none (hN lo hi r L g t), execLocal,
    Op.rule, MoveInstr.rule, DType.width, execMove,
    readValue, readReg, hr, h16, h1, h2, pure, Except.pure, bind, Except.bind]

/-- The `unpack` of a value whose round trip fails is undefined behaviour. -/
theorem out_unpack128_ub {t : TState} {pc : Nat} {lo hi r : Nat} {v : Value}
    (hc : K.code[pc]? = some ⟨none,
      .move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg r]⟩⟩)
    (hpc : t.pc = pc)
    (hf : t.fault = none) (hr : t.regs r = some v) (hq : roundTrip128 v = none)
    (hN : NoUnpack128 A)
    (hS : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ f, out K A L g t = .ev (.ub f) := by
  unfold roundTrip128 at hq
  split_ifs at hq with hb
  refine ⟨.typeMismatch, ?_⟩
  by_cases h16 : v.bytes = 16
  · have h12 : ¬ ((splitValue 128 v).1.bytes = 8 ∧ (splitValue 128 v).2.bytes = 8) :=
      fun h => hb ⟨h16, h⟩
    simp [out, hf, hpc, hc, guardHolds, Op.isLocal, Op.varyingSregs, Opnd.varying?,
      List.filterMap, List.isEmpty_nil, ↓reduceIte, hS.exec,
      execLocalRule_of_none (hN lo hi r L g t), execLocal,
      Op.rule, MoveInstr.rule, DType.width, execMove,
      readValue, readReg, hr, h16, h12, pure, Except.pure, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · simp [out, hf, hpc, hc, guardHolds, Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap,
      List.isEmpty_nil, ↓reduceIte, hS.exec, execLocalRule_of_none (hN lo hi r L g t), execLocal,
    Op.rule, MoveInstr.rule, DType.width, execMove,
      readValue, readReg, hr, h16, pure, Except.pure, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]

/-- The `pack` of two 64-bit halves. -/
theorem out_pack128 {t : TState} {pc : Nat} {d lo hi : Nat} {x y : Value}
    (hc : K.code[pc]? = some ⟨none,
      .move ⟨.pack, .int .b 128, [some d], [.reg lo, .reg hi]⟩⟩)
    (hpc : t.pc = pc)
    (hf : t.fault = none) (hlo : t.regs lo = some x) (hhi : t.regs hi = some y)
    (hx : x.bytes = 8) (hy : y.bytes = 8) (hP : NoPack128 A)
    (hS : Assumption.SegFreePc A pc := by seg_free_pc) :
    out K A L g t = .tau (PTX.next (setReg t d (joinValue x y))) := by
  simp [out, hf, hpc, hc, guardHolds, Op.isLocal, Op.varyingSregs, Opnd.varying?, List.filterMap,
    List.isEmpty_nil, ↓reduceIte, hS.exec, execLocalRule_of_none (hP d lo hi L g t), execLocal,
    Op.rule, MoveInstr.rule, DType.width, execMove,
    readValue, readReg, hlo, hhi, hx, hy, pure, Except.pure, bind, Except.bind]

/-- A `clcQuery` of a register that does not hold a response is undefined behaviour. -/
theorem out_clcQuery_ub {t : TState} {pc : Nat} {q : ClcQuery} {dst src : Nat} {v : Value}
    (hc : K.code[pc]? = some ⟨none, .clcQuery q dst (.reg src)⟩) (hpc : t.pc = pc)
    (hf : t.fault = none) (hr : t.regs src = some v) (hv : ∀ r, v ≠ .clc r) :
    out K A L g t = .ev (.ub .typeMismatch) := by
  cases v <;> first
    | exact absurd rfl (hv _)
    | simp [out, hf, hpc, hc, guardHolds, Op.isLocal, eventTmpl, clcTmpl, ofExec, readValue,
        readReg, hr, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- A 128-bit value in `r` moved through `lo`/`hi` into `d` and queried: when the round trip
leaves a response, local steps reach the query holding it; otherwise the thread is dead. -/
theorem roundTrip_query {u : TState} {pc : Nat} {r lo hi d dst : Nat} {q : ClcQuery}
    {v : Value} (hlh : lo ≠ hi)
    (h1 : K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg r]⟩⟩)
    (h2 : K.code[pc + 1]? = some ⟨none, .move ⟨.pack, .int .b 128, [some d], [.reg lo, .reg hi]⟩⟩)
    (h3 : K.code[pc + 2]? = some ⟨none, .clcQuery q dst (.reg d)⟩)
    (hpc : u.pc = pc) (hf : u.fault = none) (hr : u.regs r = some v)
    (hN : NoUnpack128 A) (hP : NoPack128 A)
    (hS : Assumption.SegFreePc A pc := by seg_free_pc)
    (hS1 : Assumption.SegFreePc A (pc + 1) := by seg_free_pc) :
    (∀ rr, roundTrip128 v = some (.clc rr) →
      Relation.ReflTransGen (Tau K A L g) u (PTX.next (setReg (PTX.next (setReg (setReg u lo
        (splitValue 128 v).1) hi (splitValue 128 v).2)) d (.clc rr)))) ∧
    ((∀ rr, roundTrip128 v ≠ some (.clc rr)) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u) := by
  cases hq : roundTrip128 v with
  | none =>
    refine ⟨fun _ h => (nomatch h), fun _ => ?_⟩
    obtain ⟨f, hout⟩ := out_unpack128_ub (A := A) (L := L) (g := g) h1 hpc hf hr hq hN
    exact Machine.dead_of_ub hout
  | some w =>
    have hq' := hq
    unfold roundTrip128 at hq'
    split_ifs at hq' with hb
    obtain ⟨-, hx, hy⟩ := hb
    have hw : joinValue (splitValue 128 v).1 (splitValue 128 v).2 = w := Option.some.inj hq'
    have o1 := out_unpack128 (A := A) (L := L) (g := g) h1 hpc hf hr hq hN
    have o2 := out_pack128 (A := A) (L := L) (g := g)
      (t := PTX.next (setReg (setReg u lo (splitValue 128 v).1) hi (splitValue 128 v).2)) h2
      (by simp [PTX.next, setReg, hpc]) (by simpa [PTX.next, setReg] using hf)
      (by simp [PTX.next, setReg, Function.update_of_ne hlh]) (by simp [PTX.next, setReg]) hx hy hP
    rw [hw] at o2
    refine ⟨fun rr h => ?_, fun hn => ?_⟩
    · obtain rfl := Option.some.inj h
      exact .tail (.single o1) o2
    · refine Machine.dead_of_tau o1 (Machine.dead_of_tau o2 (Machine.dead_of_ub (f :=
      .typeMismatch) ?_))
      exact out_clcQuery_ub (v := w) h3 (by simp [PTX.next, setReg, hpc]) (by simpa [PTX.next,
        setReg] using hf)
        (by simp [PTX.next, setReg]) (fun rr h => hn rr (by rw [h]))

/-- Bytes of a read that rebuild to a value whose round trip through two halves is a cluster
launch control response. -/
def ResponseBytes (bs : List (Option Byte)) (rr : ClcResponse) : Prop :=
  ∃ v, rebuild 3 bs = .ok v ∧ roundTrip128 v = some (.clc rr)

/-- The read of a cluster launch control response into `r`, moved through `lo`/`hi` into `d`
and queried. When the bytes are a response, local steps reach the query with `d` holding it
and every register other than `r`, `lo`, `hi` and `d` unchanged; otherwise the thread is dead
(a fault in the read, the `unpack` or the query). -/
theorem response_step {t : TState} {pc : Nat} {r lo hi d dst : Nat} {q : ClcQuery}
    {bs : List (Option Byte)} (hlh : lo ≠ hi)
    (h1 : K.code[pc + 1]? = some ⟨none, .move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg r]⟩⟩)
    (h2 : K.code[pc + 2]? = some ⟨none, .move ⟨.pack, .int .b 128, [some d], [.reg lo, .reg hi]⟩⟩)
    (h3 : K.code[pc + 3]? = some ⟨none, .clcQuery q dst (.reg d)⟩)
    (hpc : t.pc = pc) (hsub : t.sub = 0) (hacc : t.acc = []) (hf : t.fault = none)
    (hN : NoUnpack128 A) (hP : NoPack128 A)
    (hS : Assumption.SegFreePc A (pc + 1) := by seg_free_pc)
    (hS2 : Assumption.SegFreePc A (pc + 2) := by seg_free_pc) :
    (∀ rr, ResponseBytes bs rr →
      ∃ t', Relation.ReflTransGen (Tau K A L g) (afterLoad t [r] bs) t' ∧ t'.pc = pc + 3 ∧
        t'.sub = 0 ∧ t'.acc = [] ∧ t'.fault = none ∧ t'.regs d = some (.clc rr) ∧
        ∀ x, x ∉ [r, lo, hi, d] → t'.regs x = t.regs x) ∧
    ((∀ rr, ¬ ResponseBytes bs rr) →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) (afterLoad t [r] bs)) := by
  cases hv : rebuild 3 bs with
  | error f =>
    refine ⟨fun rr hr => ?_, fun _ => ?_⟩
    · obtain ⟨v, h, -⟩ := hr
      rw [hv] at h; cases h
    · exact Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])
  | ok v =>
    rw [PTX.Proof.afterLoad_ok hsub hacc hv]
    have hrq := roundTrip_query (K := K) (A := A) (L := L) (g := g)
      (u := { setReg t r v with pc := t.pc + 1, sub := 0, acc := [] }) (v := v) hlh h1 h2 h3
      (by simp [hpc]) (by simpa [setReg] using hf) (by simp [setReg]) hN hP
    refine ⟨fun rr ⟨v', hv', hrr⟩ => ?_, fun hn => hrq.2 fun rr h => hn rr ⟨v, hv, h⟩⟩
    rw [hv] at hv'
    cases hv'
    refine ⟨_, hrq.1 rr hrr, by simp [PTX.next, setReg, hpc], by simp [PTX.next, setReg],
      by simp [PTX.next, setReg], by simpa [PTX.next, setReg] using hf,
      by simp [PTX.next, setReg], fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [PTX.next, setReg, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
      Function.update_of_ne hx.2.2.1, Function.update_of_ne hx.2.2.2]

/-- The response a read's bytes carry, if any: the successor a site machine takes after the
read. -/
def responseOf (bs : List (Option Byte)) : Option ClcResponse :=
  match rebuild 3 bs with
  | .ok v => match roundTrip128 v with
    | some (.clc rr) => some rr
    | _ => none
  | .error _ => none

theorem responseOf_some {bs : List (Option Byte)} {rr : ClcResponse} :
    responseOf bs = some rr ↔ ResponseBytes bs rr := by
  unfold responseOf ResponseBytes
  constructor
  · intro h
    split at h
    · rename_i v hv
      split at h
      · rename_i rr' hq; cases h; exact ⟨v, hv, hq⟩
      · cases h
    · cases h
  · rintro ⟨v, hv, hq⟩
    simp [hv, hq]

theorem responseOf_none {bs : List (Option Byte)} :
    responseOf bs = none ↔ ∀ rr, ¬ ResponseBytes bs rr := by
  constructor
  · intro h rr hr; rw [responseOf_some.mpr hr] at h; cases h
  · intro h
    cases hr : responseOf bs with
    | none => rfl
    | some rr => exact absurd (responseOf_some.mp hr) (h rr)

/-- The bytes of a response decode to it. -/
theorem responseOf_clc (r : ClcResponse) : responseOf ((Value.clc r).toBytes.map some) = some r :=
    by
  simp [responseOf, rebuild_clc, roundTrip128, splitValue, joinValue, Value.bytes]

end
end PTX.Flow
