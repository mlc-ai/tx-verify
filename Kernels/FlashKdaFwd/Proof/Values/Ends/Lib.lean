-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.MatrixShape

@[expose] public section

/-!
# Tools for the values at the ends of the tile loop

What the four stretches share; nothing here names a site.

* **Bytes and values.** Four bytes of one binary32 payload load as that payload (`ldVal_f32`),
  four bytes of two bfloat16 payloads rebuild as their pair (`rebuild_pair`), and a payload of
  the store's width is stored as its own bytes (`storeValue_f32`, `storeValue_bf16`).
* **The bytes of a write event** (`store_bytes_direct` for `st.shared` / `st.global`,
  `store_bytes_generic` for a store through a generic pointer): at a followed state, a write
  event of a one-register store writes the bytes of the stored form of the value the machine
  holds for the source register. The proof reads the instruction's event template (the machine
  is sound, so the event was fired by it): the template is a write of those bytes or undefined
  behaviour, and the event is a write.
* **Along a trace** (`state_before`, `get_of_lt`, `next_some`): the states before a followed
  state are followed, the positions before an event have events, and a followed successor is
  the machine's `next`.
* **Read lists** (`range_map4`): the form in which the read-back theorems give four bytes.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution} {g : ℕ}

/-! ## Bytes and values -/

/-- A list of four entries given by index. -/
theorem range_map4 {α : Type} (f : ℕ → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

/-- The four bytes of a binary32 payload, as a load returns them. -/
def f32Bytes (x : ℝ) : List (Option Byte) :=
  (List.range 4).map fun i => some ((Value.float .f32 x).byteAt i)

/-- **Four bytes of one binary32 payload load as the payload** (a 32-bit load without
extension). -/
theorem ldVal_f32 (x : ℝ) : ldVal .same 32 (f32Bytes x) = .ok (.float .f32 x) := by
  have h : f32Bytes x = (Value.float .f32 x).toBytes.map some := by
    simp [f32Bytes, Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]
  rw [ldVal, h, rebuild_scalar (by simp [Value.bytes, FloatFmt.bytes]) rfl]
  rfl

/-- **Four bytes of two bfloat16 payloads rebuild as their pair.** -/
theorem rebuild_pair (lo hi : ℝ) :
    rebuild 3 [some ((Value.float .bf16 lo).byteAt 0), some ((Value.float .bf16 lo).byteAt 1),
      some ((Value.float .bf16 hi).byteAt 0), some ((Value.float .bf16 hi).byteAt 1)] =
      .ok (WarpMatrix.bf16Pair lo hi) :=
  WarpMatrix.rebuild_bf16Pair lo hi

/-- A binary32 payload is stored by a 32-bit store as it is. -/
theorem storeValue_f32 (x : ℝ) : storeValue 32 (.float .f32 x) = .ok (.float .f32 x) :=
  storeValue_of_bytes rfl

/-- A bfloat16 payload is stored by a 16-bit store as it is. -/
theorem storeValue_bf16 (x : ℝ) : storeValue 16 (.float .bf16 x) = .ok (.float .bf16 x) :=
  storeValue_of_bytes rfl

/-- The bytes of a stored binary32 payload. -/
theorem toBytes_f32 (x : ℝ) : (Value.float .f32 x).toBytes =
    [(Value.float .f32 x).byteAt 0, (Value.float .f32 x).byteAt 1,
      (Value.float .f32 x).byteAt 2, (Value.float .f32 x).byteAt 3] := by
  simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]

/-- The bytes of a stored bfloat16 payload. -/
theorem toBytes_bf16 (x : ℝ) : (Value.float .bf16 x).toBytes =
    [(Value.float .bf16 x).byteAt 0, (Value.float .bf16 x).byteAt 1] := by
  simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]

/-! ## The bytes of a write event -/

/-- A write event fired by the template of a direct store of one register: its bytes are those
of the stored form of the register's value. -/
theorem wr_storeTmpl {pc pc' : ℕ} {t : TState} {sp : Space} {w base r : ℕ} {off : Int}
    {a : Acc} {bs : List Byte} {o : Option TState} {v : Value}
    (hf : Fires pc (storeTmpl L g t sp w base off [.reg r]) ⟨pc', .wr a bs⟩ o) (hs : t.sub = 0)
    (hv : t.regs r = some v) : ∃ v', storeValue w v = .ok v' ∧ bs = v'.toBytes := by
  cases hea : effAddr L g t sp base off with
  | error f =>
    simp only [storeTmpl, hea, bind, Except.bind, Fires] at hf
    cases hf.1
  | ok loc =>
    have hrv : readValue L g t w (.reg r) = .ok v := by
      simp [readValue, readReg, hv, pure, Except.pure]
    refine shape_st (P := fun e => ∀ pc' a bs, e = ⟨pc', .wr a bs⟩ →
        ∃ v', storeValue w v = .ok v' ∧ bs = v'.toBytes) hf hea hs rfl hrv
      (fun v' hv' pc' a bs h => ?_)
      (fun f pc' a bs h => ?_) pc' a bs rfl
    · cases h
      exact ⟨v', hv', rfl⟩
    · cases h

/-- The same for a store through a generic pointer (the access template). -/
theorem wr_accessTmpl {pc pc' : ℕ} {t : TState} {ma : MemAccess} {r : ℕ} {a : Acc}
    {bs : List Byte} {o : Option TState} {v : Value}
    (hf : Fires pc (accessTmpl Assumptions.all L g t ma) ⟨pc', .wr a bs⟩ o)
    (hk : ma.kind = .store) (hsrcs : ma.srcs = [.reg r]) (hs : t.sub = 0)
    (hv : t.regs r = some v) :
    ∃ v', storeValue ma.elem.width v = .ok v' ∧ bs = v'.toBytes := by
  have hrv : readValue L g t ma.elem.width (.reg r) = .ok v := by
    simp [readValue, readReg, hv, pure, Except.pure]
  cases hacc : accessAcc L g t ma with
  | error f =>
    simp only [accessTmpl, hk, hacc, Fires] at hf
    cases hf.1
  | ok acc =>
    simp only [accessTmpl, hk, hacc, hsrcs, hs, List.getElem?_cons_zero, hrv, bind,
      Except.bind] at hf
    cases hsv : storeValue ma.elem.width v with
    | error f =>
      simp only [hsv, Fires] at hf
      cases hf.1
    | ok v' =>
      simp only [hsv, Fires] at hf
      cases hf.1
      exact ⟨v', rfl, rfl⟩

/-- **The bytes of a write event at a direct store site** (`st.shared`, `st.global`): the
stored form of the value the machine holds for the source register. `hT` is the instruction's
template (`memTmpl_direct_weakStore` on the decoded instruction). -/
theorem store_bytes_direct (F : Followed L mem0 X) {k pc : ℕ} {a : Acc} {bs : List Byte}
    {d : D} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : stateAt (code L) X g k = some (some d)) {ins : Instr} {ma : MemAccess} {sp : Space}
    {w base r : ℕ} {off : Int} (hcode : kernel.code[d.site.pc]? = some ins)
    (hins : ins.op = .mem ma)
    (hT : ∀ t : TState, memTmpl Assumptions.all L g t ma = storeTmpl L g t sp w base off [.reg r])
    (hsub : d.site.sub = 0) (hlive : (Flow.live d.site.pc).contains r = true)
    (ho : isOpaque r = true) : ∃ v', storeValue w (d.x r) = .ok v' ∧ bs = v'.toBytes := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  have hE : eventTmpl Assumptions.all L g t (.mem ma) = memTmpl Assumptions.all L g t ma := rfl
  rw [hE, hT] at hf
  rw [← valueOf_opaque ho]
  exact wr_storeTmpl hf (hat.2.1.trans hsub)
    (regs_of_live hat.2.2.2.2 (rs := [r]) (by simpa using hlive) r (by simp))

/-- **The bytes of a write event at a store through a generic pointer.** `hT` is the
instruction's template (`rfl` on the decoded instruction: it has no direct location rule). -/
theorem store_bytes_generic (F : Followed L mem0 X) {k pc : ℕ} {a : Acc} {bs : List Byte}
    {d : D} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : stateAt (code L) X g k = some (some d)) {ins : Instr} {ma : MemAccess} {r : ℕ}
    (hcode : kernel.code[d.site.pc]? = some ins) (hins : ins.op = .mem ma)
    (hT : ∀ t : TState, memTmpl Assumptions.all L g t ma = accessTmpl Assumptions.all L g t ma)
    (hk : ma.kind = .store) (hsrcs : ma.srcs = [.reg r]) {w : ℕ} (hw : ma.elem.width = w)
    (hsub : d.site.sub = 0) (hlive : (Flow.live d.site.pc).contains r = true)
    (ho : isOpaque r = true) : ∃ v', storeValue w (d.x r) = .ok v' ∧ bs = v'.toBytes := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  have hE : eventTmpl Assumptions.all L g t (.mem ma) = memTmpl Assumptions.all L g t ma := rfl
  rw [hE, hT] at hf
  rw [← valueOf_opaque ho, ← hw]
  exact wr_accessTmpl hf hk hsrcs (hat.2.1.trans hsub)
    (regs_of_live hat.2.2.2.2 (rs := [r]) (by simpa using hlive) r (by simp))

/-! ## Rewritten slots -/

/-- A read of slots of which one was rewritten. -/
theorem valueEx_one (x : ℕ → Value) (k : ℕ) (v : Value) (r : ℕ) :
    valueEx x [(k, v)] r = if r = k then v else x r := by
  by_cases h : r = k
  · simp [valueEx, List.lookup, h]
  · have hb : (r == k) = false := by simpa using h
    simp [valueEx, List.lookup, h, hb]

/-- A read at another register than the rewritten one. -/
theorem valueEx_ne {r k : ℕ} (h : r ≠ k) (x : ℕ → Value) (v : Value) :
    valueEx x [(k, v)] r = x r := by
  simp only [valueEx_one, h, ↓reduceIte]

/-- A read of slots of which one was rewritten, and then another one that is not read. -/
theorem valueEx_two {r k' : ℕ} (h : r ≠ k') (x : ℕ → Value) (k : ℕ) (v v' : Value) :
    valueEx (valueEx x [(k, v)]) [(k', v')] r = if r = k then v else x r := by
  rw [valueEx_ne h, valueEx_one]

/-! ## Along a trace -/

/-- A position before an event has an event. -/
theorem get_of_lt {k k' : ℕ} {e : Event} (he : X.get (g, k) = some e) (h : k' < k) :
    ∃ e', X.get (g, k') = some e' := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hk' : k' < (X.tr g).length := by omega
  exact ⟨(X.tr g)[k'], List.getElem?_eq_getElem hk'⟩

/-- A position below the length of the trace has an event. -/
theorem get_of_lt_length {k : ℕ} (h : k < (X.tr g).length) : ∃ e, X.get (g, k) = some e :=
  ⟨_, List.getElem?_eq_getElem h⟩

/-- The machine follows the thread before a followed state. -/
theorem state_before (F : Followed L mem0 X) (hg : g < L.threads) {k k' : ℕ} {d : D}
    (hσ : stateAt (code L) X g k = some (some d)) (h : k' ≤ k) :
    ∃ d', stateAt (code L) X g k' = some (some d') :=
  stateAt_live F.tracked hg hσ h

/-- The state after an event is the machine's successor of the state before it. -/
theorem stateAt_step {k : ℕ} {e : Event} {d : D} (he : X.get (g, k) = some e)
    (hσ : stateAt (code L) X g k = some (some d)) :
    stateAt (code L) X g (k + 1) = Thread.next L g d e := by
  rw [stateAt_succ (C := code L) he, hσ]
  rfl

/-- A followed successor is the machine's `next`. -/
theorem next_some {k : ℕ} {e : Event} {d d' : D} (he : X.get (g, k) = some e)
    (hσ : stateAt (code L) X g k = some (some d))
    (hσ' : stateAt (code L) X g (k + 1) = some (some d')) :
    Thread.next L g d e = some (some d') := by
  rw [← stateAt_step he hσ, hσ']

/-- A thread with an event is launched. -/
theorem lt_threads (F : Followed L mem0 X) {k : ℕ} {e : Event} (he : X.get (g, k) = some e) :
    g < L.threads :=
  lt_of_get F.consistent he

/-- The state before a write event (it is not undefined behaviour). -/
theorem state_of_wr (F : Followed L mem0 X) {k pc : ℕ} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : ∃ d, stateAt (code L) X g k = some (some d) :=
  event_state F.sound F.consistent F.tracked he (by
    rintro pc' f h
    cases h)

/-- The number of `bar.sync 0` before a position does not decrease along the trace. -/
theorem bar0Before_mono {k k' : ℕ} (h : k ≤ k') :
    Protocol.bar0Before X (g, k) ≤ Protocol.bar0Before X (g, k') := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  show ((X.tr g).take k).countP _ ≤ ((X.tr g).take (k + n)).countP _
  rw [List.take_add, List.countP_append]
  exact Nat.le_add_right _ _

end

end PTX.Kernels.FlashKdaFwd.Proof.Values.Ends
