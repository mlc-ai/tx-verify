-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Tc.TcMmaValue
public import Lemmas.Flow.TcStBytes
public import Lemmas.Flow.TcStLen
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The Tensor Memory words that stores, copies and shifts leave are 4 bytes wide

A `tcgen05.st` of the program never has the packed 16-bit shape (a static scan), so it stores
4-byte values (`fires_tcSt_bytes`); a `tcgen05.cp` word is four bytes (`TcCopy.word`) or a 32-bit
decompressed word, whatever the copy; the program issues no `tcgen05.shift` (a static scan). So
every Tensor Memory write leaves a 4-byte word as soon as the MMA results do (`tmem_words`: the
field `NextEnvQ.words` of a released lane's step, given the MMA results' widths). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow TcMma

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private def notPacked : Op → Bool
  | .tcSt _ _ (.packed16 _) => false
  | _ => true

private theorem notPackedCode : kernel.code.all (fun i => notPacked i.op) = true := by
  decide +kernel

private theorem noShiftCode : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- **A copy's word is four bytes wide.** -/
theorem cpWord_bytes {c : TcCopy.Spec} {bytes : List (Option Byte)} {row col : Nat} {v : Value}
    (h : TcCopy.cpWord c bytes row col = some v) : v.bytes = 4 := by
  unfold TcCopy.cpWord at h
  split at h
  · simp only [TcCopy.word, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h
    rfl
  · simp only [TcCopy.decompressedWord, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl

/-- A plain store's event has the instruction's shape. -/
private theorem st_shape {g pc : Nat} {t : TState} {e : Event} {o : Option TState} {ta : Nat}
    {ss : List Opnd} {s' : TcShape} (hnp : ∀ s, s' ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A l g t (.tcSt ta ss s')) e o) {a : Nat} {vals : List Value}
    {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) : sh = s' := by
  obtain ⟨u, _, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  rw [tcTmpl_tcSt_plain hnp] at hf
  cases ha : readBits l g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue l g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  exact hk.2.2.symm

/-- **A store's value is four bytes wide.** -/
theorem tcSt_value_bytes (hX : Consistent l kernel A m X) {st : EvId} {a : Nat}
    {vals : List Value} {sh : TcShape} (hs : X.TSt st a vals sh) {v : Value} (hv : v ∈ vals) :
    v.bytes = 4 := by
  obtain ⟨pc, he⟩ := hs
  rcases get_source hX he with ⟨_, hb⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hb
  have hop := fires_tcSt_op hf rfl
  have hn := List.all_eq_true.mp notPackedCode ins (List.mem_of_getElem? hc)
  cases hIns : ins.op <;> simp only [hIns, tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss s'
  have hnp : ∀ s, s' ≠ .packed16 s := by
    rintro s rfl
    simp [hIns, notPacked] at hn
  rw [hIns] at hf
  have hsh := st_shape hnp hf rfl
  exact fires_tcSt_bytes hf rfl (by rw [hsh]; exact hnp) v hv

/-- An MMA cell of kind `f16` with bf16 inputs and an f32 accumulator is evaluated by the ideal
real rule (`idealArith`, the first assumption), whose results are f32 words. -/
theorem eval_bytes {d : Descriptor} (hk : d.kind = .f16 .bf16 .f32) {acc : Bool}
    {a b : List (Option Byte)} {old : Option Value} {row col : Nat} {v : Value}
    (h : eval Assumptions.all d acc a b old row col = .ok v) : v.bytes = 4 := by
  simp only [eval, hk, Assumptions.all, Assumptions.idealArith, Assumption.idealReal,
    List.findSome?_cons, List.mem_cons, List.not_mem_nil, or_false, ↓reduceIte,
    Option.getD_some] at h
  simp only [Assumption.execIdealMma, hk, bind, Except.bind, pure, Except.pure] at h
  repeat' (first | split at h | cases h)
  all_goals rfl

/-- **The MMA results are 4-byte words** when every MMA has kind `f16` with an f32
accumulator. -/
theorem result_bytes
    (hkind : ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.descriptor.kind = .f16 .bf16 .f32) :
    ∀ s cell v, Result l Assumptions.all X s cell v → v.bytes = 4 := by
  intro s cell v h
  cases h with
  | overwrite hi _ _ he => exact eval_bytes (hkind _ _ _ _ _ hi) he
  | accumulate hi _ _ _ _ he => exact eval_bytes (hkind _ _ _ _ _ hi) he
  | accumulateStored hi _ _ _ _ he => exact eval_bytes (hkind _ _ _ _ _ hi) he

/-- **Every Tensor Memory write leaves a 4-byte word**, given that every MMA has kind `f16` with
an f32 accumulator. -/
theorem tmem_words (hX : Consistent l kernel Assumptions.all m X)
    (hkind : ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.descriptor.kind = .f16 .bf16 .f32) :
    ∀ s cell v, Wrote l Assumptions.all X s cell v → v.bytes = 4 := by
  intro s cell v h
  rcases h with h | ⟨a, vals, sh, j, hs, hj, -⟩ |
    ⟨c, k, cta, ops, row, col, lane, h1, h2, h3, h4, h5, h6, h7, hw⟩ | ⟨-, -, ⟨⟨sp, hsp, -⟩, -⟩, -⟩
  · exact result_bytes hkind s cell v h
  · exact tcSt_value_bytes hX hs (List.mem_of_getElem? hj)
  · exact cpWord_bytes hw
  · obtain ⟨pc, he⟩ := hsp
    exact (no_shift_of_code hX noShiftCode he sp rfl).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
