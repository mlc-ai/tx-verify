-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Alloc
public import Lemmas.Flow.TcStBytes

@[expose] public section

/-!
# Every Tensor Memory write leaves a 4-byte word

The value of a Tensor Memory cell is written by an MMA, a `tcgen05.st`, a `tcgen05.cp` or a
`tcgen05.shift` (`TcMma.Wrote`). The kernel has no `tcgen05.cp` and no `tcgen05.shift`
(`no_tcCp`, `no_tcShift`).

* **MMA.** Every MMA of the program is the MMA warp's QK or PV MMA (`Interface.mma_event_state`)
  whose descriptor decodes to `kind::f16` with `bf16` inputs and an `f32` accumulator
  (`qkIdesc_kind`, `pvIdesc_kind`, by `decide +kernel`). That kind is the one `idealArith`
  (`mma := [.f16 .bf16 .f32]`) covers, which is the first assumption of the kernel, so the result is
  a float of the output format (`TcMma.eval_f16`), 4 bytes.
* **`tcgen05.st`.** Every Tensor Memory store of the program has a shape that is not `.pack::16b`
  (`kernel_tcSt_shape`), so every value it stores is 4 bytes (`Flow.fires_tcSt_bytes`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every Tensor Memory store of the kernel has a shape that is not packed. -/
theorem kernel_tcSt_shape : kernel.code.all (fun ins => match ins.op with
    | .tcSt _ _ sh => match sh with
      | .packed16 _ => false
      | _ => true
    | _ => true) = true := by
  decide +kernel

/-- A Tensor Memory store event of the kernel has no `.pack::16b` shape. -/
theorem tcSt_not_packed {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e o) {a : Nat} {vals : List Value}
    {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) : ∀ s, sh ≠ .packed16 s := by
  have hop := fires_tcSt_op hf hk
  have hall := List.all_eq_true.mp kernel_tcSt_shape ins (List.mem_of_getElem? hc)
  obtain ⟨pci, op⟩ := ins
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss s
  cases s <;> try (simp at hall; done)
  all_goals
    rw [eventTmpl_tcSt_noWait rfl] at hf
    simp only [tcTmpl] at hf
    intro s' hs'
    subst hs'
    cases hr : readBits L g t 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g t 32) <;>
      simp only [ofExec, hr, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hf <;>
      split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
      simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
    all_goals exact hk.2.2.elim

/-- The QK descriptor decodes to the `bf16`-input `f32`-accumulate `kind::f16`. -/
theorem qkIdesc_kind : ∀ dsc, TcMma.decode .one false .f16 Mma.qkIdesc = some dsc →
    dsc.kind = .f16 .bf16 .f32 := by
  intro dsc h
  have h' : (TcMma.decode .one false .f16 Mma.qkIdesc).map (·.kind) =
      some (.f16 .bf16 .f32) := by decide +kernel
  rw [h] at h'
  simpa using h'

/-- The PV descriptor decodes to the `bf16`-input `f32`-accumulate `kind::f16`. -/
theorem pvIdesc_kind : ∀ dsc, TcMma.decode .one false .f16 Mma.pvIdesc = some dsc →
    dsc.kind = .f16 .bf16 .f32 := by
  intro dsc h
  have h' : (TcMma.decode .one false .f16 Mma.pvIdesc).map (·.kind) =
      some (.f16 .bf16 .f32) := by decide +kernel
  rw [h] at h'
  simpa using h'

/-- **The descriptor of the event fired at an MMA state is `kind::f16` with `bf16` inputs and an
`f32` accumulator.** -/
theorem mma_desc_kind {g : Nat} {d : Mma.D} {pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hsh : MmShape L g d ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    sp.descriptor.kind = .f16 .bf16 .f32 := by
  unfold MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh
  all_goals first
    | (obtain ⟨da, db, dsc, hdec, -, -, he⟩ := hsh
       simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
       obtain ⟨-, -, rfl, -⟩ := he
       exact qkIdesc_kind _ hdec)
    | (obtain ⟨db, dsc, hdec, -, he⟩ := hsh
       simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
       obtain ⟨-, -, rfl, -⟩ := he
       exact pvIdesc_kind _ hdec)
    | (exfalso; simp at hsh)

/-- **Every Tensor Memory write leaves a 4-byte word in its cell.** -/
theorem words (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) :
    ∀ s cell v, TcMma.Wrote L asms X s cell v → v.bytes = 4 := by
  intro s cell v h
  rcases h with h | ⟨a, vals, sh, j, ⟨pc, hs⟩, hj, -⟩ | ⟨c, -, -, -, -, -, -, hcp, -⟩ |
    ⟨-, -, ⟨hsc, -⟩, -⟩
  · have hk : ∀ {i d sp acc mask}, X.MmaIssue i d sp acc mask →
        sp.descriptor.kind = .f16 .bf16 .f32 := by
      rintro ⟨g, k⟩ d sp acc mask ⟨pc, he⟩
      have hg := Frame.lt_of_get hX he
      obtain ⟨dd, P, -, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
        (.inl ⟨d, sp, acc, mask, rfl⟩)
      exact mma_desc_kind hsh
    have hf32 : ∃ r, v = .float .f32 r := by
      cases h with
      | overwrite hi _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
      | accumulate hi _ _ _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
      | accumulateStored hi _ _ _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
    obtain ⟨r, rfl⟩ := hf32
    rfl
  · obtain ⟨t, ins, o, -, hc, hfire⟩ := get_source hX hs |>.resolve_left
      (by rintro ⟨f, hf'⟩; cases hf')
    exact fires_tcSt_bytes hfire rfl (tcSt_not_packed hc hfire rfl) v (List.mem_of_getElem? hj)
  · exact (no_tcCp hX _ _ hcp).elim
  · obtain ⟨sp, hsp, -⟩ := hsc
    exact (no_tcShift hX _ _ hsp).elim

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
