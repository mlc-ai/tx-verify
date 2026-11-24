-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Assembly
public import Kernels.FlashAttn4Fwd.Proof.SafeGlue3
public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaDesc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemAlloc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Lemmas.Flow.TcStBytes
public import Lemmas.Tmem.Alloc512
public import Lemmas.Assumption.Facts

@[expose] public section

/-! # The facts of the whole execution at a thread's next event

This file sits at the top of the proof tree, outside the layer order (as `ProgressFacts.lean`
does): it proves `Progress.NextSafe` for every consistent execution, from the safety goal and the
thread layer's exports.

* **The order at the bytes that are read** (`next_reads`): every access of a byte of O is a
  tensor store's write (`o_access`), so no read covers a byte of O, and outside O every conflict
  is ordered (`Safety.outside_ordered`, a premise from the safety layer: there the store warp's
  32 unordered stores of one element of O, writes of the same bytes with the same value, do not
  reach).
* **The words of Tensor Memory** (`next_words`): an MMA result is a single-precision float (the
  ideal `kind::f16` MMA with an f32 accumulator, `FloatFacts_mma_kind`, `eval_f16`); a
  `tcgen05.st` stores 4-byte values (the template's check, `fires_tcSt_bytes`); the kernel has no
  `tcgen05.cp` (`ScoreFacts_no_cp`).
* **The column of the allocation** (`next_alloc_base`): every allocation requests 512 columns
  (`TmemFacts_event`), and a safe execution's CTA histories replay without a fault
  (`tmemNoFault_of_safe`), so every recorded allocation is at column 0
  (`Consistent.alloc512_base`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy Result

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The conflicting accesses at the bytes that are read are ordered**, given that the
conflicts outside O are. -/
theorem next_reads (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hi : AsyncInputs P L X) (ho : OlderFacts P L X)
    (hord : ConflictsOrdered L X fun l => ¬ Safety.InTensor P P.oBase P.sq l) :
    ReadsOrdered L X := by
  intro r ra rbs k hrd hk e f a b hc _ ha hb
  refine (hord e f a b _ hc ha hb ?_).imp .direct .direct
  intro hO
  obtain ⟨i', x, y, z, rfl⟩ := o_access hpre hX hi.rings hi.tmem hi.async hi.ringCopies
    hi.output ho hrd.intent (Acc.covers_at hk) hO
  simp only [Execution.MemReads] at hrd

/-- FA4's Tensor Memory stores all have the shape `.32x32b`. -/
theorem kernel_tcSt_shape : kernel.code.all (fun ins => match ins.op with
    | .tcSt _ _ s => decide (s = .s32x32b)
    | _ => true) = true := by
  decide +kernel

/-- A Tensor Memory store event of FA4 has no `.pack::16b` shape: its instruction has the shape
`.32x32b` (`kernel_tcSt_shape`), which the event keeps. -/
theorem tcSt_not_packed {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e o) {a : Nat} {vals : List Value}
    {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) : ∀ s, sh ≠ .packed16 s := by
  have hop := fires_tcSt_op hf hk
  have hall := List.all_eq_true.mp kernel_tcSt_shape ins (List.mem_of_getElem? hc)
  obtain ⟨pci, op⟩ := ins
  cases op <;> simp only [tcStOp, Bool.false_eq_true] at hop
  rename_i ta ss s
  simp only [decide_eq_true_eq] at hall
  subst hall
  rw [eventTmpl_tcSt_noWait (by rfl)] at hf
  simp only [tcTmpl] at hf
  intro s' hs'
  subst hs'
  cases hr : readBits L g t 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g t 32) <;>
    simp only [ofExec, hr, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  exact absurd hk.2.2 (by simp)

/-- **Every Tensor Memory write leaves a 4-byte word in its cell.** -/
theorem next_words (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    ∀ s cell v, TcMma.Wrote L asms X s cell v → v.bytes = 4 := by
  have ht := tracked hpre hX
  intro s cell v h
  rcases h with h | ⟨a, vals, sh, j, ⟨pc, hs⟩, hj, -⟩ | ⟨c, -, -, -, -, -, -, hcp, -⟩ |
    ⟨-, -, ⟨hsc, -⟩, -⟩
  · have hf : ∃ r, v = .float .f32 r := by
      have hk := fun {i d sp acc mask} (hi : X.MmaIssue i d sp acc mask) =>
        FloatFacts_mma_kind hpre hX ht hi
      cases h with
      | overwrite hi _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
      | accumulate hi _ _ _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
      | accumulateStored hi _ _ _ _ ha =>
        exact TcMma.eval_f16 (hk hi) (by rw [hk hi]; exact List.mem_singleton.mpr rfl) ha
    obtain ⟨r, rfl⟩ := hf
    rfl
  · obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
      event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => Cross.trueJ_run L g) hs nofun
    exact fires_tcSt_bytes hf rfl (tcSt_not_packed hc hf rfl) v (List.mem_of_getElem? hj)
  · exact (ScoreFacts_no_cp hX _ _ hcp).elim
  · obtain ⟨sp, hsp, -⟩ := hsc
    exact (ScoreFacts_no_shift hX _ _ hsp).elim

/-- **Every recorded allocation returns column 0.** -/
theorem next_alloc_base (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hsafe : ¬ Unsafe L kernel asms mem0 X) :
    ∀ (i : EvId) (pc : Nat) (grp : CtaGroup) (dst : Option Loc) (n cta : Nat)
      (x : Tmem.Pair.Requests) (base : Nat),
      X.get i = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → x ∈ X.tmemHistory cta →
      x.own.event L 0 = i → x.action = .alloc n base → base = 0 := by
  intro i pc grp dst n cta x base hget hx _ ha
  obtain ⟨-, -, hsh, -⟩ := TmemFacts_event hpre hX (tracked hpre hX) (event_thread_lt hX hget) hget
  have hn : n = 512 := by
    generalize Tmem.Pair.tmemOps _ = c at hsh
    rcases c with _ | _ | _ | c <;> simp [Tmem.Pair.TmemShape] at hsh
    exact hsh
  subst hn
  refine hX.alloc512_base (tmemNoFault_of_safe (fun h : Tmem.Pair.ResourceUnsafe L X => hsafe ?_)
    cta) hx ha
  exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
    (.inl h))))))))))))))

/-- **The facts of the whole execution at a thread's next event**, for every consistent
execution, from the safety goal, the order of the conflicts outside O and the remaining premises'
thread exports. -/
theorem nextSafe (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hR : Progress.Remaining L mem0)
    (hord : ∀ X, Consistent L kernel asms mem0 X →
      ConflictsOrdered L X fun l => ¬ Safety.InTensor P P.oBase P.sq l) :
    ∀ X, Consistent L kernel asms mem0 X → Progress.NextSafe L X := fun X hX =>
  ⟨next_reads hpre hX (hR.async P X hpre hX) (hR.pollInputs P X hpre hX).older (hord X hX),
    next_words hpre hX, next_alloc_base hpre hX (hs.2 X hX)⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
