-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkBar
public import Lemmas.Kernel.PlainStep
public import Kernels.InklingRelDecode.Proof.Interface.Facts

@[expose] public section

/-!
# Warp lockstep: the shuffle events

A state is a shuffle state when its instruction is a `shfl.sync` (`shflSt`). The event fired from a
shuffle state is a shuffle, unless it is undefined behaviour, which a followed state does not fire
(`TmplOk`); and every shuffle event is fired from a shuffle state (`fires_shfl_op`). The shuffle
states of a thread are synchronizing, so the events of the class `isShfl` satisfy the hypotheses of
`Lk.lock_count` (`LkCount.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (syOp syPcs syPc syAt kernel_syPcs)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The state's instruction is a shuffle. -/
def shflSt (s : TSt) : Bool :=
  match kernel.code[TSt.pc s]? with
  | some ins => Op.isShfl ins.op
  | none => false

/-- The form of the shuffles of the kernel: one destination at least, three sources, a mask. -/
def shflForm : Op → Bool
  | .warp ⟨.shfl _, _, some _ :: _, [_, _, _], some _⟩ => true
  | .warp ⟨.shfl _, _, _, _, _⟩ => false
  | _ => true

theorem kernel_shflForm : kernel.code.all (fun ins => shflForm ins.op) = true := by
  decide +kernel

/-- The template of a shuffle instruction is a shuffle or undefined behaviour. -/
theorem shfl_tmpl_cases {A : List Assumption} {g : Nat} {t : TState} {op : Op}
    (h : Op.isShfl op = true) (hf : shflForm op = true) :
    (∃ f, eventTmpl A L g t op = .ub f) ∨ ∃ m a b c k, eventTmpl A L g t op = .shfl m a b c k := by
  cases op with
  | warp w =>
    obtain ⟨kd, ty, ds, ss, mk⟩ := w
    cases kd with
    | shfl mode =>
      rcases ds with _ | ⟨d, ps⟩
      · simp [shflForm] at hf
      rcases d with _ | d
      · simp [shflForm] at hf
      rcases ss with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨x, ss⟩⟩⟩⟩ <;>
        try (simp [shflForm] at hf; done)
      rcases mk with _ | mask
      · simp [shflForm] at hf
      simp only [eventTmpl]
      rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
        (ps := ps) (a := a) (b := b) (c := c) (mask := mask) with h1 | h1 <;> rw [h1]
      · unfold shflTmpl
        repeat' split
        all_goals first
          | exact .inl ⟨_, rfl⟩
          | exact .inr ⟨_, _, _, _, _, rfl⟩
      · exact .inl ⟨_, rfl⟩
    | _ => simp [Op.isShfl] at h
  | _ => simp [Op.isShfl] at h

/-! ### Shuffle states are synchronizing -/

/-- The position is a shuffle. -/
abbrev shflPc (pc : Nat) : Bool := opPc Op.isShfl pc

/-- **A shuffle state is synchronizing.** -/
theorem shflSt_sy {s : TSt} (h : shflSt s = true) : tSy s :=
  opPc_sy (f := Op.isShfl) (fun op h => by cases op <;> simp_all [Op.isShfl, syOp])
    ⟨fun s => by cases s <;> decide +kernel, by decide +kernel,
      fun s => by cases s <;> decide +kernel⟩ h

theorem shflKey_class :
    ∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s → (kernelSkel Q L).sy s' →
      (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' → shflSt s = shflSt s' :=
  opKey_class Op.isShfl

/-- **A shuffle state fires a shuffle event; a state that is no shuffle fires none.** The event of
a followed state is not undefined behaviour (`TmplOk`). -/
theorem isShfl_state (hX : Consistent L kernel asms mem0 X) (hf0 : ThreadFacts Q L mem0 X) :
    ClassEv Execution.isShfl shflSt Q L X := by
  intro g k e s hg he hσ
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hf0.sound hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hform : shflForm ins.op = true :=
    List.all_eq_true.mp kernel_shflForm ins (List.mem_of_getElem? hc')
  by_cases hq : Op.isShfl ins.op = true
  · have hsh : shflSt s = true := by simp only [shflSt, hc', hq]
    rw [hsh]
    rcases shfl_tmpl_cases (A := asms) (L := L) (g := g) (t := t) hq hform with
      ⟨f, hf1⟩ | ⟨m, a, b, c, k', hf1⟩
    · rw [hf1] at hf'
      obtain ⟨he1, -⟩ := hf'
      have := hf0.ub_stop hg (show X.get (g, k) = some ⟨TSt.pc s, .ub f⟩ by rw [he, he1])
      rw [hσ] at this
      rcases this with h | h <;> cases h
    · rw [hf1] at hf'
      obtain ⟨recv, ok, he1, -⟩ := hf'
      rw [he1]
      rfl
  · have hsh : shflSt s = false := by simp only [shflSt, hc']; simpa using hq
    rw [hsh]
    cases hs : Execution.isShfl e
    · rfl
    · exact absurd (fires_shfl_op hf' hs) hq

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
