-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTcCp
public import Lemmas.Execution.NoTma

@[expose] public section

/-! # A kernel without Tensor Core copy instructions issues no copy

A proof tool. Only a `tcgen05.cp` instruction fires a Tensor Core copy event
(`Flow.fires_tcCp_op`); the other templates a thread's next step can be (undefined behaviour, a
skip) fire none. So a kernel whose code has no `tcgen05.cp` (`Kernel.NoTcCp`, decided on the
code) issues no copy in any consistent execution (`noCp_of_consistent`), which is the premise of
the obligation cover (`Descent.cover`). -/

namespace PTX

/-- The kernel's code has no Tensor Core copy instruction. -/
def Kernel.NoTcCp (K : Kernel) : Bool := K.code.all fun ins => !Flow.tcCpOp ins.op

namespace Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A template that fires no Tensor Core copy fires no copy event. -/
theorem fires_notTcCp {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotTcCp m)
    (hf : Fires pc m e o) {spec : TcCopy.Spec} : e.kind ≠ .tc (.cp spec) := by
  intro hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases m <;> simp only [NotTcCp] at hm <;> simp only [Fires] at hf <;> aesop

/-- The next template of a thread of a kernel without copy instructions fires no copy. -/
theorem out_notTcCp (hK : K.NoTcCp = true) {t : TState} {m : Tmpl}
    (h : out K A L g t = .ev m) : NotTcCp m := by
  unfold out at h
  split at h
  · cases h; trivial
  · split at h
    · cases h; trivial
    · rename_i ins hins
      split at h
      · cases h; trivial
      · cases h
      · split at h
        · split at h
          · cases h
          · cases h; trivial
        · cases h
          have := List.all_eq_true.mp hK ins (List.mem_of_getElem? hins)
          simp only [Bool.not_eq_true'] at this
          exact eventTmpl_notTcCp this

/-- No event of a run of a kernel without copy instructions is a copy. -/
theorem run_notTcCp (hK : K.NoTcCp = true) {t : TState} {l : List Event} {o : Option TState}
    (h : Run K A L g t l o) :
    ∀ e ∈ l, ∀ spec, e.kind ≠ .tc (.cp spec) := by
  induction h with
  | nil => simp
  | step _ he _ ih =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_cons.mp h' with rfl | h'
    · exact fun _ => fires_notTcCp (out_notTcCp hK hm) hf
    · exact ih e' h'
  | last _ he =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_singleton.mp h' with rfl
    exact fun _ => fires_notTcCp (out_notTcCp hK hm) hf

end Flow

/-- **A kernel without copy instructions issues no Tensor Core copy.** -/
theorem noCp_of_consistent {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
    {X : Execution} (hK : K.NoTcCp = true) (hX : Consistent L K A mem0 X) :
    ∀ e spec, ¬ X.CpIssue e spec := by
  rintro v spec ⟨pc, hv⟩
  have hlt : v.2 < (X.tr v.1).length := by
    unfold Execution.get at hv; exact (List.getElem?_eq_some_iff.mp hv).1
  have hg : v.1 < L.threads := by
    by_contra hn; rw [hX.outside v.1 (by omega)] at hlt; simp at hlt
  obtain ⟨o, hr⟩ := hX.thr v.1 hg
  have hmem : (⟨pc, .tc (.cp spec)⟩ : Event) ∈ X.tr v.1 := by
    unfold Execution.get at hv; exact List.mem_of_getElem? hv
  exact Flow.run_notTcCp hK hr _ hmem spec rfl

end PTX
