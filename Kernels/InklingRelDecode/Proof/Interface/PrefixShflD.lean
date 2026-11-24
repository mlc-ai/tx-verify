-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixShfl
public import Kernels.InklingRelDecode.Proof.Thread.DPre
public import Kernels.InklingRelDecode.Proof.Thread.DCompFollows

@[expose] public section

/-!
# The common start's broadcast of the warp index does not leave the run

The common start's `shfl` state (warps 0 to 3) is the broadcast of the warp index from lane 0.
As for the workers (`PrefixShfl.lean`), the received word is lane 0's operand of the instance, or
any value when lane 0 exited before it. Lane 0's own machine (`DComp.code`) may stop following
it at the load of the base word (a word without room for the 512 columns), so lane 0 is followed
here by `DPre.code`, the common start without the base word, which follows every thread of the
default partition up to its broadcast whatever the loaded word (`DPre.sound`). Along that run
lane 0's first shuffle is its broadcast, with its warp index as operand (`dpre_first_shfl`), and
it does not exit before it (`dpre_not_exited0`). The thread's own instance is its first shuffle
(`dstart_own_count`). So `dstart_shfl_next_ne` is `hnext` at the common start's `shfl` state, in
every consistent execution, from facts of lane 0's own trace only.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event that is not the last of a machine's run fires with a continuation.** -/
theorem trace_fired_some {K : Kernel} {A : List Assumption} {g : Nat}
    {M : Machine K A L g} {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat} {e : Event} {τ : M.St}, es[j]? = some e → j + 1 < es.length →
      M.after σ (es.take j) = some τ → ∃ u, M.Fired τ e (some u) := by
  induction h with
  | nil σ => intro j e τ hj; simp at hj
  | step hf hn _ ih =>
    intro j e τ hj hl hτ
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.take_zero, Machine.after, Option.some.injEq] at hτ
      subst hτ
      exact ⟨_, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at hτ
      exact ih (by simpa using hj) (by simp at hl; omega) hτ
  | last hf =>
    intro j e τ hj hl
    simp at hl
  | dead hf hn hlen _ =>
    intro j e τ hj hl hτ
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.take_zero, Machine.after, Option.some.injEq] at hτ
      subst hτ
      exact ⟨_, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_none] at hτ
      cases hτ

/-- The run of the common start without the base word. -/
abbrev PS (Q : Params) (L : Launch) (X : Execution) (h k : Nat) : Option (Option DStart.D) :=
  Frame.stateAt (fun g => DPre.code L g Q) X h k

/-- **Where the run of `DPre` stopped following, the thread made its broadcast before.** -/
theorem ps_stop {h : Nat} : ∀ k, k ≤ (X.tr h).length → PS Q L X h k = some none →
    ∃ i < k, ∃ d, PS Q L X h i = some (some d) ∧ d.site = .shfl := by
  intro k
  induction k with
  | zero =>
    intro _ h0
    simp [PS, Frame.stateAt_zero] at h0
  | succ k ih =>
    intro hk hs
    obtain ⟨e, he⟩ : ∃ e, (X.tr h)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hsucc := Frame.stateAt_succ (C := fun g => DPre.code L g Q) he
    rw [show Frame.stateAt (fun g => DPre.code L g Q) X h (k + 1) = some none from hs] at hsucc
    cases hk' : PS Q L X h k with
    | none =>
      rw [show Frame.stateAt (fun g => DPre.code L g Q) X h k = none from hk'] at hsucc
      cases hsucc
    | some σ =>
      cases σ with
      | none =>
        obtain ⟨i, hi, d, h1, h2⟩ := ih (by omega) hk'
        exact ⟨i, by omega, d, h1, h2⟩
      | some d =>
        rw [show Frame.stateAt (fun g => DPre.code L g Q) X h k = some (some d) from hk'] at hsucc
        have hn : DPre.next L h d e = some none := hsucc.symm
        rcases DPre.stop_site hn with h1 | h1
        · exact ⟨k, by omega, d, hk', h1⟩
        · exfalso
          cases k with
          | zero =>
            simp only [PS, Frame.stateAt_zero, Option.some.injEq] at hk'
            subst hk'
            revert h1
            unfold DStart.D.start
            split <;> simp
          | succ k =>
            obtain ⟨e', he'⟩ : ∃ e', (X.tr h)[k]? = some e' :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            have hs' := Frame.stateAt_succ (C := fun g => DPre.code L g Q) he'
            rw [show Frame.stateAt (fun g => DPre.code L g Q) X h (k + 1) = some (some d)
              from hk'] at hs'
            cases hk'' : PS Q L X h k with
            | none =>
              rw [show Frame.stateAt (fun g => DPre.code L g Q) X h k = none from hk''] at hs'
              cases hs'
            | some σ' =>
              rw [show Frame.stateAt (fun g => DPre.code L g Q) X h k = some σ' from hk''] at hs'
              cases σ' with
              | none => cases hs'
              | some d0 => exact (DPre.next_site hs'.symm).1 h1

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- The run of `DPre` of a thread of the default partition is a run of its machine. -/
theorem ps_trace {h : Nat} (hh : h < L.threads) (hw : h % L.block < 128) :
    (DPre.code L h Q).toMachine.Trace (some (DPre.code L h Q).init) (X.tr h) :=
  ((DPre.sound hpre hh hw).machine).produces (hX.thr h hh)

/-- **The events before a thread's first shuffle fire from `DPre` states.** -/
theorem ps_prefix {h j : Nat} {e : Event} (hh : h < L.threads) (hw : h % L.block < 128)
    (he : X.get (h, j) = some e) (hu : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hc : ((X.tr h).take j).countP Execution.isShfl = 0) :
    ∃ d o, PS Q L X h j = some (some d) ∧ (DPre.code L h Q).toMachine.Fired (some d) e o := by
  have htr := ps_trace hpre hX hh hw
  have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  rcases htr.fired he with ⟨τ, o, hτ, hf⟩ | ⟨hτ, pc, f, rfl⟩
  · have hτ' : PS Q L X h j = some τ := hτ
    cases τ with
    | some d => exact ⟨d, o, hτ', hf⟩
    | none =>
      exfalso
      obtain ⟨i, hi, d, hd, hs⟩ := ps_stop j (by omega) hτ'
      obtain ⟨ei, hei⟩ : ∃ ei, (X.tr h)[i]? = some ei :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨u, hfu⟩ := trace_fired_some htr hei (by omega) hd
      obtain ⟨t, ins, hat, -, hcode, hfi⟩ := Code.fired_site (DPre.sound hpre hh hw) hfu
      obtain ⟨s, tm⟩ := d
      simp only at hs
      subst hs
      obtain ⟨recv, ok, rfl⟩ := DPre.shfl_fires (tm := tm) (DPre.pat_iff.mp hat) hcode hfi
      have hmem : (⟨DStart.Site.shfl.pc, .shfl .idx (b32 (h % L.block / 32)) 0 31 recv ok⟩ :
          Event) ∈
          (X.tr h).take j := by
        rw [List.mem_iff_getElem?]
        exact ⟨i, by rw [List.getElem?_take]; simp [hi, hei]⟩
      have := (List.countP_pos_iff (p := Execution.isShfl)).mpr ⟨_, hmem, rfl⟩
      omega
  · exact absurd rfl (hu pc f)

/-- **Lane 0's first shuffle has its warp index as operand** (a thread of the default
partition, whatever base word it loaded). -/
theorem dpre_first_shfl {h j : Nat} (hh : h < L.threads) (hw : h % L.block < 128)
    (hk : X.ShflK (h, j) 0) :
    ∃ pc recv ok, X.get (h, j) = some ⟨pc, .shfl .idx (b32 (h % L.block / 32)) 0 31 recv ok⟩ := by
  obtain ⟨⟨pc, m, a, b, c, r, o, hget⟩, hcnt⟩ := hk
  obtain ⟨d, o', -, hf⟩ := ps_prefix hpre hX hh hw hget (fun _ _ h => by cases h) hcnt
  obtain ⟨t, ins, hat, -, hcode, hfi⟩ := Code.fired_site (DPre.sound hpre hh hw) hf
  obtain ⟨s, tm⟩ := d
  by_cases hs : s = .shfl
  · subst hs
    obtain ⟨recv, ok, he⟩ := DPre.shfl_fires_any (tm := tm) (DPre.pat_iff.mp hat) hcode hfi rfl
    exact ⟨_, recv, ok, by rw [hget, he]⟩
  · have := (DPre.pre_fires (s := s) hs hcode hfi).1
    simp [Execution.isShfl] at this

/-- **Lane 0 does not exit before its first shuffle.** -/
theorem dpre_not_exited0 {h : Nat} (hh : h < L.threads) (hw : h % L.block < 128) :
    ¬ ShflExited X h 0 := by
  rintro ⟨k, pc, hget, hcnt⟩
  have hc : ((X.tr h).take k).countP Execution.isShfl = 0 := by omega
  obtain ⟨d, o', -, hf⟩ := ps_prefix hpre hX hh hw hget (fun _ _ h => by cases h) hc
  obtain ⟨t, ins, -, -, hcode, hfi⟩ := Code.fired_site (DPre.sound hpre hh hw) hf
  obtain ⟨s, tm⟩ := d
  by_cases hs : s = .shfl
  · subst hs
    exact DPre.shfl_not_exit hcode hfi rfl
  · exact (DPre.pre_fires (s := s) hs hcode hfi).2 rfl

end

section
variable (hX : Consistent L kernel asms mem0 X) (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
include hX hS

omit hX hS in
/-- **The states before a common-start state are common-start states before the broadcast.** -/
theorem d_prefix {g : Nat} : ∀ k, k ≤ (X.tr g).length → ∀ {d : DStart.D},
    St Q L X g k = some (some (.d (.dstart d))) →
    ∀ i < k, ∃ di : DStart.D, St Q L X g i = some (some (.d (.dstart di))) ∧
      di.site ≠ .shfl ∧ di.site ≠ .toProA := by
  intro k
  induction k with
  | zero => intro _ _ _ i hi; omega
  | succ k ih =>
    intro hkl d hσ i hi
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs := Frame.stateAt_succ (C := code L Q) he
    rw [show Frame.stateAt (code L Q) X g (k + 1) = some (some (.d (.dstart d))) from hσ] at hs
    cases hk' : St Q L X g k with
    | none => rw [show Frame.stateAt (code L Q) X g k = none from hk'] at hs; cases hs
    | some σ =>
      rw [show Frame.stateAt (code L Q) X g k = some σ from hk'] at hs
      cases σ with
      | none => cases hs
      | some s =>
        have hs' : (threadCode L g Q).next s e = some (some (.d (.dstart d))) := hs.symm
        cases s with
        | w s =>
          rw [next_w] at hs'
          obtain ⟨a, -, ha⟩ := map_map_eq_some_some hs'
          cases ha
        | d s =>
          rw [next_d] at hs'
          obtain ⟨a, ha, hae⟩ := map_map_eq_some_some hs'
          cases hae
          obtain ⟨d0, rfl, h1, h2⟩ := DComp.dstart_tgt ha
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact ih (by omega) hk' i hi
          · exact ⟨d0, hk', h1, h2⟩

/-- **The common start's broadcast is the thread's first shuffle.** -/
theorem dstart_own_count {g k : Nat} {d : DStart.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.dstart d)))) :
    ((X.tr g).take k).countP Execution.isShfl = 0 := by
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rw [List.countP_eq_zero]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hik : i < k := by simp at hi; omega
  have hil : i < (X.tr g).length := by omega
  rw [List.getElem_take]
  obtain ⟨di, hdi, hs, -⟩ := d_prefix k (by omega) hσ i hik
  have he' : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hil
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he' hdi
  have := (DPre.pre_fires (L := L) (g := g) (s := di.site) hs hc hf).1
  simp [this]

end

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
  (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
include hpre hX hS hT

/-- **`hnext` at the common start's broadcast of the warp index**: the received word is the warp
index, so the machine goes on to the prologue. -/
theorem dstart_shfl_next_ne {g k : Nat} {d : DStart.D} {e : Event} (hg : g < L.threads)
    (he : (X.tr g)[k]? = some e) (hσ : St Q L X g k = some (some (.d (.dstart d))))
    (hs : d.site = .shfl) : (threadCode L g Q).next (.d (.dstart d)) e ≠ some none := by
  have he' : X.get (g, k) = some e := he
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he' hσ (by simp [ExitState])
  have hFd : DStart.Fired L g Q d e (some u) := by
    obtain ⟨t, ⟨ha, hi⟩, hf⟩ := hF
    exact DStart.Fired_of_machine ⟨t, ⟨ha, hi.2.1⟩, hf⟩
  have hdef : IsDefault L g := by
    obtain ⟨t, ⟨-, hi⟩, -⟩ := hF
    exact hi.1
  have hsh := DStart.shape_of_pre hpre hFd
  rw [DStart.Shape, hs] at hsh
  obtain ⟨recv, ok, rfl⟩ := hsh
  have hcnt := dstart_own_count hX hS he' hσ
  have hK : X.ShflK (g, k) 0 := ⟨⟨_, _, _, _, _, _, _, he'⟩, hcnt⟩
  obtain ⟨-, hsrc⟩ := hX.shfl g k 0 _ .idx _ 0 31 recv ok he' hK
  have h0 : (shflSource .idx (laneOf L g) 0 31).1 = 0 := by
    simp [shflSource]
  rw [h0] at hsrc
  have hb : L.block = 256 := hpre.block
  have hw := lane0_sameWarp hb hg
  have hh : g - laneOf L g + 0 < L.threads := hw.1.2.1
  have h1 : (g - laneOf L g + 0) % L.block / 32 = g % L.block / 32 := hw.2.symm
  have hdh : (g - laneOf L g + 0) % L.block < 128 := by
    have : g % L.block < 128 := hdef
    omega
  have hrecv : recv = b32 (g % L.block / 32) := by
    rcases hsrc with ⟨j, pc', b', c', r', o', hK', hget'⟩ | hx
    · obtain ⟨pc'', recv'', ok'', hget''⟩ := dpre_first_shfl hpre hX hh hdh hK'
      rw [hget''] at hget'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.shfl.injEq] at hget'
      rw [← h1]
      exact hget'.2.2.1.symm
    · exact absurd hx (dpre_not_exited0 hpre hX hh hdh)
  subst hrecv
  obtain ⟨site, tm⟩ := d
  simp only at hs
  subst hs
  rw [next_d]
  simp [DComp.next, DComp.dstartNext, DStart.next, b32, DStart.warpOf]

end

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
