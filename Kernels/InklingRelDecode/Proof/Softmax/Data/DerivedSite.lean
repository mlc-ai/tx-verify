-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedStep
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The data steps of the two sites that establish the derived constants -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The facts that start the entry's path: the thread index, the query length and the words past
(registers 462, 481 and 482) read as `derV`. -/
theorem start_tab {t : TState} {d : D} (hat : (codeS e L g).AtD d t) (hs : d.c.site = .bar0) :
    Holds t.regs (factsFrom (tk 576) (derV e L g)) := by
  obtain ⟨-, -, -, -, regs⟩ := atD_ctl (atS_code hat)
  have regs' : Holds t.regs (factsFrom (Control.ctlLive 575) (Control.valueOf e L g d.c)) := by
    change Holds t.regs (factsFrom (Control.ctlLive d.c.site.pc) (Control.valueOf e L g d.c))
      at regs
    rw [hs] at regs
    exact regs
  have k : [462, 481] ⊆ Control.ctlLive 575 := by decide +kernel
  have h482 := (atS_const hat).1
  have h525 := atD_dF (atS_code hat)
  rw [hs] at h525
  refine holds_of_pointwise fun r hr => ?_
  simp only [tk, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact holds_mem regs' (mem_factsFrom (k (by simp)))
  · exact holds_mem regs' (mem_factsFrom (k (by simp)))
  · exact (holds_mem h482 (v := e.prior) (by simp [startF])).trans rfl
  · exact (holds_mem h525 (v := scaleVal L) (by simp [dFS, entryFact])).trans rfl

/-- The first site after the barrier of the entry. -/
def afterBar0 (e : Entry) (L : Launch) (g : Nat) (d : D) : Control.D :=
  {d.c with site := if preEnabled e (g % L.block) = true then .pre 0
    else loopSite e (g % L.block) d.c.i}

/-- **The data step after the barrier of the entry**: its facts from the stops the control
machine names. -/
theorem bar0_open {d : D} (hs : d.c.site = .bar0) {F : D → List (Nat × Value)}
    (hk : ∀ (t : TState) (ev : Event), (codeS e L g).AtD d t → (PTX.next t).pc = 576 →
      ((∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) t'' →
        Stops kernel Assumptions.all L g t'' → t''.pc = (afterBar0 e L g d).site.pc) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (PTX.next t)) →
      (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (PTX.next t) t' →
        Stops kernel Assumptions.all L g t' →
        Holds t'.regs (F ⟨afterBar0 e L g d, record L d ev (afterBar0 e L g d).site⟩)) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (PTX.next t)) :
    DataStep (codeS e L g) F d := by
  have pc : (codeS e L g).pc d = 575 := by
    change d.c.site.pc = 575
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 575 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  rw [Flow.code_bar_19] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := Option.some.inj hf.2
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hpc : (PTX.next t).pc = 576 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  exact hk t ev hat hpc
    (stops_pc hat0 hi (by rw [pc0]; exact Flow.code_bar_19) (by rw [pc0]; exact hf) hn')

/-- **The derived constants after the barrier of the entry.** -/
theorem der_bar0 {d : D} (hs : d.c.site = .bar0) :
    DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  refine @bar0_open e L g d hs _ fun t ev hat hpc hstops => ?_
  refine derived_goal (q := (afterBar0 e L g d).site.pc)
    ⟨?_, hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩ hstops (fun R h => conv_der ?_ h)
  · rw [hpc]; decide +kernel
  · rw [hpc]
    exact start_tab (t := t) hat hs
  · by_cases hp : preEnabled e (g % L.block) = true
    · simp [afterBar0, hp]
    · simp only [afterBar0, hp, Bool.false_eq_true, ↓reduceIte]
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h]

/-- The state after the last preload's load. -/
def after806 (t : TState) (v : Value) : TState :=
  { setRegs t [326] (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }

theorem load806_after {t : TState} {bs : List (Option Byte)} {v : Value} (hsub : t.sub = 0)
    (hv : rebuild 3 bs = .ok v) : afterLoad t [326] bs = after806 t v := by
  simp [afterLoad, hv, hsub, after806]

/-- **The data step after the last preload's load**: its facts after the event, from the stops
the control machine names (or the load's fault). -/
theorem pre63_open {d : D} (hs : d.c.site = .pre 63) {F : D → List (Nat × Value)}
    (hk : ∀ (t : TState) (x : Acc) (bs : List (Option Byte)) (v : Value) (c' : Control.D),
      (codeS e L g).AtD d t → rebuild 3 bs = .ok v →
      c' = { d.c with site := loopSite e (g % L.block) d.c.i } → t.pc + 1 = 807 →
      ((∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (after806 t v) t'' →
        Stops kernel Assumptions.all L g t'' → t''.pc = c'.site.pc) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (after806 t v)) →
      (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) (after806 t v) t' →
        Stops kernel Assumptions.all L g t' →
        Holds t'.regs (F ⟨c', record L d ⟨806, .rd x bs⟩ c'.site⟩)) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) (after806 t v)) :
    DataStep (codeS e L g) F d := by
  have pc : (codeS e L g).pc d = 806 := by
    change d.c.site.pc = 806
    rw [hs]
    rfl
  have pc0 : (code e L g).pc d = 806 := pc
  intro t ev u d' ins hat hi hc' hf hn
  have hat0 := atS_code hat
  have hn' : (code e L g).next d ev = some (some d') := hn
  rw [pc] at hc' hf
  have hc0 := hc'
  rw [Flow.code_806] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load (a := _) rfl rfl hf
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hsub : t.sub = 0 := hat.2.1.trans rfl
  cases hv : rebuild 3 bs with
  | error f => exact .inr (Machine.dead_of_fault (f := f) (by simp [afterLoad, hv]))
  | ok v =>
    simp only [MemAccess.regs] at hf ⊢
    rw [show List.filterMap id [some 326] = [326] from rfl, load806_after hsub hv] at hf ⊢
    have hpc : t.pc + 1 = 807 := by
      have h1 := hat.1
      omega
    exact hk t x bs v _ hat hv rfl hpc
      (stops_pc hat0 hi (by rw [pc0]; exact hc0) (by rw [pc0]; exact hf) hn')

/-- **The derived constants after the last preload.** -/
theorem der_pre63 {d : D} (hs : d.c.site = .pre 63) :
    DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  refine @pre63_open e L g d hs _ fun t x bs v c' hat hv hc hpc => ?_
  subst hc
  intro hstops
  obtain ⟨h482, hB⟩ := atS_const hat
  rw [hs] at hB
  have H : Holds t.regs (factsFrom (tk 807) (derV e L g)) :=
    holds_factsFrom_mono (holds_factsFrom_app (a := keysB) (b := [482]) hB
      ⟨(holds_mem h482 (v := e.prior) (by simp [startF])).trans rfl, trivial⟩) (by decide)
  refine derived_goal (q := (loopSite e (g % L.block) d.c.i).pc) ⟨?_, rfl, rfl, ?_⟩ hstops
    (fun R h => conv_der ?_ h)
  · show (inIvs ivsD (t.pc + 1) || evAtB kernel (t.pc + 1)) = true
    rw [hpc]; decide +kernel
  · show Holds _ (phi tk (fun _ => false) (derV e L g) (derV e L g) (t.pc + 1))
    rw [hpc]
    refine holds_of_pointwise fun r hr => ?_
    have hr' : r ≠ 326 := by
      simp [tk] at hr
      omega
    show (setRegs t [326] (t.acc ++ [v])).regs r = some (derV e L g r)
    rw [EventFrame.setRegs_regs_of_not_mem (by simpa using hr')]
    exact holds_mem H (mem_factsFrom (val := derV e L g) hr)
  · exact .inr (loopSite_mem _ _ _)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
