-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QLoad
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Ld
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QuerySite
public import Kernels.InklingRelDecode.Proof.Prologue.Data.Query
public import Lemmas.Flow.StepsQGuard

@[expose] public section

/-! # The strict step of a query load -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem q_ld_tags1 : ∀ j : Fin 64, (proQt (queryPc j + 1)).lookup (qDst j) = none := by
  decide +kernel

theorem q_ld_tags2 : ∀ j : Fin 64, ∀ p ∈ proQt (queryPc j + 1), p.1 ≠ qDst j →
    (proQt (queryPc j)).lookup p.1 = some p.2 ∨ ([] : Env).lookup p.1 = some p.2 := by
  decide +kernel

/-- **A query load** whose group is on strictly steps to the next load or the first store. -/
theorem step_ldq (d : Data.D) (j : Fin 64) (hs : d.c.site = .ldq j) (hk : Ok Q L g d)
    (e : Event) : (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c0, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c : Control.D := ⟨.ldq j, a, b, c0, won, bcast⟩
  have hon : queryOn (g % L.block) (j.val / 16) c = true := hI
  refine Code.ldWGQ (C := Data.code Q L g w) (qt := proQt) (ex := []) (P := fun v => v.bytes = 2)
    (r := qDst j) (d := ⟨c, vs⟩) (f := fun v => ⟨{c with site := afterQuery c (g % L.block) j},
      upd vs j v⟩) (qLoadPair (L := L) (g := g) j).2 rfl rfl rfl rfl ?_ ?_ rfl rfl ?_
    (fun _ _ => typed_nil') ?_ ?_ ?_ e ins hat ⟨hI, hpay⟩ hc hq hw hf
  · exact fun e hWf hpc x bs hk => hWf.2.2.1 j hpc x bs hk
  · intro x bs v h hP
    simp [c, Data.code, Data.succ, Control.next, Data.record, h, Except.toOption, Data.loadVal, upd]
  · obtain ⟨h1, h2⟩ := Data.ldq_fresh j
    exact fresh_reg (d := ⟨c, vs⟩) h1 (fun h => by
      obtain ⟨τ, hτ, he⟩ := List.mem_map.mp h
      exact h2 τ hτ he)
  · exact ld_hv (n := queryPc j + 1) (r := qDst j) (q_ld_tags1 j)
  · exact ld_hq (n := queryPc j) (r := qDst j) (q_ld_tags2 j)
  · intro v hv
    obtain ⟨hi, hle, hlt, hsite, hoff, hon'⟩ := Data.after_site c (g % L.block) j hon
    have pay : Payload {c with site := afterQuery c (g % L.block) j} :=
      payload_next (Q := Q) (L := L) (g := g) (d := c) (e := ⟨0, .exit⟩)
        (t := {c with site := afterQuery c (g % L.block) j}) rfl hpay (fun k h => by cases h)
    by_cases h64 : hi < 64
    · have e1 : afterQuery c (g % L.block) j = .ldq ⟨hi, h64⟩ := by
        rw [hsite]; simp [qSiteAt, h64]
      have hj : j.val < 63 := by omega
      rw [e1] at pay
      rw [e1]
      refine ⟨rfl, rfl, ⟨hon' h64, pay⟩, ?_⟩
      exact dFacts_seg (pre := [(qDst j, v)]) (ldq_span (w := w) c vs v ⟨j, hj⟩ hon ⟨hi, h64⟩
        hlt hoff)
    · have e1 : afterQuery c (g % L.block) j = .stq 0 0 := by
        rw [hsite]; simp [qSiteAt, h64]
      rw [e1] at pay
      rw [e1]
      refine ⟨rfl, rfl, ⟨trivial, pay⟩, ?_⟩
      by_cases hj : j.val < 63
      · exact dFacts_seg (pre := [(qDst j, v)]) (ldq_stq (w := w) c vs v ⟨j, hj⟩ hon hk.qBytes hv
          fun n h1 h2 => hoff n h1 (by omega))
      · have : j = 63 := Fin.ext (by omega)
        subst this
        exact dFacts_seg (pre := [(qDst 63, v)]) (ldq_last (w := w) c vs v hon hk.qBytes hv)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
