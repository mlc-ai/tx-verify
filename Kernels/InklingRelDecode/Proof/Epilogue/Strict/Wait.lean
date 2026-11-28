-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Gate
public import Kernels.InklingRelDecode.Proof.Iface.RcpStep
public import Lemmas.Flow.StepsQFW
public import Lemmas.Flow.SegQDat
public import Lemmas.Flow.SegQTSat
import Kernels.InklingRelDecode.Gen.TypedLateLane06
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The strict step of the poll that opens the epilogue (pc 2565)

A failed poll returns to the poll; a successful one goes on through the window of the data
registers and the branch on the masked flag to the shuffle site or to the row store gate. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt PTX.Kernels.InklingRelDecode.Gen.TypedLate06

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value} {R : TState → Prop} {Wf : Event → Prop}
local notation "F" => facts e L g v
local notation "Lane" => (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)

/-- The single pieces of the epilogue's windows (outside the control spans). -/
def epiS (pc : Nat) : Bool := 2642 ≤ pc && pc ≤ 2673

abbrev RcpStep (L : Launch) (g : Nat) (R : TState → Prop) : Prop := Iface.RcpStep L g R

/-- The facts of a later pc, as a (trivial) strict segment. -/
theorem wk {Q : TState → Prop} {a p q : Nat} (h : ∀ r ∈ ctlLive q, r ∈ ctlLive p) :
    SegQ kernel Assumptions.all L g Q a (F p) a (F q) :=
  SegQ.weaken fun _ hR => holds_of_forall fun x hx => holds_mem hR (fsub (v := v) h x hx)

theorem poll_seg (ok : Bool) : SegQ kernel Assumptions.all L g Lane 2566
    ((2612, Value.pred ok) :: F 2565) (if ok then 2567 else 2565)
    ((2612, Value.pred ok) :: F 2565) :=
  by cases ok <;> exact SegQ.tauAll R (SegQF.braNotS _ Flow.code_2566
    (fun _ hR => holds_mem hR (List.mem_cons_self ..)) (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel))

/-- What the tables give at the poll: the table at the join pc 2674 is implied by the one at the
branch 2600, and the poll result is tagged a predicate. -/
theorem epi_tab : tagsSatF (lateQt 2674) (lateQt 2600) = true ∧
    afterF lateQt 2565 [(2612, .old .pred)] = true := by
  decide +kernel

/-- The site a successful poll goes to. -/
def readySite (e : Entry) (t : Nat) : Site := if e.skip then firstStore e.valid (lead t) else .shfl

/-- The window of the data registers after a successful poll, to the branch on the mask. -/
theorem win_2567 : SegQ kernel Assumptions.all L g Lane 2567 ((2612, Value.pred true) :: F 2565)
    2600 (F 2600) := by
  refine lw_l06_2567 (R := R) (fp3_epi (by decide +kernel)) ?_
    (fun p hp => List.mem_cons_of_mem _ (fsub (v := v) (by decide +kernel) p hp))
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  exact (by decide +kernel : ∀ r ∈ ctlLive 2600, r ∉ l06_2567_wr) r hr

/-- The branch on the mask, the window and the reciprocal, to the shuffle. -/
theorem to_shfl (hR : RcpStep L g R) (h : e.skip = false) :
    SegQ kernel Assumptions.all L g Lane 2567
    ((2612, Value.pred true) :: F 2565) 2603 (F 2603) := by
  have val : valueOf e L g v 173 = .pred false := congrArg Value.pred h
  have br := SegQT.bra (R := R) false win_2567 Flow.code_2600 (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel)
    (fun u hu _ => by
      obtain ⟨-, -, -, -, hF⟩ := hu
      exact holds_mem hF (mem_factsFrom_eq (by decide) val))
  have w : SegQ kernel Assumptions.all L g Lane 2601 (F 2600) 2602 (F 2602) :=
    lw_l06_2601 (R := R) (fp3_epi (by decide +kernel)) (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      exact (by decide +kernel : ∀ r ∈ ctlLive 2602, r ∉ l06_2601_wr) r hr)
      (fun p hp => fsub (v := v) (by decide +kernel) p hp) (fun _ h => nomatch h)
      (fun _ h => nomatch h)
  refine br.comp (w.comp ?_)
  · exact (segQ_dat (qt := lateQt) (R := R) (d := 1761) Flow.code_2602 (by rfl)
      (by decide +kernel) (fun p hp => fsub (v := v) (by decide +kernel) p hp) (fun p hp h => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        exact (by decide +kernel : ∀ r ∈ ctlLive 2603, r ≠ 1761) r hr h)
      (fun t hp hT hRt => hR _ Flow.code_2602 t hp hT hRt) :
      SegQ kernel Assumptions.all L g Lane 2602 (F 2602) 2603 (F 2603))

/-- The branch on the mask to the row store gate. -/
theorem to_gate (h : e.skip = true) : SegQ kernel Assumptions.all L g Lane 2567
    ((2612, Value.pred true) :: F 2565) (firstStore e.valid (lead (g % L.block))).pc
    (F (firstStore e.valid (lead (g % L.block))).pc) := by
  have val : valueOf e L g v 173 = .pred true := congrArg Value.pred h
  have br := SegQT.braS (R := R) true win_2567 Flow.code_2600 (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) epi_tab.1
    (fun u hu _ => by
      obtain ⟨-, -, -, -, hF⟩ := hu
      exact holds_mem hF (mem_factsFrom_eq (by decide) val))
  exact br.comp ((wk (v := v) (by decide +kernel)).comp store_gate_seg)

/-- **The strict step of the poll**. -/
theorem sstep_wait (hR : RcpStep L g R) (ev : Event) : (code e L g).StepForQP (QTF lateQt)
    (TauAll kernel Assumptions.all L g R) Wf ⟨.wait, v⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.waitFP (C := code e L g) (d := ⟨.wait, v⟩)
    (dst := fun ok => ⟨if ok then readySite e (g % L.block) else .wait, v⟩) Flow.code_2565 ?_ ?_
    rfl rfl (fun ok => by cases ok <;> rfl) (fun ok => by cases ok <;> rfl) ?_
    epi_tab.2 ?_ ev
  · change 2612 ∉ (factsFrom (ctlLive 2565) _).map Prod.fst
    rw [factsFrom_keys]
    decide +kernel
  · intro m q ok sc
    cases ok <;> rfl
  · intro ok
    cases ok
    · trivial
    · change Inv e _ ⟨readySite e _, v⟩
      unfold readySite
      split
      · exact first_inv ..
      · trivial
  · intro ok
    cases ok
    · change SegQ kernel Assumptions.all L g Lane 2566 _ 2565 _
      exact (poll_seg (e := e) (v := v) (L := L) (g := g) (R := R) false).comp
        (SegQ.weaken fun _ hR => holds_of_forall fun p hp =>
          holds_mem hR (List.mem_cons_of_mem _ hp))
    · change SegQ kernel Assumptions.all L g Lane 2566 _
        (readySite e (g % L.block)).pc (F (readySite e (g % L.block)).pc)
      unfold readySite
      cases hk : e.skip
      · exact (poll_seg (e := e) (v := v) (L := L) (g := g) (R := R) true).comp
          (to_shfl (v := v) hR hk)
      · exact (poll_seg (e := e) (v := v) (L := L) (g := g) (R := R) true).comp
          (to_gate (v := v) hk)

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
