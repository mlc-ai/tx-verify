-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerEvents
public import Kernels.InklingRelDecode.Proof.Interface.BarOrdinal
public import Kernels.InklingRelDecode.Proof.Thread.LedgerB0

@[expose] public section

/-!
# The kind of an event on named barrier 0, from its state

An event on named barrier 0 is `bar.sync 0` without a count or `bar.sync 0, 128`
(`bar_kind_op`). The second is a default-partition thread's (no worker state has an instruction
`bar.sync 0, 128`: `Ledger.worker_b0`, `idle_b0`, `loader_b0`, `mma_b0`, `exit_b0`), and an event
of that form is never fired from a site of the common start, so it follows at least two
barrier-0 events of its thread (`ordinal_inv`, `start_event`).

* `cls_inv`: a thread's states are the default partition's exactly when the thread is
  (`g % L.block < 128`);
* `bar0_event_class`: an event on barrier 0 has no count, or the count 128 and a default-partition
  thread and at least two earlier barrier-0 events. This is the source classification
  `NamedBar.PhSources` asks of the arrivals of barrier 0.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The class of a thread state. -/
def TSt.isD : TSt → Prop
  | .d _ => True
  | .w _ => False

/-- **A thread's states are of its class**: the default partition's machine for a thread of the
default partition, the worker's machine for the others. -/
theorem cls_inv {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      (s.isD ↔ g % L.block < 128) := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    show TSt.isD (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) ↔ _
    split_ifs with h <;> simp [TSt.isD, h]
  | succ k ih =>
    intro s' hk hs'
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        have ih' := ih s (by omega) hσ
        cases s with
        | d s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
            (Option.map TSt.d) = some (some s') from hn)
          simpa [TSt.isD] using ih'
        | w s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
            (Option.map TSt.w) = some (some s') from hn)
          simpa [TSt.isD] using ih'

/-- No worker state's instruction is `bar.sync 0, 128`. -/
theorem w_b0_ne (s : WComp.WSt) : b0At (WComp.pc s) ≠ 2 := by
  cases s with
  | worker w => have := worker_b0 w.site; simp only [WComp.pc]; split at this <;> omega
  | idle d => have := idle_b0 d.site; simp only [WComp.pc]; omega
  | loader d P => have := loader_b0 d.site; simp only [WComp.pc]; omega
  | mma d P => have := mma_b0 d.site; simp only [WComp.pc]; omega
  | exit x => have := exit_b0 x.site; simp only [WComp.pc]; split at this <;> omega

/-- **An event on named barrier 0** has no count, or the count 128, a thread of the default
partition and at least two earlier barrier-0 events of its thread. -/
theorem bar0_event_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) :
    cnt = none ∨ (cnt = some 128 ∧ g % L.block < 128 ∧
      2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  have hk : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar 0 cnt mode⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar 0 cnt mode⟩ : Event).kind = .bar 0 cnt mode
    from rfl) with ⟨al, hop⟩ | ⟨-, al, hop⟩
  · left
    rw [hop] at hf'
    have := EvD.fires_barSync_imm (by decide) hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    exact this.2.2.1
  · right
    rw [hop] at hf'
    have := EvD.fires_barSyncN_128 hb hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    obtain ⟨-, -, hcnt, -⟩ := this
    refine ⟨hcnt, ?_, ?_⟩
    · have hd := (cls_inv k s hk hσ)
      by_contra hn
      have hw : ¬ s.isD := fun h => hn (hd.mp h)
      cases s with
      | d s0 => exact hw trivial
      | w s0 =>
        have hpc : b0At (TSt.pc (.w s0)) = 2 := by
          simp only [b0At, hc', hop]
        exact w_b0_ne s0 hpc
    · by_contra hlt
      have hl : tLb s < 2 := by
        have := (ordinal_inv hX hS k s hk hσ).1
        omega
      rcases start_event hX hS he hσ hl with ⟨-, pc', h⟩ | ⟨-, h⟩
      · simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at h
        rw [hcnt] at h
        exact absurd h.2.1 (by simp)
      · exact h 0 cnt mode rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
