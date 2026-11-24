-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Interface.LedgerFacts
public import Kernels.InklingRelDecode.Proof.Thread.LkB0

@[expose] public section

/-!
# The aligned barriers without a count of a thread, from its abstract states

`Thread/LkB0.lean` gives every abstract state of a thread the number `tN0` of the thread's earlier
`bar.sync 0` events, and says whether its own instruction is `bar.sync 0` (`tB0`). The aligned
barriers without a thread count (`Kernel.isAlignedCtaBar`) of the kernel are exactly its
`bar.sync 0` (the program text has `bar.sync 0` aligned and `barrier.sync 1` not:
`kernel_barSync_aligned`), so:

* `event_aln`: an event fired from a state is an aligned barrier without a count exactly when the
  state's instruction is `bar.sync 0`;
* `aln_inv`: the number of aligned barriers before a state is `tN0`;
* `aln_before_le`: an aligned barrier has at most two earlier ones;
* `exit_aln`: an exit has made exactly three aligned barriers.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number of earlier `bar.sync 0` of a state. -/
def tN0 : TSt → Nat
  | .d s => dN0 s
  | .w s => wN0 s

/-- Whether a state's instruction is `bar.sync 0`. -/
def tB0 : TSt → Bool
  | .d s => dB0 s
  | .w s => wB0 s

theorem t_b0 (s : TSt) : b0At (TSt.pc s) = 1 ↔ tB0 s = true := by
  cases s with
  | d s => exact d_b0 s
  | w s => exact w_b0 s

theorem tN0_next {g : Nat} {s s' : TSt} {e : Event}
    (h : (threadCode L g Q).next s e = some (some s')) : tN0 s' = tN0 s + bInc (tB0 s) := by
  cases s with
  | d s =>
    obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from h)
    exact d_next_n0 ha
  | w s =>
    obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some s') from h)
    exact w_next_n0 ha

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
include hpre hX hS

/-- **An event without a count is its state's `bar.sync`**: its instruction. -/
theorem event_bar_op {g k : Nat} {s : TSt} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some s)) {pc id : Nat} {m : BarMode} (hk : e = ⟨pc, .bar id none m⟩)
    :
    ∃ ins al, kernel.code[TSt.pc s]? = some ins ∧ ins.op = .barSync (.imm (id : Int)) al ∧
      pc = TSt.pc s := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hpc : e.pc = TSt.pc s := Frame.event_pc hS hX he hσ
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  subst hk
  rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar id none m⟩ : Event).kind = .bar id none m
    from rfl) with ⟨al, hop⟩ | ⟨-, al, hop⟩
  · exact ⟨ins, al, hc', hop, hpc⟩
  · rw [hop] at hf'
    have := EvD.fires_barSyncN_128 hb hf'
    simp only [Event.mk.injEq, Kind.bar.injEq] at this
    exact absurd this.2.2.1 (by simp)

/-- **An event is an aligned barrier without a count exactly when its state's instruction is
`bar.sync 0`.** -/
theorem event_aln {g k : Nat} {s : TSt} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some s)) :
    kernel.isAlignedCtaBar e = true ↔ tB0 s = true := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hmem := List.mem_of_getElem? hc'
  have hall := List.all_eq_true.mp kernel_barSync_aligned ins hmem
  constructor
  · intro h
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [Kernel.isAlignedCtaBar, Bool.false_eq_true] at h
    rename_i id c m
    cases c with
    | some n => simp at h
    | none =>
      obtain ⟨ins', al, hc2, hop, hpc⟩ := event_bar_op hpre hX hS he hσ (pc := pc) (id := id)
        (m := m) rfl
      have hins : ins' = ins := Option.some.inj (hc2.symm.trans hc')
      subst hins
      subst hpc
      simp only [Kernel.alignedAt, hc2, hop, Op.aligned] at h
      rw [hop] at hall
      simp only [decide_eq_true_eq] at hall
      have hid : (id : Int) = 0 := hall.2.mp h
      have hid0 : id = 0 := by omega
      subst hid0
      rw [← t_b0]
      simp [b0At, hc2, hop]
  · intro h
    have h1 := (t_b0 s).mpr h
    obtain ⟨al, hop⟩ : ∃ al, ins.op = .barSync (.imm 0) al := by
      simp only [b0At, hc'] at h1
      split at h1 <;> first | (rename_i al hq; exact ⟨al, hq⟩) | (exfalso; simp at h1)
    rw [hop] at hf' hall
    have hev := EvD.fires_barSync_imm (id := 0) (by decide) hf'
    simp only [decide_eq_true_eq] at hall
    have hal : al = true := hall.2.mpr trivial
    subst hev
    simp [Kernel.isAlignedCtaBar, Kernel.alignedAt, hc', hop, Op.aligned, hal]

omit hpre hX hS in
theorem aln_init (L : Launch) (g : Nat) (Q : Params) : tN0 (threadCode L g Q).init = 0 := by
  show tN0 (if g % L.block < 128 then .d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init) = 0
  split_ifs
  · show dN0 (.dstart (DStart.D.start L g)) = 0
    unfold DStart.D.start
    split_ifs <;> rfl
  · rfl

/-- **The aligned barriers before a state**: at every state a launched thread's machine is at
before its `k`-th event, the thread's earlier aligned barriers without a count number `tN0`. -/
theorem aln_inv {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      ((X.tr g).take k).countP kernel.isAlignedCtaBar = tN0 s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    simp only [List.take_zero, List.countP_nil]
    exact (aln_init L g Q).symm
  | succ k ih =>
    intro s' hk hs'
    have hs' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs'
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs'; simp at hs'
    | some o =>
      cases o with
      | none => rw [hσ] at hs'; simp [Flow.Code.toMachine] at hs'
      | some s =>
        rw [hσ] at hs'
        simp only [Option.bind_some] at hs'
        have hn : (threadCode L g Q).next s e = some (some s') := hs'
        have h1 := ih s (by omega) hσ
        have h2 := tN0_next hn
        have h3 := event_aln hpre hX hS (show X.get (g, k) = some e from he) hσ
        rw [countP_take_succ _ he, h1, h2]
        by_cases hb : tB0 s = true
        · simp [hb, h3.mpr hb, bInc]
        · simp [hb, mt h3.mp hb, bInc]

/-- **An aligned barrier has at most two earlier aligned barriers.** -/
theorem aln_before_le (ht : Frame.Tracked (code L Q) X) {g i : Nat} {ev : Event}
    (he : X.get (g, i) = some ev) (hm : kernel.isAlignedCtaBar ev = true) :
    ((X.tr g).take i).countP kernel.isAlignedCtaBar ≤ 2 := by
  have hne : ∀ pc f, ev ≠ ⟨pc, .ub f⟩ := by
    intro pc f h
    subst h
    simp [Kernel.isAlignedCtaBar] at hm
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he hne
  rw [aln_inv hpre hX hS i s (event_le he) hσ]
  have hb := (event_aln hpre hX hS he hσ).mp hm
  cases s with
  | d s => exact d_b0_le hb
  | w s => exact w_b0_le hb

/-- **An exit has made exactly three aligned barriers**: the common start's two and the last. -/
theorem exit_aln (ht : Frame.Tracked (code L Q) X) {g j pc : Nat}
    (he : X.get (g, j) = some ⟨pc, .exit⟩) :
    ((X.tr g).take j).countP kernel.isAlignedCtaBar = 3 := by
  rcases exit_event_state hX hS ht he with ⟨d, hσ, hs⟩ | ⟨x, hσ, hs⟩
  · rw [aln_inv hpre hX hS j _ (event_le he) hσ]
    exact d_exit_n0 d hs
  · rw [aln_inv hpre hX hS j _ (event_le he) hσ]
    exact w_exit_n0 x hs

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
