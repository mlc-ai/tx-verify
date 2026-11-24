-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts
public import Kernels.InklingRelDecode.Proof.Thread.ShapeBarOrd
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Flow.NotClc
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-!
# The ordinal of an event on named barrier 0

`Thread/ShapeBarOrd.lean` gives each abstract state of a thread a lower bound `tLb` for the number
of the thread's earlier barrier-0 events, which is exact at the sites of the common start
(`alloc`, `allocWr`, the two `bar.sync 0`, the load of the base word, and the workers' three
sites) and 2 at every other state. This file turns it into a statement about an execution:

* `ordinal_inv`: at every state a thread's machine is at before an event, the number of the
  thread's earlier events on barrier 0 is at least `tLb`, and equal to it at the sites of the
  common start;
* `start_event`: an event fired at a site of the common start is the `bar.sync 0` without a count
  (increment 1) or no barrier event at all (increment 0), so that the two arrivals of source
  ordinals 0 and 1 are the common start's, whatever the later arrivals' counts are;
* the barrier events of the kernel: `barSync` and `barSyncN` forms only, each on barrier 0 or 1
  without a count (`bar_event_static`, `bar_one_static`), and with count 128 only on barrier 0.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The bound of a thread state. -/
def tLb : TSt → Nat
  | .d s => dLb s
  | .w s => wLb s

/-- The increment of a thread state. -/
def tInc : TSt → Nat
  | .d s => dInc s
  | .w s => wInc s

theorem tLb_next {g : Nat} {s s' : TSt} {e : Event}
    (h : (threadCode L g Q).next s e = some (some s')) :
    tLb s' ≤ tLb s + tInc s ∧ (tLb s' < 2 → tLb s' = tLb s + tInc s ∧ tLb s < 2) := by
  cases s with
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from h)
    exact dLb_next ha
  | w s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some s') from h)
    exact wLb_next ha

/-- **The instructions at the sites of the common start**: the two `bar.sync 0` of increment 1,
and instructions that are no barrier (the allocation, the load of the base word) of increment 0. -/
theorem start_ops {s : TSt} (h : tLb s < 2) :
    (tInc s = 1 ∧ ∀ ins, kernel.code[TSt.pc s]? = some ins → ins.op = .barSync (.imm 0) true) ∨
    (tInc s = 0 ∧ ∀ ins, kernel.code[TSt.pc s]? = some ins → barOp ins.op = false) := by
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      cases site
      · refine .inr ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        rfl
      · refine .inr ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        rfl
      · refine .inl ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
        rfl
      · refine .inr ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
        rfl
      · refine .inl ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
        rfl
      all_goals simp [tLb, dLb] at h
    | _ => simp [tLb, dLb] at h
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site
      · refine .inl ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
        rfl
      · refine .inr ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
        rfl
      · refine .inl ⟨rfl, fun ins hc => ?_⟩
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
        rfl
      all_goals simp [tLb, wLb] at h
    | _ => simp [tLb, wLb] at h

/-- **An event at a site of the common start**: the `bar.sync 0` without a count (increment 1),
or no barrier event (increment 0). -/
theorem start_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) (hl : tLb s < 2) :
    (tInc s = 1 ∧ ∃ pc, e = ⟨pc, .bar 0 none .sync⟩) ∨
      (tInc s = 0 ∧ ∀ id c m, e.kind ≠ .bar id c m) := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  rcases start_ops hl with ⟨hi, hins⟩ | ⟨hi, hins⟩
  · refine .inl ⟨hi, ?_⟩
    have hop := hins ins hc
    rw [hop] at hf
    exact ⟨_, EvD.fires_barSync_imm (by decide) hf⟩
  · refine .inr ⟨hi, fun id c m hk => ?_⟩
    have := fires_bar_op hf hk
    rw [hins ins hc] at this
    cases this

/-- The number of barrier-0 events of the first `k + 1` events of a list. -/
theorem countP_succ {es : List Event} {k : Nat} {e : Event} (he : es[k]? = some e) :
    (es.take (k + 1)).countP (Execution.isBarId 0) =
      (es.take k).countP (Execution.isBarId 0) +
        (if Execution.isBarId 0 e = true then 1 else 0) := by
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- Every state outside the common start has bound 2: the epilogue's, the prologue's and softmax
region's, the exit role's, the loader's, the MMA warp's and the idle role's. -/
theorem tLb_epi (d : Epi.D) : tLb (.d (.epi d)) = 2 := rfl
theorem tLb_pro (d : ProA.D) : tLb (.d (.pro d)) = 2 := rfl
theorem tLb_exit (x : WComp.ExitD) : tLb (.w (.exit x)) = 2 := rfl

set_option maxRecDepth 100000 in
/-- **The kernel has no `bar.arrive`**: its barriers are `bar.sync` and `barrier.sync`. -/
theorem noBarArrive : kernel.NoBarArrive := by
  unfold Kernel.NoBarArrive
  decide +kernel

instance : Fact kernel.NoBarArrive := ⟨noBarArrive⟩

theorem tInc_zero_of {s : TSt} (h : ¬ tLb s < 2) : tInc s = 0 := by
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      cases site <;> simp_all [tLb, dLb, tInc, dInc]
    | _ => rfl
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site <;> simp_all [tLb, wLb, tInc, wInc]
    | _ => rfl

/-- **The ordinal measure**: at every state a launched thread's machine is at before its `k`-th
event, the thread's earlier events on barrier 0 number at least `tLb`, and exactly `tLb` at the
sites of the common start. -/
theorem ordinal_inv (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      tLb s ≤ ((X.tr g).take k).countP (Execution.isBarId 0) ∧
      (tLb s < 2 → ((X.tr g).take k).countP (Execution.isBarId 0) = tLb s) := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    have h0 : tLb (threadCode L g Q).init = 0 := by
      show tLb (if g % L.block < 128 then .d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) = 0
      split_ifs
      · exact dLb_init L g Q
      · exact wLb_init L g Q
    simp [h0]
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
        obtain ⟨h1, h2⟩ := ih s (by omega) hσ
        obtain ⟨h3, h4⟩ := tLb_next hn
        rw [countP_succ he]
        by_cases hl : tLb s < 2
        · have hc0 := h2 hl
          rcases start_event hX hS (show X.get (g, k) = some e from he) hσ hl with
            ⟨hi, pc, rfl⟩ | ⟨hi, hnb⟩
          · have hb : Execution.isBarId 0 ⟨pc, .bar 0 none .sync⟩ = true := by
              simp [Execution.isBarId]
            simp only [hb, ↓reduceIte]
            refine ⟨by omega, fun h5 => ?_⟩
            have := (h4 h5).1
            omega
          · have hb : Execution.isBarId 0 e = false := by
              obtain ⟨pc, kd⟩ := e
              cases kd <;> simp [Execution.isBarId]
              rename_i id c m
              intro hid
              exact hnb id c m (by simp [hid])
            simp only [hb, Bool.false_eq_true, ↓reduceIte]
            refine ⟨by omega, fun h5 => ?_⟩
            have := (h4 h5).1
            omega
        · have hi := tInc_zero_of hl
          by_cases hb : Execution.isBarId 0 e = true <;> simp only [hb, ↓reduceIte] <;>
            refine ⟨by omega, fun h5 => ?_⟩ <;> exact absurd (h4 h5).2 hl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
