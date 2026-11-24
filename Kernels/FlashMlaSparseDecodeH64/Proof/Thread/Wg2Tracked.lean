-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputFootprint
public import Lemmas.Flow.Final
public import Lemmas.Flow.TraceInduction
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # When the dequantizer's composed machine follows firing events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Flow PTX.Proof

private def lengthBindings (P : Params) (s : Site) : Prop :=
  (s = .lenOrig → ∃ x, P.topkLenBase = some x) ∧
    (s = .lenExtra → ∃ x, P.extraTopkLenBase = some x)

private theorem lengthBindings_init {P : Params} {L : Launch} {g : Nat} :
    lengthBindings P (init P L g).site := by
  cases h0 : P.topkLenBase <;> cases h1 : P.extraTopkLenBase <;>
    simp [lengthBindings, init, firstSite, h0, h1]

private theorem lengthBindings_next {P : Params} {L : Launch} {g : Nat} {d d' : D}
    {e : Event} (hn : next P L g d e = some (some d')) :
    lengthBindings P d'.site := by
  cases hd : d.site <;> simp only [next, nextSite, hd] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [lenOrigNext, lenExtraNext, afterScale, afterRaw, afterStore, afterFree]
    repeat' split_ifs
    all_goals simp_all [lengthBindings]
    all_goals cases hP : P.extraTopkLenBase <;> simp_all

private def hasBindings (P : Params) : Option Machine.ThreadD → Prop
  | some (.wg2 d) => lengthBindings P d.site
  | _ => True

private theorem hasBindings_next {P : Params} {L : Launch} {g : Nat} {d d' : Option Machine.ThreadD}
    {e : Event} (hn : (Machine.machine P L g).next d e = some d') : hasBindings P d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> first | exact lengthBindings_init | trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case wg2 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' h
        cases hn
        exact lengthBindings_next h
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

private theorem lengthBindings_of_trace {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : D} (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) :
    lengthBindings P d.site :=
  (hs.produces (hX.thr g hg)).prefix_induction (fun q _ => hasBindings P q) trivial
    (fun _ _ _ _ _ _ _ hn => hasBindings_next hn) i (some (.wg2 d)) hstate

/-- The exact data obligations for accepting a raw or scale read into the role state. -/
def ValidRead (d : D) (e : Event) : Prop :=
  match d.site with
  | .scale _ j => ∀ a bs, e.kind = .rd a bs →
      rebuild 3 bs = .ok (b32 (scaleBits bs)) ∧
        (j.val = 3 → ScaleWordOk (d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * scaleBits bs))
  | .raw _ _ => ∀ a bs, e.kind = .rd a bs →
      rebuild 3 bs = .ok (b64 (rawBits bs)) ∧ RawWordOk (rawBits bs)
  | _ => True

private theorem kept_of_next {P : Params} {L : Launch} {g : Nat} {d : D} {e : Event}
    (hn : next P L g d e ≠ some none ∨ d.site = .barrier) :
    Machine.next P L g (.wg2 d) e ≠ some none := by
  simp only [Machine.next]
  split
  · intro h
    cases h
  · rename_i h
    rcases hn with hne | hd
    · exact (hne h).elim
    · rw [ite_eq_left hd]
      intro h
      cases h
  · intro h
    cases h

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D} {e : Event}
    {o : Option TState} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

set_option maxRecDepth 4096 in
/-- A followed dequantizer is never dismissed by a firing event with validated raw inputs.
The optional length values come directly from the launch memory and the selected read-only rule. -/
theorem never_dismiss (hs : (Machine.machine P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (he : X.get (g, i) = some e) (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o)
    (hRead : ValidRead d e) :
    Machine.next P L g (.wg2 d) e ≠ some none := by
  apply kept_of_next
  cases o with
  | none =>
    left
    obtain ⟨_, _, hFire⟩ := hf
    rcases fires_none_ends hFire with ⟨f, hk⟩ | hk <;>
      cases hd : d.site <;> simp [next, nextSite, hd, hk]
  | some u =>
    have hf' : (machine P L g).Fired (some (.inr d)) e (some u) := hf
    have hi : Inv P L g d := (Exists.choose_spec hf).1.2
    have binding := lengthBindings_of_trace hX (Frame.lt_of_get hX he) hs hstate
    cases hd : d.site
    case lenOrig =>
      left
      obtain ⟨p, hp⟩ := binding.1 hd
      obtain ⟨bs, hk, -⟩ := fired_length_event (orig := true) hd hf'
      rw [runtimeLenAddr_main hpre hp hi.batch] at hk
      have hnc : ncLoads.contains e.pc = true := by
        obtain ⟨t, ht, hFire⟩ := hf
        have ht' : t.pc = d.site.pc := ht.1.1
        rw [fires_pc hFire, ht', hd]
        decide
      have hv := LaunchReads.rebuild_main (g := g) hpre hX hi.batch hp he ⟨hk, hnc⟩
      simp [next, nextSite, hd, hk, hv, Wg0.eOf, eOf]
    case lenExtra =>
      left
      obtain ⟨p, hp⟩ := binding.2 hd
      obtain ⟨bs, hk, -⟩ := fired_length_event (orig := false) hd hf'
      rw [runtimeLenAddr_extra hpre hp hi.batch] at hk
      have hnc : ncLoads.contains e.pc = true := by
        obtain ⟨t, ht, hFire⟩ := hf
        have ht' : t.pc = d.site.pc := ht.1.1
        rw [fires_pc hFire, ht', hd]
        decide
      have hv := LaunchReads.rebuild_extra (g := g) hpre hX hi.batch hp he ⟨hk, hnc⟩
      simp [next, nextSite, hd, hk, hv, Wg0.eOf, eOf]
    case scale r j =>
      left
      obtain ⟨a, bs, hk, ha, hz⟩ := fired_scale_event hpre hd hf'
      simp only [ValidRead, hd] at hRead
      obtain ⟨hv, hw⟩ := hRead a bs hk
      by_cases hj : j.val = 3
      · simp [next, nextSite, hd, hk, ha, hz, hv, hw hj]
      · simp [next, nextSite, hd, hk, ha, hz, hv, hj]
    case raw r s =>
      left
      obtain ⟨a, bs, hk, ha, hz⟩ := fired_raw_event hpre hd hf'
      simp only [ValidRead, hd] at hRead
      obtain ⟨hv, hw⟩ := hRead a bs hk
      simp [next, nextSite, hd, hk, ha, hz, hv, hw, rawBytesPerThread]
    case store r s =>
      left
      obtain ⟨a, hk, ha, hz⟩ := fired_store_event hpre hd hf'
      simp [next, nextSite, hd, hk, ha, hz]
    case barrier => exact .inr rfl
    all_goals
      left
      cases hk : e.kind <;> simp [next, nextSite, hd, hk]

/-- An executed dequantizer length load lies inside its optional launch array. -/
theorem length_footprint (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .lenOrig ∨ d.site = .lenExtra)
    (hFire : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    NcInputEvent P e := by
  cases o with
  | none =>
    intro a bs hk
    obtain ⟨_, _, hf⟩ := hFire
    rcases fires_none_ends hf with ⟨_, h⟩ | h <;> rw [hk] at h <;> cases h
  | some u =>
    have hf : (machine P L g).Fired (some (.inr d)) e (some u) := hFire
    have hi : Inv P L g d := (Exists.choose_spec hFire).1.2
    have hBinding := lengthBindings_of_trace hX (Frame.lt_of_get hX he) hs hState
    rcases hSite with h | h
    · obtain ⟨ptr, hp⟩ := hBinding.1 h
      obtain ⟨bs, hk, _⟩ := fired_length_event (orig := true) h hf
      rw [runtimeLenAddr_main hpre hp hi.batch] at hk
      exact NcInputEvent.mainLength hp hi.batch hk
    · obtain ⟨ptr, hp⟩ := hBinding.2 h
      obtain ⟨bs, hk, _⟩ := fired_length_event (orig := false) h hf
      rw [runtimeLenAddr_extra hpre hp hi.batch] at hk
      exact NcInputEvent.extraLength hp hi.batch hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
