-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WmAhead
public import Kernels.InklingRelDecode.Proof.Protocol.WkLdBlock
public import Kernels.InklingRelDecode.Proof.Lib.KvSingle

@[expose] public section

/-!
# The phase of `kv_ready` when a lane of the MMA warp polls it

A lane `g` of the MMA warp at its poll of `kv_ready (i % 3)` at the end of its trace has made
`q = i / 3` successful polls of it (`Wv.mma_polls_le`). The barrier's final phase is

* at least `q` (`full_phase_ge`): the lane's last successful poll found phase `q` or later
  (`Ring.Kv.lane_poll_full`) and phases do not decrease (`CheckedLog.phase_mono`);
* at most `q + 1` (`full_phase_le`): its arrival units are at least its phase (`Accounted`), and
  each is a counted arrival item of a distinct use (`Ring.Kv.full_count`), so with phase `q + 2`
  an arrival of a use `u ≥ q + 1` is counted. The loader's poll of `kv_empty` for use `q + 1`
  guards it (`Ring.Kv.guardP`) and observed the commit of use `q` (`observes_empty` of the ring of
  items, `Ring.Kv.SE_op`), which no lane of `g`'s warp has made (`Wm.no_commit_ahead`).

With the parity of the poll, the final phase is `q` (`full_phase_eq`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)
open PTX.MBarrier hiding okPolls

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The arrival units of the full barrier's history are at least its final phase. -/
theorem full_units_ge (hX : Consistent L kernel asms mem0 X) {S : Ring.Kv.Slot}
    (H : Ring.Kv.Hyp L kernel asms X S) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    st.phase ≤ arrivalUnits (X.objects S.full) := by
  have hch := X.objects_checked hX S.full
  obtain ⟨hpend, hacc⟩ := (hch.accounted H.full_noInval le_rfl).2 st hst
  have hexp := PairTmaRing.expected_of_init hX H.full_init H.full_noInval hst
  have hinc := Ring.Kv.full_noIncrement H
  simp only [unitsBefore, List.take_length] at hacc
  rw [hexp, hinc] at hpend hacc
  omega

/-- **A counted arrival of a use past `q`** when the full barrier's arrival units exceed
`q + 1`. -/
theorem arrival_past (hX : Consistent L kernel asms mem0 X) {S : Ring.Kv.Slot}
    (H : Ring.Kv.Hyp L kernel asms X S) {q : Nat}
    (hu : q + 2 ≤ arrivalUnits (X.objects S.full)) :
    ∃ x ∈ Ring.Kv.SF X S, x.1.val = 0 ∧ q + 1 ≤ x.2 := by
  classical
  set T := (Ring.Kv.SF X S).filter
    (fun x => x.1 ∈ ({⟨0, by omega⟩} : Finset Ring.Kv.Kind)) with hT
  have hle : unitsBefore (X.objects S.full) (X.objects S.full).length ≤ T.card :=
    MbarRing.Round.units_le_of_uses (X.objects_checked hX S.full)
      (fun x : Ring.Kv.Kind × Nat => Ring.Kv.itF X S x.1 x.2) T
      (fun k r c tx hr hf ha => (Ring.Kv.full_count H k r c tx hr hf ha).1)
      (fun k _ r c tx hr hf ha => (Ring.Kv.full_count H k r c tx hr hf ha).2)
  simp only [unitsBefore, List.take_length] at hle
  by_contra hno
  push Not at hno
  have hsub : T ⊆ ({⟨0, by omega⟩} : Finset Ring.Kv.Kind) ×ˢ Finset.range (q + 1) := by
    intro x hx
    obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    have hx0' : x.1.val = 0 := by
      have := Finset.mem_singleton.mp hx0
      rw [this]
    refine Finset.mem_product.mpr ⟨hx0, Finset.mem_range.mpr ?_⟩
    have := hno x hxS hx0'
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_singleton, Finset.card_range] at hc
  omega

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X)
include hpre hX hf hR

/-- **The final phase of `kv_ready` is at most one past the polling lane's polls.** -/
theorem full_phase_le {S : Ring.Kv.Slot} (H : Ring.Kv.Hyp L kernel asms X S)
    {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    (hempty : S.empty = kvEmpty L (g / L.block) (d.i % 3)) (hcw : SameWarp L S.cm g)
    {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    st.phase ≤ d.i / 3 + 1 := by
  by_contra hlt
  push Not at hlt
  have hu := full_units_ge hX H hst
  obtain ⟨x, hx, hx0, hxu⟩ := arrival_past hX H (q := d.i / 3) (by omega)
  have hg := Ring.Kv.guardP H hx (n := d.i / 3 + 1) (by omega) hxu
  rw [Ring.Kv.kOwner_of_zero hx0] at hg
  have hwp : X.RefPresent (.thread (Ring.Kv.wE X S 0 (d.i / 3 + 1))) :=
    MbarRing.Round.Slot.present_of_guard hg
  obtain ⟨hy, -⟩ := (Ring.Kv.ring hX H).observes_empty hX.depAcyclic (a := 0) (n := d.i / 3)
    hwp 0
  obtain ⟨-, ⟨pc, sp, he, hm, -, hcnt⟩, -⟩ := Ring.Kv.SE_op H hy
  rw [hempty] at hm hcnt
  exact no_commit_ahead hpre hX hf hR hσ hw hcw he hm
    (by simp only [Ring.Kv.cmE] at hcnt ⊢; omega)

/-- **The final phase of `kv_ready` is at least the polling lane's polls.** -/
theorem full_phase_ge {S : Ring.Kv.Slot} (H : Ring.Kv.Hyp L kernel asms X S)
    {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    (hfull : S.full = kvReady L (g / L.block) (d.i % 3)) {st : State}
    (hst : stateBefore (X.objects S.full) (X.objects S.full).length = some st) :
    d.i / 3 ≤ st.phase := by
  have hs : d.site ≠ .setMaxReg := by rw [hw]; nofun
  obtain ⟨-, hk⟩ := Proof.Wv.mma_polls_le hpre hX hf hR le_rfl hσ hs
  rw [List.take_length] at hk
  have hq := hk _ (Nat.mod_lt d.i (by omega))
  have hpo : Ring.Mm.polled d = d.i := by simp [Ring.Mm.polled, hw]
  rw [hpo, Ring.below_of_slot (Nat.mod_lt d.i (by omega)) rfl, ← hfull] at hq
  rcases Nat.eq_zero_or_pos (d.i / 3) with h0 | hpos
  · omega
  obtain ⟨pc, p, acq, sc, he, hc⟩ :=
    MbarRing.Poll.nth_spec (X := X) (g := g) (m := S.full) (n := d.i / 3 - 1) (by omega)
  obtain ⟨i, w, st', hi, -, hst', hge, -⟩ := Ring.Kv.lane_poll_full hX H he
  have hil : i ≤ (X.objects S.full).length := (List.getElem?_eq_some_iff.mp hi).1.le
  obtain ⟨t, ht, hmono⟩ :=
    (X.objects_checked hX S.full).phase_mono H.full_noInval hil le_rfl hst'
  rw [hst] at ht
  cases ht
  omega

end

end
end PTX.Kernels.InklingRelDecode.Proof.Wm
