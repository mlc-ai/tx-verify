-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingObjects
public import Lemmas.Protocol.PairTmaRing.Attribution

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # The dequantized tile and PV reuse ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

noncomputable section

set_option maxRecDepth 4096

abbrev full (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  Object.dequantReady.loc L cta slot

abbrev empty (L : Launch) (cta : Nat) (slot : Fin 2) : Loc :=
  Object.svDone.loc L cta slot

abbrev producer (L : Launch) (cta : Nat) : Fin 128 → Nat := RawRing.consumer L cta

/-- Every producer lane belongs to the dequantizer warpgroup. -/
theorem producer_wg2 {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (cta : Nat) (lane : Fin 128) : wgOf L (producer L cta lane) = 2 := by
  have := lane.isLt
  simp only [wgOf, tidOf_eq hpre, producer, RawRing.consumer, hpre.block]
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The dequantizer's successful PV waits guard its ready arrival for this slot use. -/
theorem guard_ready_arrival {cta n i tag : Nat} {slot : Fin 2} {lane : Fin 128} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (he : X.get (producer L cta lane, i) = some ⟨tag, .arrive (full L cta slot) 0 1 true scope⟩)
    (hn : n ≤ PTX.Flow.arrivals (full L cta slot) ((X.tr (producer L cta lane)).take i)) :
    Resumes kernel X (producer L cta lane, Poll.nth X (empty L cta slot) (producer L cta lane) n)
      (producer L cta lane, i) := by
  let g := producer L cta lane
  have hg := Frame.lt_of_get hX he
  have hFollow := MachineTracking.tracked_nonsoftmax_wg hpre hX
    (fun _ hg => Machine.code_sound hpre hg) (show wgOf L g ≠ 0 by
      rw [producer_wg2 hpre cta lane]; decide) i
  obtain ⟨⟨hc, d, hb, hd, hst⟩, _, _, _, _⟩ :=
    arrival_at_followed hpre hX (hs g hg) hFollow he rfl
  obtain ⟨ha, hp⟩ := Wg2GemmTrace.composed_publication_counts hpre
    ((hs g hg).produces (hX.thr g hg)) hst hd
  rw [hc, hb] at ha hp
  change PTX.Flow.arrivals (full L cta slot) ((X.tr g).take i) = d.block / 2 at ha
  change PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take i) = d.block / 2 + 1 at hp
  rw [ha] at hn
  have hcount : n + 1 ≤ PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take i) := by
    omega
  exact Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    (PTX.len_of_get he) hcount

/-- The guard for a dequantizer publication already present in the counted ring. -/
theorem guard_ready {cta n : Nat} {slot : Fin 2} {x : Fin 128 × Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (hx : x ∈ Unit.S X (full L cta slot) (producer L cta)) (hn : n ≤ x.2) :
    Resumes kernel X (producer L cta x.1, Poll.nth X (empty L cta slot) (producer L cta x.1) n)
      (Unit.it X (full L cta slot) (producer L cta) x.1 x.2) := by
  let F := dequant_obj hpre hX hs (cta := cta) (slot := slot)
  obtain ⟨_, ⟨_, _, he⟩, hu⟩ := F.S_rec hx
  exact guard_ready_arrival hpre hX hs he (hu.symm ▸ hn)

/-- The MMA thread's successful dequant-ready waits guard its PV commit of that use. -/
theorem guard_pv_issue {cta issuer j i tag : Nat} {slot : Fin 2} {sp : TcCommit.Spec}
    {rank : Fin 16} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (he : X.get (issuer, i) = some ⟨tag, .tc (.commit sp)⟩)
    (htgt : TcCommit.target sp rank = some (empty L cta slot))
    (hj : j ≤ ((X.tr issuer).take i).countP (commitsTo (empty L cta slot))) :
    Resumes kernel X (issuer, Poll.nth X (full L cta slot) issuer j) (issuer, i) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hc, d, hb, hd, hst⟩ :=
    actual_notification hpre hX (fun _ hg => Machine.code_sound hpre hg) he rfl htgt
  have hd : d.site = .pvCommit := by
    rcases hd with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · exact h
  have trace := (hs issuer hg).produces (hX.thr issuer hg)
  have hp := Wg1MmaGemmTrace.composed_count_here hpre hg .dequant trace hst hb
  have ha := Wg1MmaGemmTrace.composed_count_here hpre hg .pv trace hst hb
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ha
  simp only [hd, Wg1MmaGemmTrace.completed, ↓reduceIte] at hp
  change PTX.Flow.okPolls (full L (ctaOf L issuer) slot) ((X.tr issuer).take i) = _ at hp
  change ((X.tr issuer).take i).countP (commitsTo (empty L (ctaOf L issuer) slot)) = _ at ha
  rw [hc] at hp ha
  rw [ha] at hj
  have hcount : j + 1 ≤ PTX.Flow.okPolls (full L cta slot) ((X.tr issuer).take i) := by
    omega
  exact Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw)
    (PTX.len_of_get he) hcount

/-- The PV guard for a notification already present in the counted ring. -/
theorem guard_pv {cta issuer j : Nat} {slot : Fin 2} {y : Fin 1 × Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hy : y ∈ Notify.S X (empty L cta slot) issuer (empty L cta slot)) (hj : j ≤ y.2) :
    Resumes kernel X (issuer, Poll.nth X (full L cta slot) issuer j)
      (issuer, Notify.cm X issuer (empty L cta slot) y.2) := by
  let E := reuse_obj (slot := slot) hpre hX hs hmma
  obtain ⟨_, _, _, he, _, htgt, hu⟩ := E.S_rec hy
  exact guard_pv_issue hpre hX hs he htgt (hu.symm ▸ hj)

/-- A PV commit issues the counted completion notification. -/
theorem issue_pv {cta issuer : Nat} {slot : Fin 2} {y : Fin 1 × Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hy : y ∈ Notify.S X (empty L cta slot) issuer (empty L cta slot)) :
    Relation.ReflTransGen (DepStep L kernel X)
      (.thread (issuer, Notify.cm X issuer (empty L cta slot) y.2), false)
      (Notify.it X (empty L cta slot) issuer (empty L cta slot) y.2, false) := by
  let E := reuse_obj (slot := slot) hpre hX hs hmma
  obtain ⟨⟨k, r, hr, hid, _, _⟩, _, sp, he, _, htarget, _⟩ := E.S_rec hy
  have hp := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hid] at hp
  exact .single (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))

/-- One tile slot has 128 dequantizer publications and one MMA completion per generation. -/
def dequantRing {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) :
    Items.Ring L kernel Assumptions.all X 128 1 1 (fun _ => 128) where
  owner _ := 0
  ownF _ k := k
  wE a n := (producer L cta a, Poll.nth X (empty L cta slot) (producer L cta a) n)
  opF _ := Unit.it X (full L cta slot) (producer L cta)
  itF _ a u := .thread (Unit.it X (full L cta slot) (producer L cta) a u)
  wF _ n := (issuer, Poll.nth X (full L cta slot) issuer n)
  cm _ u := (issuer, Notify.cm X issuer (empty L cta slot) u)
  note _ _ := Notify.it X (empty L cta slot) issuer (empty L cta slot)
  SF _ := Unit.S X (full L cta slot) (producer L cta)
  phF _ := Unit.ph X (full L cta slot) (producer L cta)
  SE _ := Notify.S X (empty L cta slot) issuer (empty L cta slot)
  phE _ := Notify.ph X (empty L cta slot) issuer (empty L cta slot)
  oF _ n := Unit.obsOf X (full L cta slot) issuer n
  oE a n := Unit.obsOf X (empty L cta slot) (producer L cta a) n
  cover _ a := ⟨a, rfl⟩
  guardP _ _ hx _ _ hn := guard_ready hpre hX hs hx hn
  issueF _ _ _ := .refl
  guardM _ _ hy _ hj := guard_pv hpre hX hs hmma hy hj
  issue _ _ hy := issue_pv hpre hX hs hmma hy
  obsF _ _ hw _ hx hph :=
    (dequant_obj hpre hX hs).observed hX (Nat.zero_le _) (Poll.nth_present.mp hw) hx hph
  obsE a _ hn hw _ hy hph :=
    (reuse_obj hpre hX hs hmma).observed hX hn (Poll.nth_present.mp hw) hy hph
      (producer_wg2 hpre cta a)
  fullF _ _ hw :=
    (dequant_obj hpre hX hs).card_phase hX (Nat.zero_le _) (Poll.nth_present.mp hw)
  fullE a _ hn hw :=
    (reuse_obj hpre hX hs hmma).card_phase hX hn (Poll.nth_present.mp hw)
      (producer_wg2 hpre cta a)
  ltF _ _ _ hj hw := by
    have hcount := Poll.nth_present.mp hw
    let F := dequant_obj hpre hX hs (cta := cta) (slot := slot)
    exact ⟨Poll.nth_present.mpr (Nat.lt_trans hj hcount),
      Poll.observed_lt hX (by decide) (F.pclean hX) F.noInval (F.alt hX _)
        (Nat.zero_le _) hj hcount⟩
  ltE a _ _ hn hj hw := by
    have hcount := Poll.nth_present.mp hw
    let E := reuse_obj hpre hX hs hmma (slot := slot)
    exact ⟨Poll.nth_present.mpr (Nat.lt_trans hj hcount),
      Poll.observed_lt hX (le_refl 1) (E.pclean hX) E.noInval (E.alt hX _ (producer_wg2 hpre cta a))
        hn hj hcount⟩


/-- A dequantizer reusing this slot observes the previous PV completion notification. -/
theorem acquire_reuse {cta issuer j tag parity u : Nat} {slot : Fin 2} {sc : MbarScope}
    {lane : Fin 128} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (he : X.get (producer L cta lane, j) = some ⟨tag, .wait (empty L cta slot) parity true true sc⟩)
    (hu : PTX.Flow.okPolls (empty L cta slot) ((X.tr (producer L cta lane)).take j) = u + 1) :
    Witness L X (Notify.it X (empty L cta slot) issuer (empty L cta slot) u)
      (producer L cta lane, j) := by
  let R := dequantRing (slot := slot) hpre hX hs hmma
  have hj : Poll.nth X (empty L cta slot) (producer L cta lane) (u + 1) = j := by
    rw [← hu]
    exact Poll.nth_eq he
  have hp : X.RefPresent (.thread (R.wE lane (u + 1))) := by
    change X.RefPresent (.thread (producer L cta lane,
      Poll.nth X (empty L cta slot) (producer L cta lane) (u + 1)))
    rw [hj]
    exact ⟨_, he⟩
  have hw := (R.observes_empty hX.depAcyclic hp 0).2
  change Witness L X (Notify.it X (empty L cta slot) issuer (empty L cta slot) u)
    (producer L cta lane, Poll.nth X (empty L cta slot) (producer L cta lane) (u + 1)) at hw
  rwa [hj] at hw

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
