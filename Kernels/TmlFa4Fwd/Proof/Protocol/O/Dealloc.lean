-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Base
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemAccess
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Lib.BarUpTo
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.DeallocHand
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.MmaDealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Done
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every MMA is done before the deallocation (`Tmem1.MmaDoneDealloc`)

A correction lane of the deallocating CTA arrives at barrier 2's second rendezvous, and its events
before that arrival precede the deallocation (`dealloc_arrival`). An MMA means the CTA picked a
tile (`mma_picked`: the pipeline's states hold the first pass's choice), so that arrival is the
lane's `barEnd true` (`barEnd false` follows a first pass without a tile: `noPicked_exit`), where
the lane has made one successful poll of the final O barrier of stage 0 (`RefQ.cnt`). That poll
observes the MMA's completion (`mma_observed`): `mma_done`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

set_option maxHeartbeats 8000000 in
/-- **A lane of warps 0 to 11 of a deallocating CTA arrives at barrier 2's second rendezvous,
and its events before that arrival precede the deallocation.** -/
theorem dealloc_arrival {z j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da nn : Nat}
    (hd : X.get (z, j) = some ⟨pc, .tc (.resource grp dst (.dealloc da nn))⟩) {h : Nat}
    (hh : h < L.threads) (hcta : z / L.block = h / L.block) (hw : Prologue.warpIndex L h < 12) :
    ∃ i pci mi, X.get (h, i) = some ⟨pci, .bar 2 (some 416) mi⟩ ∧
      ((X.tr h).take i).countP (Execution.isBarId 2) = 1 ∧
      ∀ w, w < i → baseCausality L X (h, w) (z, j) :=
  dealloc_ord1 hp hX hFw hd hh hcta hw

omit hp hFw in
/-- The MMA warp's pipeline states hold the first pass's choice: the CTA picked a tile. -/
theorem mma_picked {k : Nat} {d : Mma.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)))
    (hJ : JR p L g (Mma.minj p L g d n))
    (hs : (∃ b j, d.site = .qk b j) ∨ ∃ b j, d.site = .pv b j) :
    ∃ R bal, Epilogue.Picked p L g R bal := by
  have hR : Mma.Ref p L g (Mma.minj p L g d n) := by
    rw [JR_eq] at hJ; unfold RefAll at hJ
    split_ifs at hJ <;> first
      | exact hJ
      | simp [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ
  obtain ⟨-, hF⟩ := hR (ub_zero hX he hσ)
  obtain ⟨site, v⟩ := d
  rcases hs with ⟨b, j, hs⟩ | ⟨b, j, hs⟩ <;> simp only at hs <;> subst hs <;>
    simp only [Mma.MFits, Mma.Site.early, Bool.false_eq_true, ite_false] at hF <;>
    obtain ⟨-, hFE, -⟩ := hF <;>
    simp only [Epilogue.Fits, Mma.toE, Mma.Site.epi] at hFE <;>
    obtain ⟨R, bal, hC, -⟩ := hFE <;>
    exact ⟨R, bal, hC.1⟩

omit hp hX hFw in
theorem acq144_barEnd (l : Bool) (r : Nat) :
    Correction.passed (Correction.ptsOf (.acquire 144)) (.barEnd l) r = if l then 1 else 0 := by
  have h : ∀ l : Bool, (Correction.ptsOf (.acquire 144)).countP
      (Correction.before (.barEnd l)) = (if l then 1 else 0) ∧
      (Correction.ptsOf (.acquire 144)).countP Correction.inRound = 0 := by decide +kernel
  obtain ⟨h1, h2⟩ := h l
  simp only [Correction.passed, h1, h2, Nat.mul_zero, Nat.add_zero]

set_option maxHeartbeats 8000000 in
/-- **A correction lane's second barrier-2 arrival in a CTA with a tile follows its successful
poll of the final O barrier of stage 0.** -/
theorem corr_arrival_poll {h i pci : Nat} {mi : BarMode}
    (hi : X.get (h, i) = some ⟨pci, .bar 2 (some 416) mi⟩)
    (hc1 : ((X.tr h).take i).countP (Execution.isBarId 2) = 1)
    (hw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11)
    {R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L h R bal) :
    ∃ k, k < i ∧ ∃ pc par acq sc,
      X.get (h, k) = some ⟨pc, .wait (Correction.bl L h 144) par true acq sc⟩ := by
  obtain ⟨⟨σ1, n⟩, hσ, hJ, -, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hi (by intro f hf; cases hf)
  have hR := jr_corrRef hJ hw
  have hub0 := ub_zero hX hi hσ
  rcases σ1 with s | ⟨role, d⟩
  · have := start_barOps hJ hev
    simp at this
  cases role
  case correction =>
    obtain ⟨hRc, hF⟩ := hR hub0
    obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := hRc
    have hev1 := hev.1.data_or_vote.resolve_right (by rintro ⟨_, _, h⟩; cases h)
    have hc2 : CorrWarp.rc n Correction.Cnt.bar2 = 1 := by
      rw [← hc1, ← cls_corr_bar2 (L := L) (g := h), count hσ]
    obtain ⟨site, v, kk⟩ := d
    have hq2 := hQ.cnt .bar2 (by decide)
    -- the site is `barEnd l`
    obtain ⟨l, rfl⟩ : ∃ l, site = .barEnd l := by
      cases site
      case barEnd l => exact ⟨l, rfl⟩
      case bar1 =>
        exfalso
        have h0 : (Correction.ptsOf .bar2).countP (Correction.before .bar1) = 0 ∧
            (Correction.ptsOf .bar2).countP Correction.inRound = 0 := by decide +kernel
        have hq2' : CorrWarp.rc n .bar2 =
            Correction.passed (Correction.ptsOf .bar2) .bar1 r := hq2
        rw [hc2] at hq2'
        simp only [Correction.passed, h0.1, h0.2, Nat.mul_zero] at hq2'
        omega
      all_goals exfalso
      all_goals simp only [Correction.Control.D.scheduler, Correction.Ev] at hev1
      all_goals (try exact (epi_nobar ‹Epilogue.Ev _ _ _ _ _› 2 (some 416) mi rfl))
      all_goals (try split at hev1)
      all_goals shape_destruct hev1
      all_goals (try subst_vars)
      all_goals simp_all [Correction.rdOrUb]
      all_goals (try exact corr_nbW_ne2 _ (by omega))
    -- with a tile, the lane's barrier-2 arrival is its `barEnd true`
    cases l
    · exfalso
      obtain ⟨rv, -, -, hFE, -⟩ := hF
      exact noPicked_exit hFE rfl ⟨R, bal, hP⟩
    -- its successful poll of the stage-0 final barrier
    have hq := hQ.cnt (.acquire 144) (by decide)
    have hq' : CorrWarp.rc n (.acquire 144) =
        Correction.passed (Correction.ptsOf (.acquire 144)) (.barEnd true) r := hq
    rw [acq144_barEnd] at hq'
    have hcnt : ((X.tr h).take i).countP (Proof.cls L h (.corr (.acquire 144))) = 1 := by
      rw [count hσ]; exact hq'
    obtain ⟨e, hmem, hce⟩ := List.countP_pos_iff.mp (show 0 < _ by rw [hcnt]; omega)
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    simp only [List.length_take] at hk
    have hgk : X.get (h, k) = some e := by
      have h1 : ((X.tr h).take i)[k]? = some e := by rw [← hget]; exact List.getElem?_eq_getElem _
      rw [List.getElem?_take, ite_eq_left (by omega)] at h1
      exact h1
    obtain ⟨pc, kind⟩ := e
    cases kind
    case wait mm par ok acq sc =>
      cases ok
      · simp [Proof.cls, Correction.cls] at hce
      · simp only [Proof.cls, Correction.cls, decide_eq_true_eq] at hce
        subst hce
        exact ⟨k, by omega, pc, par, acq, sc, hgk⟩
    all_goals simp_all [Proof.cls, Correction.cls]
  all_goals simp [CorrWarp.Ref] at hR

set_option maxHeartbeats 8000000 in
/-- **The observer of an MMA**: a correction lane's poll of its CTA's final commit, before a
deallocation of its CTA. -/
theorem mma_observer {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (hi : Tmem1.IsMma X i) (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩)
    (hcd : d.1 / L.block = i.1 / L.block) :
    ∃ h k pck l par, h < L.threads ∧ h / L.block = i.1 / L.block ∧
      X.get (h, k) = some ⟨pck, .wait l par true true .cta⟩ ∧
      AsyncCopy.AsyncObserved X i .mmaDone (h, k) true .cta ∧
      baseCausality L X (h, k) d := by
  have hb := hp.block
  obtain ⟨zi, fi⟩ := i
  obtain ⟨z, j⟩ := d
  obtain ⟨dd, sp, accm, mask, pci, hei⟩ := hi
  have hzi := Frame.lt_of_get hX hei
  -- the CTA picked a tile
  obtain ⟨di, ni, hσi, hJi, -⟩ := mma_issue_state hp hX hFw hei
  have hsite := mma_issue_site (k := .tc (.mma dd sp accm mask)) trivial
    (Mma.mfired hp hX hei hσi).1
  obtain ⟨R, bal, hP⟩ := mma_picked hX hei hσi hJi hsite
  -- the CTA's first correction lane
  have hh : (zi / L.block) * L.block + 256 < L.threads := by
    show _ < L.grid * L.block
    have : zi < L.grid * L.block := hzi
    rw [hb] at this ⊢
    omega
  have hch : ((zi / L.block) * L.block + 256) / L.block = zi / L.block := by rw [hb]; omega
  have hw8 : Prologue.warpIndex L ((zi / L.block) * L.block + 256) = 8 := by
    show _ % L.block / 32 = 8
    rw [hb]; omega
  have hP' := Epilogue.Picked.cta hch.symm hP
  obtain ⟨i', pci', mi, hi', hc1, Hc⟩ := dealloc_arrival hp hX hFw hd hh
    (by simp only at hcd; rw [hcd, hch]) (by omega)
  obtain ⟨k, hk, pck, par, acq, sc, hgk⟩ :=
    corr_arrival_poll hp hX hFw hi' hc1 (by omega) hP'
  -- the poll is of the CTA's final O barrier of stage 0, with parity 0
  have hloc : Correction.bl L ((zi / L.block) * L.block + 256) 144 = obj L zi (oOff 0) := by
    simp only [Correction.bl, obj, hch]; rfl
  rw [hloc] at hgk
  obtain ⟨σ, -, -, -, h2⟩ := o_event hp hX hFw (g := zi) hgk rfl
    (by intro c h; cases h)
  rcases h2 with ⟨d', n', s', -, -, hk'⟩ | ⟨d', n', ok, -, -, hk'⟩
  · cases hk'
  simp only [Kind.wait.injEq] at hk'
  obtain ⟨-, rfl, -, rfl, rfl⟩ := hk'
  have hobs := mma_observed hp hX hFw ⟨dd, sp, accm, mask, pci, hei⟩ hgk
  exact ⟨_, k, pck, _, _, hh, hch, hgk, hobs, Hc k hk⟩

/-- **`Tmem1.MmaDoneDealloc`**: every MMA is done, by its CTA's final commit observed by a
correction lane's poll, before every deallocation of its CTA. -/
theorem mma_done : Tmem1.MmaDoneDealloc L X := by
  intro i d pc a n grp dst hi hd hcd
  obtain ⟨h, k, pck, l, par, hh, hch, -, hobs, hb⟩ := mma_observer hp hX hFw hi hd hcd
  obtain ⟨_, _, _, _, _, hei⟩ := id hi
  have hzi : i.1 < L.threads := Frame.lt_of_get hX hei
  exact .inl ⟨_, .cta, hobs, ⟨⟨hzi, hh, by rw [hch]⟩, ⟨hh, hzi, hch⟩⟩, hb⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
