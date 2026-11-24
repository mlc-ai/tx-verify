-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Data.AsyncTypes
public import Core.Data.Types
public import Core.Data.Value
public import Core.Isa.Tc
public import Core.Source.Instr
public import Core.Tc.TcMmaLifetime
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.FmaRun
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.CorrLdWait
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.DeallocHand
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.PendNoBar
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Lemmas.Kernel.UbLast
import Kernels.TmlFa4Fwd.Proof.Top.Register

@[expose] public section

/-! # Every load and store is waited on before the deallocation (`Life.ldst_before_dealloc`)

A `tcgen05.ld` or `tcgen05.st` is a softmax or correction lane's, made after one barrier-2 event
of the lane, so the lane arrives at barrier 2 again at some `i` after it and every event of the
lane before `i` precedes the deallocation (`dealloc_handoff`). Between the access and `i` the lane
makes the access's wait: a correction load's next event (`corr_ld_wait`); for a correction store,
a softmax store or a softmax load, the lane's states from the access stay in the access's region
until a wait or undefined behaviour (`corr_st_pend`, `soft_st_pend`, `soft_ld_pend`), undefined
behaviour is the lane's last event (`ub_last`), and the region fires no barrier-2 event
(`stp_nobar`, `pstp_nobar`, `ldp_nobar`), so the region is left before `i` by its wait
(`ldst_dealloc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

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

set_option maxHeartbeats 16000000 in
/-- **A load or store has its wait before every deallocation of its CTA.** -/
theorem ldst_wait {z j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da nn : Nat}
    (hd : X.get (z, j) = some ⟨pc, .tc (.resource grp dst (.dealloc da nn))⟩) {h f pcf : Nat}
    {k : Kind} (he : X.get (h, f) = some ⟨pcf, k⟩) (hcta : z / L.block = h / L.block)
    {wk : TcKind} (hk : (∃ a vals sh, k = .tc (.ld a vals sh) ∧ wk = .waitLd) ∨
      (∃ a vals sh, k = .tc (.st a vals sh) ∧ wk = .waitSt)) :
    TcMma.WaitBefore L X wk (h, f) (z, j) := by
  have hacc : IsAcc k := by
    rcases hk with ⟨a, vals, sh, rfl, -⟩ | ⟨a, vals, sh, rfl, -⟩ <;> trivial
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he (by rintro fl rfl; exact hacc)
  -- the lane is a softmax or correction lane
  have hcls : (∃ d, σ1 = .inr ⟨.softmax, d⟩) ∨ (∃ d, σ1 = .inr ⟨.correction, d⟩) := by
    rcases σ1 with s | ⟨i, d⟩
    · exact (start_noacc hJ hacc hev).elim
    cases i with
    | softmax => exact .inl ⟨d, rfl⟩
    | correction => exact .inr ⟨d, rfl⟩
    | epilogue => exact (epi_noacc hacc hev).elim
    | loader b => exact (ld_noacc hacc hev).elim
    | stub r =>
      exact (jr_stub hJ).elim
    | mma =>
      exfalso
      rcases d with s | ⟨⟨⟩, d⟩
      · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;>
          simp only at hk' <;> subst hk' <;> exact hacc
      · rcases hk with ⟨a, vals, sh, rfl, -⟩ | ⟨a, vals, sh, rfl, -⟩
        · exact mma_noldst (hev := hev) (by trivial)
        · exact mma_noldst (hev := hev) (by trivial)
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  -- the common end: a wait between the access and the lane's arrival
  have common : ∀ (hw : Prologue.warpIndex L h < 12)
      (hf1 : ((X.tr h).take f).countP (Execution.isBarId 2) = 1)
      (R : ∀ i, f < i → i < (X.tr h).length → ∀ σi, Frame.stateAt (thread p L) X h i =
        some (some σi) → (∀ pci mi, X.get (h, i) = some ⟨pci, .bar 2 (some 416) mi⟩ →
          TEv p L h σi ⟨pci, .bar 2 (some 416) mi⟩ →
          (∃ w, f < w ∧ w < i ∧ ∃ pcw, X.get (h, w) = some ⟨pcw, .tc wk⟩) ∨
          (∃ u, f < u ∧ u < i ∧ ∃ pcu fl, X.get (h, u) = some ⟨pcu, .ub fl⟩))),
      TcMma.WaitBefore L X wk (h, f) (z, j) := by
    intro hw hf1 R
    obtain ⟨i, pci, mi, hi', hci, hfi, Hc⟩ :=
      dealloc_handoff hp hX hFw hd he hacc hcta hw hf1
    have hilen : i < (X.tr h).length :=
      (List.getElem?_eq_some_iff.mp (show (X.tr h)[i]? = _ from hi')).1
    obtain ⟨σi, hσi, -, -, hevi⟩ := ev_at hp hX hT hF hi' (by intro f hf; cases hf)
    rcases R i hfi hilen σi hσi pci mi hi' hevi with
      ⟨w, hfw, hwi, pcw, hgw⟩ | ⟨u, h1, h2, pcu, fl, hu⟩
    · exact ⟨(h, w), ⟨pcw, hgw⟩, rfl, hfw, .inl (Hc w hwi)⟩
    · have := ub_last hX hu hi'
      omega
  rcases hcls with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · -- a softmax lane
    have h8 := jr_soft hJ
    refine common (by omega) (soft_tc_bar2 hp hX hFw he hσ (soft_acc hacc hev.1))
      fun i hfi hilen σi hσi pci mi hi' hevi => ?_
    rcases hk with ⟨a, vals, sh, rfl, rfl⟩ | ⟨a, vals, sh, rfl, rfl⟩
    · rcases soft_ld_site hev.1 with ⟨r0, c0, hs0⟩ | ⟨c0, hs0, hk0⟩
      · obtain ⟨s0, v0, k0, a0⟩ := d
        simp only [Softmax.Control.D.scheduler] at hs0
        subst hs0
        rcases soft_ld_pend hp hX hσ i hfi hilen.le σi hσi with
          h | h | ⟨d', n', rfl, hpd⟩
        · exact .inl h
        · exact .inr h
        · exact (ldp_nobar h8 hpd hevi.1).elim
      · exfalso
        have htr := (goodR hp hX hFw hg (f + 1)).1
        apply htr
        rw [Frame.stateAt_succ (show (X.tr h)[f]? = _ from he), hσ]
        show (thread p L h).next (SmWarp.sinj p L h d n) _ = some none
        rw [SmWarp.next_sinj]
        obtain ⟨s0, v0, k0, a0⟩ := d
        simp only [Softmax.Control.D.scheduler] at hs0 hk0
        subst hs0
        simp [Softmax.Control.succ, Softmax.Control.D.scheduler, Softmax.succ, hk0]
    · obtain ⟨r0, q0, hs0⟩ := soft_st_site hev.1
      obtain ⟨s0, v0, k0, a0⟩ := d
      simp only [Softmax.Control.D.scheduler] at hs0
      subst hs0
      rcases soft_st_pend hp hX hσ i hfi hilen.le σi hσi with
        h | h | ⟨d', n', rfl, hpd⟩
      · exact .inl h
      · exact .inr h
      · exact (pstp_nobar (d := d'.scheduler) hpd hevi.1).elim
  · -- a correction lane
    have hw := jr_corr hJ (Prologue.warpIndex_lt hp h)
    have hevc := hev.1.data_or_vote.resolve_right (by rintro ⟨_, _, rfl⟩; exact hacc)
    refine common (by omega) (corr_tc_bar2 hp hX hFw he hσ (corr_acc hacc hevc))
      fun i hfi hilen σi hσi pci mi hi' hevi => ?_
    rcases hk with ⟨a, vals, sh, rfl, rfl⟩ | ⟨a, vals, sh, rfl, rfl⟩
    · have hf1 : f + 1 < (X.tr h).length := by omega
      have he1 : X.get (h, f + 1) = some ((X.tr h)[f + 1]'hf1) := List.getElem?_eq_getElem hf1
      have hu : ∀ fl, ((X.tr h)[f+1]'hf1).kind ≠ .ub fl := by
        rcases Nat.eq_or_lt_of_le hfi with hi | hi
        · subst i
          rw [← Option.some.inj (hi'.symm.trans he1)]
          nofun
        · exact Frame.noUbBefore_of_get hX hi' _ hi _ he1
      have hw1 := corr_ld_wait hp hX hFw he hσ he1 hu
      have hne : f + 1 ≠ i := by
        rintro rfl
        rw [hi'] at he1
        simp only [Option.some.injEq] at he1
        rw [← he1] at hw1
        cases hw1
      refine .inl ⟨f + 1, by omega, by omega, ((X.tr h)[f + 1]'hf1).pc, ?_⟩
      rw [he1, ← hw1]
    · obtain ⟨st0, c0, hs0⟩ := corr_st_site hevc
      obtain ⟨s0, v0, k0⟩ := d
      simp only [Correction.Control.D.scheduler] at hs0
      subst hs0
      rcases corr_st_pend hp hX hσ i hfi hilen.le σi hσi with h | h | ⟨d', n', rfl, hpd⟩
      · exact .inl h
      · exact .inr h
      · exact (stp_nobar (d := d'.scheduler) hpd
        (hevi.1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h))).elim

/-- **`Life`'s second field**: every load and store of a CTA is waited on before every
deallocation of the CTA. -/
theorem ldst_dealloc {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {da n : Nat}
    (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩)
    (hc : d.1 / L.block = e.1 / L.block) :
    (X.TLd e a vals sh → TcMma.WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → TcMma.WaitBefore L X .waitSt e d) :=
  ⟨fun ⟨_, he⟩ => ldst_wait hp hX hFw hd he hc (.inl ⟨a, vals, sh, rfl, rfl⟩),
    fun ⟨_, he⟩ => ldst_wait hp hX hFw hd he hc (.inr ⟨a, vals, sh, rfl, rfl⟩)⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
