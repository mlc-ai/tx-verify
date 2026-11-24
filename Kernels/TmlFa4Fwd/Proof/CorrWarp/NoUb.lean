-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Flow.GlueStep
import Kernels.TmlFa4Fwd.Proof.Correction.RefNext
import Kernels.TmlFa4Fwd.Proof.Common.DataStop
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Lib.WordAlign
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part122
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Common.LdWait
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Correction.Safe
import Kernels.TmlFa4Fwd.Proof.Correction.SafeSt
import Kernels.TmlFa4Fwd.Proof.Correction.SafeTm
import Kernels.TmlFa4Fwd.Proof.Correction.Shapes
import Kernels.TmlFa4Fwd.Proof.Correction.Steps
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Safe
import Kernels.TmlFa4Fwd.Proof.Lib.MemAl
import Lemmas.Kernel.NoUbFirstStop
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Lemmas.Flow.UbFree
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # No event of a correction warp is undefined behaviour

`Frame.noUb_of_first_stop` for the lanes of warps 8 to 11 (`noUb`), followed with `Ref` by
`good` given the data premise `DataSrc`.

`safe` (`fired_safe`): every undefined-behaviour alternative of the shape table is excluded at a
role state under the reference values. The scheduler's and the request's reads address the
output warp's cuQ words (`Epilogue.rd_aligned` on the reference values' output-warp state) and the
chosen request's used-K word, 4-aligned; the statistics reads the row's statistics word
`sb + 4 row` plus a multiple of 4 (`al_tac`); the rescale loads' implicit waits are selected by the
kernel's `tcLdDataflow` assumption; the closing arrival, the store waits, the Tensor Memory loads
and stores, the final shared stores and the LSE stores by `Correction/Safe*.lean`.

`live` (`next_none`): the role machine dies only on an event of another kind than its site's,
which the shapes exclude, at the exit, at a read whose bytes do not rebuild, which the reference's
expectations exclude (the launch words, and the statistics words by `DataSrc`), and at the first
pass's tile count when the coordinate divisions have no rule, which the scan's reference values
exclude as for the output warp (`Epilogue.tiles_next`, through `succ_scan`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

set_option maxHeartbeats 4000000 in
/-- **The scheduler's and the request's reads are no undefined behaviour** under the reference
values: their addresses are 4-aligned. -/
theorem rd_safe (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : CFits p L g d ns nv) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) (f : Fault) :
    e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨k, hs⟩ | hs | hs | hs
  · have hal := Epilogue.rd_aligned hp hFE (.inl ⟨k, by simp only [hs, epi]⟩)
    obtain ⟨site, v, kk⟩ := d
    simp only at hs
    subst hs
    cases k <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (hreg _ (by lit_mem)) ?_ f hu
      exact hal
  · have hal := Epilogue.rd_aligned hp hFE (.inr (.inl (by simp only [hs, epi])))
    obtain ⟨site, v, kk⟩ := d
    simp only at hs
    subst hs
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (hreg _ (by lit_mem)) ?_ f hu
    exact hal
  · have hal := Epilogue.rd_aligned hp hFE (.inr (.inr (by simp only [hs, epi])))
    obtain ⟨site, v, kk⟩ := d
    simp only at hs
    subst hs
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (hreg _ (by lit_mem)) ?_ f hu
    exact hal
  · have hb := Epilogue.batch_lt hp
    have huk := hp.alignment.2.2.2.2.2.2.2.2.2.1
    have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
      hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
    simp only [Epilogue.Fits, toE, hs, epi] at hFE
    obtain ⟨R, bal, hC, -, -⟩ := hFE
    obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
    obtain ⟨site, v, kk⟩ := d
    simp only at hs hi
    subst hs
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine ldGlobal_ok' rfl rfl rfl rfl rfl rfl (by decide) (hreg _ (by lit_mem)) ?_ f hu
    show (truncBits 64 (Epilogue.vbits (Epilogue.addrS p.usedKBase (chosen v.sc))) +
      BitVec.ofInt 64 0).toNat % 4 = 0
    rw [hi, Mma.addrK_toNat hp hroom (by omega)]
    omega

/-- The row's statistics word `sb + 4 row` is 4-aligned. -/
theorem al_statW (hp : Pre p L m) : Al 2 (statW L g) := by
  have hsb : Al 2 (Mma.sbW L) := by
    have h := hp.shared.1
    have h2 := hp.shared.2.1
    unfold Al
    simp only [Mma.sbW, BitVec.toNat_ofNat]
    omega
  simp only [statW]
  al_tac

set_option maxHeartbeats 4000000 in
/-- **The statistics reads are no undefined behaviour**: the row's statistics word plus a
multiple of 4. -/
theorem stat_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g).AtD d t)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ st, d.site = .rscale st) ∨ (∃ st, d.site = .fsum st) ∨ ∃ st, d.site = .fmax st)
    (f : Fault) : e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hal := al_statW (g := g) hp
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, kk⟩ := d
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨st, rfl⟩ | ⟨st, rfl⟩ | ⟨st, rfl⟩ <;> fin_cases st <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact ldShared_ok (n := 4) rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      (hreg _ (by lit_mem)) hal (by decide) f hu

set_option maxHeartbeats 4000000 in
/-- **The rescale loads' implicit waits are no undefined behaviour**: the kernel's
`tcLdDataflow` assumption selects them (`tcLd_wait_ok`). -/
theorem rldw_safe {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g).AtD d t) (hk1 : d.k = 1)
    (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∃ st c, d.site = .rldw st c) (f : Fault) : e.kind ≠ .ub f := by
  have hsub : t.sub ≠ 0 := by rw [h.2.1]; simp [hk1]
  have hpc : t.pc = d.site.pc := h.1
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, kk⟩ := d
  intro hk
  have hu := fires_ub hf hk
  obtain ⟨st, c, rfl⟩ := hs
  fin_cases st <;> fin_cases c <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact tcLd_wait_ok (by rw [hpc]; ld_wait) hsub f hu

set_option maxHeartbeats 4000000 in
/-- **No event a state of a correction warp fires under its reference invariant and values is
undefined behaviour.** -/
theorem fired_safe (hp : Pre p L m) (hg : g < L.threads) {d : D} {n : Cnt → Nat} {ns nv : Nat}
    (hJ : Correction.Ref p L g (d, n)) (hF : CFits p L g d ns nv) {e : Event} {o : Option TState}
    (hf : (code p L g).toMachine.Fired (some d) e o) (f : Fault) : e.kind ≠ .ub f := by
  have hev := (Code.Shape.fired (shape hp) (stepAt hp hg) hf).1
  obtain ⟨t, ins, h, hi, hc, hfi⟩ := Code.fired_tmpl (stepAt hp hg) hf
  obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := hJ
  have hsub := hQ.sub
  obtain ⟨s, v, k⟩ := d
  simp only at hsub
  cases s
  case word kk => exact rd_safe hp hF h hc hfi (.inl ⟨kk, rfl⟩) f
  case q0 => exact rd_safe hp hF h hc hfi (.inr (.inl rfl)) f
  case q1 => exact rd_safe hp hF h hc hfi (.inr (.inr (.inl rfl))) f
  case uk => exact rd_safe hp hF h hc hfi (.inr (.inr (.inr rfl))) f
  case rscale st => exact stat_safe hp h hc hfi (.inl ⟨st, rfl⟩) f
  case fsum st => exact stat_safe hp h hc hfi (.inr (.inl ⟨st, rfl⟩)) f
  case fmax st => exact stat_safe hp h hc hfi (.inr (.inr ⟨st, rfl⟩)) f
  case rld st c => exact ld_safe hp h hc hfi (.inl ⟨st, c, rfl⟩) f
  case fld st j => exact ld_safe hp h hc hfi (.inr ⟨st, j, rfl⟩) f
  case rst st c => exact st_safe hp h hc hfi ⟨st, c, rfl⟩ f
  case fst st j hh => exact fst_safe hp h hc hfi ⟨st, j, hh, rfl⟩ f
  case lse hh => exact lse_safe hp h (hsub rfl) hc hfi ⟨hh, rfl⟩ f
  case rldw st c => exact rldw_safe h (hsub rfl) hc hfi ⟨st, c, rfl⟩ f
  case barEnd l => exact misc_safe hp hc hfi (.inl ⟨l, rfl⟩) f
  case rwait st => exact misc_safe hp hc hfi (.inr ⟨st, rfl⟩) f
  all_goals
    intro hk
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    simp [Ev, Epilogue.Ev, Site.toE] at hev

set_option maxHeartbeats 4000000 in
/-- **The role machine dies only at the exit** on an event of its shape that is no undefined
behaviour and returns what the references say: the reads rebuild, and the first pass's tile count
is the reference one (the output warp's `tiles_next` on the scan state). -/
theorem next_none (hp : Pre p L m) (hg : g < L.threads) {d : D} {ns nv : Nat} {e : Event}
    (hF : CFits p L g d ns nv) (hE : CExpect p L g d ns e) (hD : ExpectD d e)
    (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f) (hn : (code p L g).next d e = none) :
    e.kind = .exit := by
  by_cases ht : d.site = .tiles false
  · exfalso
    have hs : d.site.sched = true := by rw [ht]; rfl
    have hn' : Epilogue.succ p L g (toE d) e = none := by
      change succ p L g d e = none at hn
      rw [succ_scan (ctaR_eq hp hg) hs] at hn
      simpa using hn
    obtain ⟨rv, -, -, hFE, -⟩ := hF
    obtain ⟨s, v, k⟩ := d
    simp only at ht
    subst ht
    have hE' : Epilogue.Expect p L g (toE ⟨.tiles false, v, k⟩) ns e := by
      simp only [CExpect] at hE
      exact hE rfl
    exact Epilogue.tiles_next hp hg rfl hFE hE' hev hn'
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kind⟩ := e
  change succ p L g ⟨s, v, k⟩ ⟨pc, kind⟩ = none at hn
  cases s
  case exit l => simpa [Ev] using hev
  case tiles l =>
    cases l
    · exact absurd rfl ht
    · simp only [Ev, Epilogue.Ev, Site.toE] at hev
      obtain ⟨_, _, hk⟩ := hev
      subst hk
      simp only [succ] at hn
      split at hn <;> simp at hn
  case word | q0 | q1 | uk =>
    all_goals simp only [Ev, rdOrUb] at hev
    all_goals rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    all_goals try exact absurd hk (hub f)
    all_goals subst hk
    all_goals obtain ⟨x, hx⟩ := hD a bs rfl
    all_goals simp [succ, hx, word32] at hn
  case fmax =>
    simp only [Ev, rdOrUb] at hev
    rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [ExpectD] at hD
      obtain ⟨x, ht, hx⟩ := hD a bs rfl
      simp [succ, hx, max32_ereal _ ⟨x, ht⟩] at hn
    · exact absurd hk (hub f)
  case rscale | fsum =>
    all_goals simp only [Ev, rdOrUb] at hev
    all_goals rcases hev with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    all_goals try exact absurd hk (hub f)
    all_goals subst hk
    all_goals simp only [ExpectD] at hD
    all_goals obtain ⟨x, hx⟩ := hD a bs rfl
    all_goals simp [succ, hx, real32, scale32_val] at hn
  all_goals simp only [Ev, Epilogue.Ev, Site.toE] at hev
  all_goals shape_destruct hev
  all_goals first
    | (simp [succ, word32] at hn; done)
    | (simp [succ, word32] at hn
       repeat' split at hn
       all_goals simp_all)

set_option maxHeartbeats 4000000 in
private theorem data_event {k d n e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some e)
    (hs : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction,d⟩,n))) :
    ∃ o, (code p L g).toMachine.Fired (some d) e o := by
  obtain ⟨o, hf⟩ := (Frame.trace (fun _ hg => threadD_sound hp hg) hX
    (Frame.lt_of_get hX he)).fired_at he hs
  exact ⟨o,hf⟩

private theorem data_expect {k d n e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hData : d.site.data = true → ExpectD d e)
    (hw8 : 8 ≤ w ∧ w ≤ 11) (hw : Prologue.warpIndex L g = w)
    (he : X.get (g,k) = some e)
    (hs : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction,d⟩,n)))
    (hJ : Correction.Ref p L g (d,rc n)) :
    CExpect p L g d (n .shfl) e ∧ ExpectD d e ∧ (∀ f, e.kind ≠ .ub f) := by
  have hg := Frame.lt_of_get hX he
  have hc := control_of_data hp hs
  obtain ⟨hj,hF⟩ := (good hp hX hw8 hg hw k).2 _ hc (ub_zero hX he hc)
  obtain ⟨o,hf⟩ := data_event hp hX he hs
  have hu := fired_safe hp hg hJ hF hf
  have hE := (cexpect hp hX (cuQReadsFromLaunch hp hX) hg hw he hc hj hF hu
    (fun _ h j hin _ => good hp hX hw8 hin.1 hin.2 j)).1
  exact ⟨hE,expectD_of hF hE hData,hu⟩

/-- The data reads of a correction lane before position `K` return what its data machine follows. -/
def DataTo (p : Params) (L : Launch) (X : Execution) (g K : Nat) : Prop :=
  ∀ i < K, ∀ d n e, X.get (g, i) = some e →
    Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨.correction,d⟩,n)) →
    Correction.Ref p L g (d, rc n) → d.site.data = true → ExpectD d e

/-- Induction is restricted to live value states. The positivity clauses enter at the
dispatch and are maintained by successful statistics reads before the first stop. -/
private theorem data_ref_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw8 : 8 ≤ w ∧ w ≤ 11) (hw : Prologue.warpIndex L g = w)
    {k : Nat} (hData : DataTo p L X g k) {d n e} (he : X.get (g,k) = some e)
    (hs : Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction,d⟩,n))) :
    Correction.Ref p L g (d,rc n) := by
  induction k generalizing d n e with
  | zero => rw [Frame.stateAt_zero] at hs; cases hs
  | succ k ih =>
    have hc := control_of_data hp hs
    have hg := Frame.lt_of_get hX he
    obtain ⟨hctl,_⟩ := (good hp hX hw8 hg hw (k+1)).2 _ hc (ub_zero hX he hc)
    have hlen : k < (X.tr g).length := by
      obtain ⟨h,_⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[k+1]? = some e from he)
      omega
    let ev := (X.tr g)[k]'hlen
    have hev : (X.tr g)[k]? = some ev := List.getElem?_eq_getElem _
    rw [Frame.stateAt_succ hev] at hs
    obtain ⟨o,ho,hn⟩ := Option.bind_eq_some_iff.mp hs
    cases o with
    | none => cases hn
    | some s =>
      obtain ⟨s,n0⟩ := s
      obtain ⟨hn,rfl⟩ := Code.counted_next_some (C := gluedD p L g) hn
      cases s with
      | inl s =>
        obtain ⟨s',hstep,henter⟩ := Code.glue_inl_some hn
        unfold Code.enter at henter
        split at henter <;> cases henter
        exact ⟨hctl.counts, fun st _ => by fin_cases st <;> exact le_refl (0 : ℝ)⟩
      | inr a =>
        obtain ⟨i,d0⟩ := a
        obtain ⟨d',hstep,hd⟩ := Code.glue_inr_some hn
        cases hd
        have hJ := ih (fun i hi => hData i (by omega)) hev ho
        obtain ⟨_,hx,hu⟩ := data_expect hp hX
          (hData k (Nat.lt_succ_self k) _ _ _ hev ho hJ) hw8 hw hev ho hJ
        obtain ⟨_,hf⟩ := data_event hp hX hev ho
        have hshape := (Code.Shape.fired (shape hp) (stepAt hp hg) hf).1
        exact (Correction.ref_next hJ hx hshape hu).2 _
          ((Code.counted_next _ _ _).trans (by rw [hstep]; rfl))

/-- **No event of a lane of a correction warp is undefined behaviour**, given the lane's data
reads. -/
theorem noUb_of_data (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw8 : 8 ≤ w ∧ w ≤ 11) {g : Nat} (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) (hData : ∀ K, DataTo p L X g K) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e)
    (f : Fault) : e.kind ≠ .ub f := by
  have followed := good hp hX hw8 hg hw
  have safe : ∀ i σ v, X.get (g,i) = some v →
      Frame.stateAt (threadD p L) X g i = some (some σ) → ∀ f, v.kind ≠ .ub f := by
    intro i ⟨σ,n⟩ v hi hs f
    have hc := control_of_data hp hs
    have hR := (followed i).2 _ hc
    cases σ with
    | inl s => exact start_safe hp hX hi hc hR.1 f
    | inr a =>
      obtain ⟨i',d⟩ := a
      cases i' with
      | correction =>
        have hJ := data_ref_at hp hX hw8 hw (hData _) hi hs
        exact (data_expect hp hX (hData _ i i.lt_succ_self _ _ _ hi hs hJ)
        hw8 hw hi hs hJ).2.2 f
      | _ => exact hR.elim
  refine Frame.noUb_of_first_stop (C := threadD p L) hX safe ?_ he f
  intro i ⟨σ,n⟩ v hi hs _ loss
  have hc := control_of_data hp hs
  have hR := (followed i).2 _ hc
  cases σ with
  | inl s =>
    exact start_live hp hX hi hc hR.1
      (Frame.next_none_of_stop hi hc (data_start_stop loss) (followed (i+1)).1)
  | inr a =>
    obtain ⟨i',d⟩ := a
    cases i' with
    | correction =>
      have hJ := data_ref_at hp hX hw8 hw (hData _) hi hs
      obtain ⟨hCE,hE,hu⟩ := data_expect hp hX (hData _ i i.lt_succ_self _ _ _ hi hs hJ)
        hw8 hw hi hs hJ
      obtain ⟨_,hf⟩ := data_event hp hX hi hs
      have hev := (Code.Shape.fired (shape hp) (stepAt hp hg) hf).1
      rcases data_role_stop loss with hn | hn
      · exact next_none (d := d) hp hg (hR (ub_zero hX hi hc)).2 hCE hE hev hu hn
      · exact (Correction.not_stop hJ hE hn).elim
    | _ => exact hR.elim

/-- **No event of a lane of a correction warp is undefined behaviour**, given the data premise. -/
theorem noUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hData : DataSrc p L X) (hw8 : 8 ≤ w ∧ w ≤ 11) {g : Nat} (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (f : Fault) : e.kind ≠ .ub f :=
  noUb_of_data hp hX hw8 hg hw (fun _ i _ => hData g i) he f

/-- **A correction lane's data machine is alive**, with its reference invariant, up to a position,
once its data reads before it returned what the machine follows. -/
theorem alive (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw8 : 8 ≤ w ∧ w ≤ 11) {g : Nat} (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) {K : Nat} (hData : DataTo p L X g K) :
    ∀ k ≤ K, k < (X.tr g).length → ∃ σ, Frame.stateAt (threadD p L) X g k = some (some σ) ∧
      ∀ d n, σ = (.inr ⟨.correction, d⟩, n) → Correction.Ref p L g (d, rc n) := by
  have followed := good hp hX hw8 hg hw
  intro k
  induction k with
  | zero =>
    intro _ hlen
    refine ⟨_, Frame.stateAt_zero, fun d n h => ?_⟩
    cases h
  | succ k ih =>
    intro hkK hlen
    obtain ⟨⟨σ, n⟩, hs, -⟩ := ih (by omega) (by omega)
    obtain ⟨v, hi⟩ : ∃ v, X.get (g, k) = some v :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
    by_cases hok : ∃ σ, Frame.stateAt (threadD p L) X g (k + 1) = some (some σ)
    · obtain ⟨σ', h'⟩ := hok
      obtain ⟨v', hi'⟩ : ∃ v', X.get (g, k + 1) = some v' := ⟨_, List.getElem?_eq_getElem hlen⟩
      refine ⟨σ', h', fun d n hd => ?_⟩
      subst hd
      exact data_ref_at hp hX hw8 hw (fun i hi => hData i (by omega)) hi' h'
    exfalso
    have loss : (threadD p L g).next (σ, n) v = none ∨
        (threadD p L g).next (σ, n) v = some none := by
      have hst := Frame.stateAt_succ (C := threadD p L) (show (X.tr g)[k]? = some v from hi)
      rw [hs] at hst
      rcases h : (threadD p L g).next (σ, n) v with _ | _ | b
      · exact .inl rfl
      · exact .inr rfl
      · exact (hok ⟨b, hst.trans h⟩).elim
    have hx : v.kind = .exit := by
      have hc := control_of_data hp hs
      have hR := (followed k).2 _ hc
      cases σ with
      | inl s =>
        exact start_live hp hX hi hc hR.1
          (Frame.next_none_of_stop hi hc (data_start_stop loss) (followed (k+1)).1)
      | inr a =>
        obtain ⟨i',d⟩ := a
        cases i' with
        | correction =>
          have hJ := data_ref_at hp hX hw8 hw (fun i hi => hData i (by omega)) hi hs
          obtain ⟨hCE,hE,hu⟩ := data_expect hp hX (hData k (by omega) _ _ _ hi hs hJ) hw8 hw hi hs
              hJ
          obtain ⟨_,hf⟩ := data_event hp hX hi hs
          have hev := (Code.Shape.fired (shape hp) (stepAt hp hg) hf).1
          rcases data_role_stop loss with hn | hn
          · exact next_none (d := d) hp hg (hR (ub_zero hX hi hc)).2 hCE hE hev hu hn
          · exact (Correction.not_stop hJ hE hn).elim
        | _ => exact hR.elim
    obtain ⟨pc, kd⟩ := v
    simp only at hx
    subst hx
    obtain ⟨r, hr⟩ := hX.thr g hg
    have := Flow.Run.end_last hr hi (.inr rfl)
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
