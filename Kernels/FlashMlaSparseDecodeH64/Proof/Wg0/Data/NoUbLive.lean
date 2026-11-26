-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PayEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ValidUpto
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepCondsOf
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StrictChain
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Lemmas.Flow.NotNc
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.StrictSite

@[expose] public section

/-! # The steps before a live event of warpgroup 0 are strict

`w0_wctx`: the context of a window (`WCtx`) at an event before a live event, from the valid prefix
(`w0_upto`), the data machine's invariants and the event's typed word; so the step into the next
state is strict (`w0_prev`, `stepConds_of`) and the next event fires from a strictly good state of
its site's template (`Frame.strict_site`). -/

/-! # Non-coherent reads of warpgroup 0 are at the three length and sink loads

`nc_site_pc`: an event of the template of a state at a site of warpgroup 0 that is a
non-coherent read is at the pc of the sink load or of one of the two length loads: the only
sites of warpgroup 0 among the kernel's `ncLoads`, and a template fires such a read only at
a site the assumption allows (`fires_not_nc`). -/

/-! # The payload registers of every site of a state of the data machine

`payAll_of`: at a state with the context of a window (`WCtx`: the data state's invariants, the
valid trace through the event, the words the block has loaded), the registers its facts name hold
the payload words the site's store, Tensor Memory store or vote reads (`PayAll`). The table of the
store instructions' registers is decided once (`needs_*`); the values are the sites' lemmas
(`pay_pst` to `pay_ost2`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- The registers an instruction reads for its payload and its predicate. -/
def needsPair (ins : Instr) : List (Nat × Nat) × List Nat := (needsOf ins, predNeeds ins)

theorem needs_pst : ∀ k < 8, (kernel.code[403 + 10 * k]?).map needsPair =
    some ([(4031 + k, 16)], []) := by decide +kernel

theorem needs_ost : ∀ k < 4, (kernel.code[704 + k]?).map needsPair =
    some ((List.range 4).map fun i => (1115 + 12 * k + 3 * i, 4), []) := by decide +kernel

theorem needs_rst : ∀ k < 4, (kernel.code[[814, 915, 1016, 1117].getD k 0]?).map needsPair =
    some ((List.range 64).map fun j => (1264 + 129 * k + j, 4), []) := by decide +kernel

theorem needs_ost2 : ∀ a : Fin 4, ∀ k < 8, (kernel.code[ost2Base a + k]?).map needsPair =
    some ((List.range 4).map fun i => (eStart a + 3 * (4 * k + i), 4), []) := by
  decide +kernel

theorem needs_mst : (kernel.code[566]?).map needsPair = some ([(1109, 4)], []) := by
  decide +kernel

theorem needs_vote : (kernel.code[578]?).map needsPair = some ([], [109]) := by decide +kernel

theorem needs_est : (kernel.code[1155]?).map needsPair = some ([(1727, 4)], []) := by
  decide +kernel

theorem needs_lse : (kernel.code[1178]?).map needsPair = some ([(1733, 4)], []) := by
  decide +kernel

/-- The payload from a table entry. -/
theorem pay_of_tbl {t : TState} {ins : Instr} {pc : Nat} {ns : List (Nat × Nat)} {ps : List Nat}
    (hc : kernel.code[pc]? = some ins) (ht : (kernel.code[pc]?).map needsPair = some (ns, ps))
    (h1 : ∀ r n, (r, n) ∈ ns → ∃ v, t.regs r = some v ∧ v.bytes = n)
    (h2 : ∀ r, r ∈ ps → ∃ p, t.regs r = some (.pred p)) : PayAll t ins := by
  rw [hc] at ht
  simp only [Option.map_some, Option.some.injEq, needsPair, Prod.mk.injEq] at ht
  exact payAll_of_needs (fun r n hm => h1 r n (by rw [← ht.1]; exact hm))
    (fun r hm => h2 r (by rw [← ht.2]; exact hm))

/-- **The payload registers of a site** hold what its store, Tensor Memory store or vote reads. -/
theorem payAll_of (c : WCtx L g sc l d e) {t : TState} {ins : Instr}
    (hF : Holds t.regs (dF L d)) (hc : kernel.code[d.c.site.pc]? = some ins) : PayAll t ins := by
  by_cases hp : paySite d.c.site = false
  · exact pay_of_free hp hc
  have hs : ∃ s, d.c.site = s := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := hs
  rw [hs] at hc hp
  cases s with
  | pst k =>
    refine pay_of_tbl hc (needs_pst k.val k.isLt) (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact pay_pst c k hs hF
  | mst =>
    refine pay_of_tbl hc needs_mst (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact pay_mst c hs hF
  | vote =>
    refine pay_of_tbl hc needs_vote (fun r n hm => by simp at hm) (fun r hm => ?_)
    simp only [List.mem_singleton] at hm
    subst hm
    exact pay_vote c hs hF
  | est =>
    refine pay_of_tbl hc needs_est (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact pay_est c hs hF
  | lse =>
    refine pay_of_tbl hc needs_lse (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact pay_lse c hs hF
  | ost k =>
    refine pay_of_tbl hc (needs_ost k.val k.isLt) (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨i, hi, rfl, rfl⟩ := hm
    exact pay_ost c k hs hF i hi
  | rst k =>
    refine pay_of_tbl hc (needs_rst k.val k.isLt) (fun r n hm => ?_) (fun r hm => by simp at hm)
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨j, hj, rfl, rfl⟩ := hm
    exact pay_rst c k hs hF j hj
  | ost2 a k =>
    refine pay_of_tbl hc (needs_ost2 a k.val k.isLt) (fun r n hm => ?_)
      (fun r hm => by simp at hm)
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
    obtain ⟨i, hi, rfl, rfl⟩ := hm
    exact pay_ost2 c a k hs hF i hi
  | _ => simp [paySite] at hp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

theorem nc_sites : ∀ s ∈ allSites, ncLoads.contains s.pc = true →
    s.pc = 156 ∨ s.pc = 168 ∨ s.pc = 181 := by
  decide +kernel

theorem nc_any (p : Nat) : Assumptions.all.any (·.ncLoads p) = ncLoads.contains p := by
  simp [Assumptions.all, Assumptions.ncReadOnly, Assumption.ncReadOnly, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.paramPointers, Assumptions.storeDrain,
    Assumptions.sharedBits, Assumptions.commitOrder, Assumptions.pvCommitOrderSites,
    Assumption.commitOrderAt]

/-- **A non-coherent read of a warpgroup-0 site** is at the sink or a length load. -/
theorem nc_site_pc {L : Launch} {g : Nat} {t : TState} {op : Op} {e : Event} {o : Option TState}
    {s : Site} (hpc : t.pc = s.pc) (hf : Fires s.pc (eventTmpl Assumptions.all L g t op) e o)
    {x : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc x bs) :
    s.pc = 156 ∨ s.pc = 168 ∨ s.pc = 181 := by
  apply nc_sites s (mem_allSites s)
  by_contra hn
  have hA : Assumptions.all.any (·.ncLoads t.pc) = false := by
    rw [nc_any, hpc]
    simpa using hn
  exact fires_not_nc hA hf hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0.Data

variable {k : Nat}

/-- **The context of the window at an event before the live event `k`.** -/
theorem w0_wctx (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hP : W0Payloads P L X) (hg : g < L.threads)
    {k : Nat} {ek : Event} (hek : X.get (g, k) = some ek)
    (hσ : ThreadLive P L X g k) {j : Nat} (hj : j < k) {ej : Event}
    (hej : X.get (g, j) = some ej) {dj : D} {nj : (threadD P L g).D}
    (hstj : Frame.stateAt (threadD P L) X g j = some (some nj))
    (hd : nj.1 = .inr ⟨.inl .wg0, dj⟩) : WCtx L g P.scale ((X.tr g).take j) dj ej := by
  obtain ⟨q0, n0⟩ := nj
  obtain rfl : q0 = .inr ⟨.inl .wg0, dj⟩ := hd
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hub : ∀ f, ej.kind ≠ .ub f := (noUbBefore_of_get hX hek).ne hj hej
  obtain ⟨hv, hLd⟩ := w0_upto hp hX hFw hw hP hg hek hσ j (by omega)
  obtain ⟨hv1, -⟩ := w0_upto hp hX hFw hw hP hg hek hσ (j + 1) (by omega)
  obtain ⟨s, hs, -, -, hI, -⟩ := followW_st hp hX hFw hw hej
    (threadLive_le hFw hg hσ (by omega : j ≤ k)) (w0_scale_rd hp) hv j le_rfl
  obtain rfl := Option.some.inj (Option.some.inj (hs.symm.trans hstj))
  obtain ⟨hIW, hOk, hCar, -, hIE, hSk⟩ := hI dj rfl
  obtain ⟨hpcd, -, -⟩ := w0_state_ev hp hX hFw hej hub hstj rfl
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_siteU hsD hX hej hstj hub
  have hel : dj.c.el < Control.elems dj.c.site := hinv
  refine ⟨w0_scale_rd hp, hIW, hOk, hCar, hSk, hIE, hpcd, hel, ?_, hP g j ej hg hw hej, ?_⟩
  · rw [← trace_take_succ hej]
    exact hv1
  · rw [hpcd]
    exact w0Loaded_of (hLd _ hstj dj rfl) hIW hIE

/-- **A non-coherent read before the live event is at the sink or a length load.** -/
theorem w0_nc_before (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j : Nat} {ej : Event} (hej : X.get (g, j) = some ej)
    (hub : ∀ f, ej.kind ≠ .ub f) {nj : (threadD P L g).D}
    (hstj : Frame.stateAt (threadD P L) X g j = some (some nj)) {dj : D}
    (hd : nj.1 = .inr ⟨.inl .wg0, dj⟩) :
    ∀ x bs, ej.kind = .nc x bs → ej.pc = 156 ∨ ej.pc = 168 ∨ ej.pc = 181 := by
  intro x bs hk
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  obtain ⟨hpcd, -, -⟩ := w0_state_ev hp hX hFw hej hub hstj hd
  obtain ⟨q0, n0⟩ := nj
  obtain rfl : q0 = .inr ⟨.inl .wg0, dj⟩ := hd
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_siteU hsD hX hej hstj hub
  obtain ⟨hpc, -⟩ := hat
  rw [hpcd]
  exact nc_site_pc hpc hf hk

/-- **The event at a live state fires from a strictly good state of its site's template.** -/
theorem w0_strict_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hP : W0Payloads P L X) (hg : g < L.threads)
    {k : Nat} {ek : Event} (hek : X.get (g, k) = some ek) (hσ : ThreadLive P L X g k)
    {st : (threadD P L g).D} (hstk : Frame.stateAt (threadD P L) X g k = some (some st)) :
    ∃ (t : TState) (o : Option TState) (ins : Instr), (threadD P L g).Good (some st) t ∧
      kernel.code[(threadD P L g).pc st]? = some ins ∧
      Fires ((threadD P L g).pc st) (eventTmpl Assumptions.all L g t ins.op) ek o := by
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  refine Frame.strict_site (C := threadD P L) hsD hX hek hstk
    (fun j dj ej hj hej hdj hnext => ?_)
  have hjk : j < k := by omega
  have hej' : X.get (g, j) = some ej := hej
  have hub : ∀ f, ej.kind ≠ .ub f := (noUbBefore_of_get hX hek).ne hjk hej'
  obtain ⟨hv, -⟩ := w0_upto hp hX hFw hw hP hg hek hσ j (by omega)
  obtain ⟨s, hs, hslot, -⟩ := followW_st hp hX hFw hw hej'
    (threadLive_le hFw hg hσ (by omega : j ≤ k)) (w0_scale_rd hp) hv j le_rfl
  obtain rfl := Option.some.inj (Option.some.inj (hs.symm.trans hdj))
  intro t u ins hat hi hc hf
  exact Wg0.w0_prev hp ⟨hg, cta_lt hp hg⟩ hslot (fun dd hdd =>
    Wg0.stepConds_of (w0_wctx hp hX hFw hw hP hg hek hσ hjk hej' hdj hdd)
      (w0_nc_before hp hX hFw hej' hub hdj hdd)) ins hat hi hc hf

/-- The events before `k` counted by a class of undefined-behaviour events are none. -/
theorem countP_ub_zero (hal : NoUbBefore X g k) {c : Event → Bool}
    (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl) : ((X.tr g).take k).countP c = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => by
    obtain ⟨j, hj, hjf⟩ := get_lt_of_mem_take hf
    obtain ⟨fl, hk⟩ := hc f hcl
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    exact hal j hj pc fl hjf

/-- **A live state of warpgroup 0 before its event**: the lane is in warps 0 to 3, the reference
invariant holds at the prefix's counts, with the launch facts. -/
theorem w0_alive_facts (hFw : Follow P L X) (hg : g < L.threads) {k : Nat}
    (hal : NoUbBefore X g k) {d : Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg0, d⟩, n))) :
    warp L g < 4 ∧ Wg0.RefCore L g d (fun c => ((X.tr g).take k).countP (Wg0.cls c)) ∧
      Wg0.LaunchOk P L g d := by
  have hJ := (follow_iff.mp hFw g hg k).2 _ hσ
  obtain ⟨-, ⟨hR, -⟩, -, hg2⟩ := hJ
  have hg3 : wgOf L g = 0 := hg2
  have hw : warp L g < 4 := by
    simp only [wgOf, tidOf] at hg3
    simp only [warp]
    omega
  have hc : (fun c => n (.wg0 c)) = fun c => ((X.tr g).take k).countP (Wg0.cls c) :=
    funext fun c => state_count hσ (.wg0 c)
  have hu : n .ub = 0 := (state_count hσ .ub).trans
    (countP_ub_zero hal (fun f h => by obtain ⟨pc, kd⟩ := f; cases kd <;> simp [Proof.cls] at h ⊢))
  have hR' := hR hu
  rw [hc] at hR'
  obtain ⟨hC, hL, -⟩ := hR' (countP_ub_zero hal (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf] at h
    | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf] at h
    | _ => simp [Wg0.cls, Wg0.kindOf] at h))
  exact ⟨hw, hC, hL⟩

set_option maxRecDepth 100000 in
private theorem pay_pc_quiet : ∀ s ∈ allSites, paySite s = true → s ≠ .vote →
    (s.pc ≠ 103 ∧ s.pc ≠ 156 ∧ s.pc ≠ 200 ∧ s.pc ≠ 1122 ∧ s.pc ≠ 280 ∧ s.pc ≠ 283 ∧ s.pc ≠ 278 ∧
      s.pc ≠ 285 ∧ s.pc ≠ 289 ∧ s.pc ≠ 572 ∧ s.pc ≠ 578 ∧ s.pc ≠ 1157) ∧
    (∀ k ∈ List.range 8, s.pc ≠ 477 + 5 * k) ∧ w0OPcs.contains s.pc = false := by
  decide +kernel

/-- **The event at a payload site keeps the trace valid** whatever its kind: the vote's clause
needs only the words loaded, the other payload sites' pcs are none of the words' (the event may be
undefined behaviour). -/
theorem w0_valid_pay {sc : ℝ} {l : List Event} {e : Event} {s : Site} (hsc : 0 < sc)
    (hs : paySite s = true) (hpc : e.pc = s.pc) (hv : W0Valid sc l) (hld : W0Loaded l e.pc) :
    W0Valid sc (l ++ [e]) := by
  by_cases hvt : s = .vote
  · have h578 : e.pc = 578 := by rw [hpc, hvt]; rfl
    exact w0Core_vote h578 (hld.score (by omega) (by omega)).1 (hld.score (by omega) (by omega)).2
      (hld.mask (by omega) (by omega)) (fun k0 hk0 => hld.pair k0 hk0 (by omega) (by omega))
      (hld.peerMax (by omega) (by omega)) hv
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, h13, h14⟩ :=
    pay_pc_quiet s (mem_allSites s) hs hvt
  rw [← hpc] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  exact W0Valid.snoc_quiet hsc ⟨⟨⟨by unfold w0ArrSPc; omega, by unfold w0ArrLPc; omega⟩,
    ⟨h5, h6⟩, ⟨h7, h8⟩, h9, h10, h11, fun k hk hc => h13 k (List.mem_range.mpr hk) hc⟩,
    ⟨h12, by simpa using h14⟩, ⟨h1, h2⟩⟩ hv

/-- The state at index `0` is at the `setmaxnreg`. -/
theorem site_zero {st : (threadD P L g).D}
    (hst : Frame.stateAt (threadD P L) X g 0 = some (some st)) {d : D}
    (hd : st.1 = .inr ⟨.inl .wg0, d⟩) : d.c.site = .smr := by
  obtain rfl := Option.some.inj (Option.some.inj (Frame.stateAt_zero.symm.trans hst))
  exact enter_smr (b := (startupCode P L g).init) hd

/-- **The control machine stops only at the exit**: a step without a successor is the exit's, for
an event of the site's kind that is no undefined behaviour (the nc reads' words rebuild). -/
theorem succ_none_exit {c : Control.D} {e : Event} {w : BitVec 64}
    (h : Control.succ P L g w c e = none) (hK : EvK P L g w c e) (hub : ∀ f, e.kind ≠ .ub f)
    (hnc : (c.site = .sink ∨ c.site = .lenA ∨ c.site = .lenB) →
      ∀ x bs, e.kind = .nc x bs → ∃ v, rebuild 3 bs = .ok v) : e.kind = .exit := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  unfold EvK at hK
  have hub0 : ¬ ∃ f, e.kind = .ub f := fun ⟨f, hf⟩ => hub f hf
  cases s <;> (try (rename_i x; fin_cases x)) <;> (try (rename_i x; fin_cases x)) <;>
    simp only [Control.succ, Option.some_ne_none, NcEv, PollEv, TcLdEv, RdAt, hub0,
      or_false] at h hK
  all_goals first
    | exact hK
    | (exfalso; obtain ⟨a, bs, hk⟩ := hK; simp [Control.dataRd, hk] at h; done)
    | (exfalso; obtain ⟨ok, hk⟩ := hK; simp [Control.poll, hk] at h; done)
    | (exfalso; obtain ⟨vals, hk⟩ := hK; simp [Control.tcLoad, hk] at h; done)
    | (exfalso; obtain ⟨-, a, bs, hk⟩ := hK; simp [hk] at h; split at h <;> simp at h)
    | (exfalso; split at h <;> cases h)
    | (exfalso; obtain ⟨a, bs, hk⟩ := hK
       obtain ⟨v, hv⟩ := hnc (by simp) a bs hk
       simp only [Control.ncWord, hk, hv] at h
       split at h <;> first | (rename_i heq; cases heq; done) | simp at h)

end Wg0.Data

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
