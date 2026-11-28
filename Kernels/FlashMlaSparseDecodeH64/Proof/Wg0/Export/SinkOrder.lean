-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceSk
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.LseSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NcRead
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The last sink event of a lane

The sink word `w0SkWord` of the events before a late event of a lane of warpgroup 0 is `-inf`
when the sink pointer is null, and else the scaled word of the one sink load (pc 156), the event
after the `setmaxnreg` (pc 103). Read off the control machine's steps (`PrevPc` of the data
machine): the sink load is at the site after the `setmaxnreg` when the pointer is set, and no
later site is at pc 103 or 156. -/

/-! # The sink load of warpgroup 0 reads its head's word of the sink array

An event of a lane of warpgroup 0 at pc 156 is the `.nc` read of the four bytes at
`sinkBase + 4 (tid % 64)`, with the sink pointer set (`Wg0.sink_read`); `Pre` gives the bytes
(`paramSink`) and the `f32` word they are. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The sink load reads the head's word**: the event at pc 156 is a `.nc` read, the sink
pointer is set, and the word is `ReadsLaunchWord` at the head's address. -/
theorem wg0_sink_reads (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : Wg0At L g e.pc) (hpc : e.pc = 156) :
    ∃ (x : Nat) (a : Acc) (bs : List (Option Byte)), P.sinkBase = some x ∧ e.kind = .nc a bs ∧
      ReadsLaunchWord e (x + 4 * (tidOf L g % 64)) bs := by
  have hub := noUb_kind hnu he
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, hE, hw⟩ := wg0_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  obtain ⟨t, ins, o, hat', hinv, hc', hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  have hs : d.site = .sink := Wg0.Data.site_pc_156 (hpcσ.symm.trans hpc)
  have hK := hE.2
  unfold Wg0.EvK at hK
  rw [hs] at hK
  obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .nc a bs := by
    rcases hK with h | ⟨f, hf'⟩
    · exact h
    · exact absurd hf' (hub f)
  rcases wg0_pred hFw hnu hw hg hkl.le hσ with ⟨-, -, d', -, e', -, -, hS⟩ | h
  · obtain ⟨-, hptr, -⟩ := Wg0.sink_pred hS hs
    obtain ⟨x, hx⟩ := len_ptr hptr
    obtain ⟨bs', hr⟩ := Wg0.sink_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact ⟨x, a, bs, hx, hk, hr⟩
  · rw [hs] at h; cases h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0

/-- The invariant at the pc `p` of the next event after the events `l`: before the sink load
the word is `-inf`; at it the pointer is set; after it the word is `-inf` for a null pointer, else
the scaled word of a sink load among `l`. -/
def SinkInv (P : Params) (l : List Event) (p : Nat) : Prop :=
  (p ≤ 156 → w0SkWord l = w0NegInf) ∧ (p = 156 → ∃ x, P.sinkBase = some x) ∧
    (157 ≤ p → (P.sinkBase = none ∧ w0SkWord l = w0NegInf) ∨
      ∃ f ∈ l, ∃ (a : Acc) (bs : List (Option Byte)) (x : Nat), f.pc = 156 ∧
        f.kind = .nc a bs ∧ P.sinkBase = some x ∧ w0SkOf f = some (w0SkWord l))

private theorem site_ge (s : Site) : s.pc = 103 ∨ s.pc = 156 ∨ 157 ≤ s.pc := by
  cases s
  all_goals first
    | (simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> simp [Site.pc]; done)
    | (rename_i a k; fin_cases a <;> fin_cases k <;> simp [Site.pc, ost2Base])

private theorem eqz_W {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) : eqz64 (W x) = false := by
  simp only [eqz64, PTX.compare, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.ofInt_ofNat]
  simp only [decide_eq_false_iff_not]
  intro he
  omega

/-- With the sink pointer set the site after the `setmaxnreg` is the sink. -/
private theorem afterSmr_sink (hp : Pre P L m) {x : Nat} (hx : P.sinkBase = some x)
    {w : BitVec 64} (c : Control.D) : (Control.afterSmr P L g w c).site = .sink := by
  obtain ⟨hx0, -, hx64⟩ := hp.sinkAddressable x hx
  have h1 : eqz64 (pw8 (P.sinkBase.getD 0)) = false := by
    rw [hx, Option.getD_some, pw8_eq x (by omega)]
    exact eqz_W hx0 (by omega)
  have h2 : scmp .ge .s (Control.r10W L g) (pw 64) = false := by
    have e1 : Control.r10W L g = W (tidOf L g % 64) :=
      andi_W_low (k := 6) (tidOf_lt hp g) (by decide)
    have e2 : pw 64 = W 64 := by
      simp only [pw, leNat_eq, pow_zero, Nat.div_one]; rfl
    have h3 := tidOf_lt hp g
    rw [e1, e2]
    have h4 : tidOf L g % 64 < 64 := Nat.mod_lt _ (by norm_num)
    simp only [scmp, PTX.compare, r32_W (show tidOf L g % 64 < 2 ^ 32 by omega),
      r32_W (show 64 < 2 ^ 32 by omega), toSigned, toNat_W (show tidOf L g % 64 < 2 ^ 64 by omega),
      toNat_W (show 64 < 2 ^ 64 by omega), decide_eq_false_iff_not]
    split_ifs <;> omega
  simp [Control.afterSmr, h1, h2]

/-- **One step of the invariant** along the control machine's step `c -> c'` at the event `f`. -/
private theorem sinkInv_step (hp : Pre P L m) {l : List Event} {f : Event} {c c' : Control.D}
    (hI : SinkInv P l f.pc) (hpc : c.site.pc = f.pc)
    (hs : Control.succ P L g (warpW L g) c f = some (some c'))
    (hnc : f.pc = 156 → ∃ (a : Acc) (bs : List (Option Byte)) (x : Nat),
      f.kind = .nc a bs ∧ P.sinkBase = some x) : SinkInv P (l ++ [f]) c'.site.pc := by
  obtain ⟨hI1, hI2, hI3⟩ := hI
  rcases site_ge c.site with h | h | h
  · have hsite : c.site = .smr := Data.site_pc_103 h
    have hf : f.pc = 103 := hpc ▸ h
    have hsk : w0SkWord (l ++ [f]) = w0NegInf := by
      simp [Data.w0SkWord_snoc, w0SkOf, hf, w0NegInf]
    simp only [Control.succ, hsite, Option.some.injEq] at hs
    subst hs
    refine ⟨fun _ => hsk, fun h156 => ?_, fun h157 => ?_⟩
    · obtain ⟨-, hptr, -⟩ := sink_pred (P := P) (L := L) (g := g) (w := warpW L g) (d := c)
        (e := f) (d' := Control.afterSmr P L g (warpW L g) c)
        (by simp [Control.succ, hsite]) (Data.site_pc_156 h156)
      exact len_ptr hptr
    · rcases hn : P.sinkBase with _ | x
      · exact Or.inl ⟨rfl, hsk⟩
      · exfalso
        have := afterSmr_sink (g := g) (w := warpW L g) hp hn c
        rw [this] at h157
        simp [Site.pc] at h157
  · have hsite : c.site = .sink := Data.site_pc_156 h
    have hf : f.pc = 156 := hpc ▸ h
    obtain ⟨a, bs, x, hk, hx⟩ := hnc hf
    have hsk : w0SkOf f = some (w0SkWord (l ++ [f])) := by
      have h1 : w0SkOf f ≠ none := by
        simp [w0SkOf, hf, hk]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h1
      rw [Data.w0SkWord_snoc, hv]
      simp
    simp only [Control.succ, hsite, Control.dataRd, hk, Option.some.injEq] at hs
    subst hs
    have h3 : 157 ≤ (Control.afterSink P L g (warpW L g) c).site.pc := by
      rcases Control.site_afterSink (P := P) (L := L) (g := g) (w := warpW L g) c with
        h | h | h | h | h <;> simp [h, Site.pc]
    refine ⟨fun h4 => by omega, fun h4 => by omega, fun _ => Or.inr ⟨f, ?_, a, bs, x, ?_⟩⟩
    · simp
    · exact ⟨hf, hk, hx, hsk⟩
  · have h1 : f.pc ≠ 103 := by omega
    have h2 : f.pc ≠ 156 := by omega
    have hsk : w0SkWord (l ++ [f]) = w0SkWord l := by
      rw [Data.w0SkWord_snoc]
      simp [w0SkOf, h1, h2]
    have hf : 157 ≤ f.pc := by omega
    have hc : 157 ≤ c'.site.pc := by
      by_cases ha : c.site = .arrS
      · rcases Control.succ_arrS hs ha with h | h <;> simp [h, Site.pc]
      · have := Control.succ_pc_mono hs ha
        omega
    refine ⟨fun h => by omega, fun h => by omega, fun _ => ?_⟩
    rcases hI3 hf with ⟨hn, hw⟩ | ⟨f', hf', a, bs, x, h1', h2', h3', h4'⟩
    · exact Or.inl ⟨hn, hsk.trans hw⟩
    · exact Or.inr ⟨f', List.mem_append_left _ hf', a, bs, x, h1', h2', h3', by rw [hsk]; exact h4'⟩

/-- Events before the `setmaxnreg` leave the sink word `-inf`. -/
private theorem skWord_pre {l : List Event} (h : ∀ f ∈ l, f.pc < 103) :
    w0SkWord l = w0NegInf := by
  have : l.filterMap w0SkOf = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have := h x hx
    simp [w0SkOf, show x.pc ≠ 103 by omega, show x.pc ≠ 156 by omega]
  rw [w0SkWord, this]
  rfl

/-- The role entered from the startup's first state starts at its first site. -/
private theorem enter_smr {b : Startup.D} {d : Data.D}
    (h : Code.enter (startupCode P L g) (Code.withStubs (fragD P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) b = .inr ⟨.inl .wg0, d⟩) :
    d.c.site = .smr := by
  unfold Code.enter at h
  split at h
  · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases eq_of_heq h
    rfl
  · cases h

end Wg0

/-- **The sink word at a late event of a lane** (valid trace): at an event at pc 157 or later, the
sink word of the events before it is `-inf` when the sink pointer is null, and else the scaled
word of the lane's sink load (pc 156, an earlier event, a `.nc` read). -/
theorem w0_sink_order (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv0 : W0Trace P X g)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hge : 157 ≤ e.pc) :
    (P.sinkBase = none ∧ w0SkWord ((X.tr g).take k) = w0NegInf) ∨
      ∃ (j : Nat) (f : Event) (x : Nat) (a : Acc) (bs : List (Option Byte)), j < k ∧
        X.get (g, j) = some f ∧ f.pc = 156 ∧ f.kind = .nc a bs ∧ P.sinkBase = some x ∧
        w0SkOf f = some (w0SkWord ((X.tr g).take k)) := by
  have hub := noUb_kind hnu he
  have hF := followW hp hX hFw hw he hub (w0_scale_rd hp) (hv0.take (j := k))
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hnc : ∀ j f, X.get (g, j) = some f → f.pc = 156 →
      ∃ (a : Acc) (bs : List (Option Byte)) (x : Nat), f.kind = .nc a bs ∧ P.sinkBase = some x :=
    fun j f hf h156 => by
      obtain ⟨x, a, bs, hx, hk, -⟩ := wg0_sink_reads hp hX hFw hnu hf ⟨hw, by omega, by omega⟩ h156
      exact ⟨a, bs, x, hk, hx⟩
  have hstart : ∀ j f s (b : Startup.D) n, X.get (g, j) = some f →
      Frame.stateAt (threadD P L) X g j = some (some s) → s = (Sum.inl b, n) → f.pc < 103 := by
    intro j f s b n hf hst hs
    have hubf := noUb_kind hnu hf
    have hpc' := Frame.event_pcU hsD hX hf hst hubf
    subst hs
    obtain ⟨t, ins, o, hat, hinv, hcode, hf'⟩ := Frame.fired_siteU hsD hX hf hst hubf
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : f.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  have key : ∀ j ≤ k, ∀ f, X.get (g, j) = some f →
      Wg0.SinkInv P ((X.tr g).take j) f.pc := by
    intro j
    induction j with
    | zero =>
      intro _ f hf
      obtain ⟨s, hst, hslot, hpre, -, -, -⟩ := hF 0 (Nat.zero_le _)
      have hpc' := Frame.event_pcU hsD hX hf hst (noUb_kind hnu hf)
      obtain ⟨q0, n⟩ := s
      rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
      · obtain rfl : q0 = .inl b := hb
        have hlt := hstart 0 f _ b n hf hst rfl
        exact ⟨fun _ => Wg0.skWord_pre (hpre b rfl), fun h => by omega, fun h => by omega⟩
      · obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
        have hin := congrArg Prod.fst (Option.some.inj (Option.some.inj hst))
        have h0 := Wg0.enter_smr (P := P) (L := L) (g := g) (b := (startupCode P L g).init) hin
        have hp103 : f.pc = 103 := by
          have : f.pc = d.c.site.pc := hpc'
          rw [this, h0]; rfl
        exact ⟨fun _ => Wg0.skWord_pre (fun f hf => by simp at hf), fun h => by omega,
          fun h => by omega⟩
    | succ j ih =>
      intro hj f hf
      obtain ⟨s, hst, hslot, hpre, -, hPrev, -⟩ := hF (j + 1) hj
      have hpc' := Frame.event_pcU hsD hX hf hst (noUb_kind hnu hf)
      obtain ⟨q0, n⟩ := s
      rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
      · obtain rfl : q0 = .inl b := hb
        have hlt := hstart (j + 1) f _ b n hf hst rfl
        exact ⟨fun _ => Wg0.skWord_pre (hpre b rfl), fun h => by omega, fun h => by omega⟩
      · obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
        have hp' : f.pc = d.c.site.pc := hpc'
        rcases hPrev d rfl j rfl with ⟨hs, hlt⟩ | ⟨f', c, hf', hpcf, hsucc, -⟩
        · have hp103 : f.pc = 103 := by rw [hp', hs]; rfl
          exact ⟨fun _ => Wg0.skWord_pre hlt, fun h => by omega, fun h => by omega⟩
        · have hfj : X.get (g, j) = some f' := hf'
          have h1 := Wg0.sinkInv_step hp (ih (by omega) f' hfj) hpcf hsucc (hnc j f' hfj)
          rw [← trace_take_succ hfj] at h1
          rw [hp']
          exact h1
  obtain ⟨-, -, h3⟩ := key k le_rfl e he
  rcases h3 hge with h | ⟨f, hfm, a, bs, x, h1, h2, h3, h4⟩
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfm
    rw [List.getElem?_take] at hj
    split at hj
    · exact Or.inr ⟨j, f, x, a, bs, by omega, hj, h1, h2, h3, h4⟩
    · cases hj

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
