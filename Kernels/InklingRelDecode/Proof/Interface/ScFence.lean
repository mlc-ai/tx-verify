-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ScFence
public import Kernels.InklingRelDecode.Proof.Thread.FootOrder
public import Kernels.InklingRelDecode.Proof.Interface.FootBar
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Protocol.BaseWord
public import Kernels.InklingRelDecode.Proof.Protocol.BarOne

@[expose] public section

/-!
# Every tensor copy's issue is after every read of the base word, through a proxy fence

A tensor copy writes the asynchronous proxy; the generic read of the Tensor Memory base word
`[sharedBase, sharedBase + 4)` is ordered before it only through a `fence.proxy.async` that is after
the read and before the issue (`ProxyBefore`). The kernel has two such fences, in the prologue of
the default partition: `ProA.Site.fnc0` after the mbarrier initializations, before the prologue's
own copies, and `fnc1` after the query stores, before the role-table store.

* A copy of the prologue is issued at a site after `fnc0` (`ProA.next_cross_fnc0`: the site order),
  so its thread has fired the fence earlier, and the fence is before the issue by program order.
* A copy of the loader is issued after the loader's barrier-1 arrival of ordinal 0, which
  synchronizes with the arrival of ordinal 0 of the CTA's thread 0, and `fnc1` of thread 0 is before
  that arrival (`exists_pastPro`).
* In both cases the fence is after every base-word read: the thread that fired it has made two
  barrier-0 arrivals, and the read is between the thread's first and second (`Bar.bar0_chain`).

`base_before_copy` is `ProxyBefore` for the issue of every tensor copy, for any byte of the CTA's
shared memory.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Bar

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem ptc_pc_gt : ∀ i < 12, ProA.Site.fnc0.pc < (ProA.ptcSite i).pc := by decide +kernel

/-- The default-partition states after the prologue site `c`. -/
def PastPro (c : ProA.Site) : TSt → Prop
  | .d (.pro d) => c.pc < d.site.pc
  | .d (.sm _) => True
  | .d (.epi _) => True
  | _ => False

/-- A step into a state after the site `c` comes from `c` or from such a state, for a site that
no step of the prologue's machine jumps over. -/
theorem next_pastPro {c : ProA.Site}
    (hcross : ∀ {L : Launch} {g : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D} {e : Event},
      ProA.next L g ⟨s, dt⟩ e = some (some d') → s.pc ≤ c.pc → c.pc < d'.site.pc → s = c)
    (hb : c.pc < ProA.Site.bar18.pc) (hst : ProA.Site.sMax.pc ≤ c.pc) {g : Nat} {s s' : TSt}
    {e : Event} (hn : (threadCode L g Q).next s e = some (some s')) (hs : PastPro c s') :
    PastPro c s ∨ ∃ d : ProA.D, s = .d (.pro d) ∧ d.site = c := by
  cases s with
  | w s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map (Option.map TSt.w) =
      some (some s') from hn)
    exact hs.elim
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    cases s with
    | dstart d =>
      exfalso
      change DComp.dstartNext L g Q d _ = _ at ha
      unfold DComp.dstartNext at ha
      obtain ⟨d', -, hs'⟩ := map_map_eq_some_some ha
      split at hs'
      · subst hs'
        have : ¬ c.pc < ProA.Site.sMax.pc := by omega
        exact this (by simpa [PastPro, ProA.D.start] using hs)
      · subst hs'
        exact hs
    | pro dp =>
      change DComp.proNext L g Q dp _ = _ at ha
      unfold DComp.proNext at ha
      split at ha
      · rename_i hbar
        left
        show c.pc < dp.site.pc
        rw [hbar]
        exact hb
      · obtain ⟨d3, hd3, h3⟩ := map_map_eq_some_some ha
        subst h3
        obtain ⟨site, dt⟩ := dp
        by_cases hle : site.pc ≤ c.pc
        · exact .inr ⟨_, rfl, hcross hd3 hle hs⟩
        · exact .inl (by simpa [PastPro] using Nat.lt_of_not_le hle)
    | sm d => left; trivial
    | epi d => left; trivial

theorem init_notPastPro (c : ProA.Site) (g : Nat) : ¬ PastPro c (code L Q g).init := by
  show ¬ PastPro c (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init)
  split <;> exact fun h => h

/-- **A state after the site `c` has `c`'s state earlier in its run.** -/
theorem exists_pastPro {c : ProA.Site}
    (hcross : ∀ {L : Launch} {g : Nat} {s : ProA.Site} {dt : ProA.Dat} {d' : ProA.D} {e : Event},
      ProA.next L g ⟨s, dt⟩ e = some (some d') → s.pc ≤ c.pc → c.pc < d'.site.pc → s = c)
    (hb : c.pc < ProA.Site.bar18.pc) (hst : ProA.Site.sMax.pc ≤ c.pc) {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → PastPro c s →
      ∃ j < k, ∃ d : ProA.D, St Q L X g j = some (some (.d (.pro d))) ∧ d.site = c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hσ hs
    by_cases hinit : s = (code L Q g).init
    · subst hinit
      exact absurd hs (init_notPastPro c g)
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ hinit
      rcases next_pastPro hcross hb hst hn hs with h | ⟨d, rfl, hd⟩
      · obtain ⟨j, hj, d, hd, hsite⟩ := ih k0 hlt s0 hs0 h
        exact ⟨j, by omega, d, hd, hsite⟩
      · exact ⟨k0, hlt, d, hs0, hd⟩

/-- **The event at a fence's state** is the `fence.proxy.async` of the CTA's shared memory. -/
theorem fnc_event (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g j : Nat} {e : Event} {d : ProA.D}
    (hg : g < L.threads) (he : X.get (g, j) = some e)
    (hσ : St Q L X g j = some (some (.d (.pro d)))) (hs : d.site = .fnc0 ∨ d.site = .fnc1) :
    ∃ pc, e = ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by
    rcases hs with h | h <;> simp [ExitState])
  exact ⟨_, ProA.shape_fnc (fired_pro hF) hs⟩

/-- **A thread of the prologue has made no barrier-1 event before any of its prologue
states.** -/
theorem pro_count0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} (hd : g % L.block < 128)
    (hk : k ≤ (X.tr g).length) {d : ProA.D} (hσ : St Q L X g k = some (some (.d (.pro d)))) :
    b1N X g k = 0 := by
  obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hS hd k _ hk hσ
  cases hd'
  rw [h]
  obtain ⟨site, dt⟩ := d
  cases site <;> rfl

/-- **A read of the base word is before every event of a thread of its CTA whose state is past the
common start**: the read has one barrier-0 event before it, and the later event is after its
thread's arrival of ordinal 1. -/
theorem base_read_before_late (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {h kr u kc : Nat} {s : TSt} (hsame : SameCta L h u) (hr : kr < (X.tr h).length)
    (hb : BaseReadAt Q L X h kr) (hσ : St Q L X u kc = some (some s)) (hl : ¬ tLb s < 2)
    (hkc : kc < (X.tr u).length) : baseCausality L X (h, kr) (u, kc) := by
  obtain ⟨hc1, hn1⟩ := baseRead_facts hX hS hr hb
  have h2 : 2 ≤ ((X.tr u).take kc).countP (Execution.isBarId 0) :=
    bar0_ordinal_two hX hS hkc.le hσ hl
  obtain ⟨j1, pc1, hj1, hf, hord⟩ := arrival_before hX hS ht (h := u) (k := kc) (r := 1)
    (by omega) le_rfl
  exact bar0_chain hpre hX hS ht hsame hf (by omega) (by omega) hr hn1 hj1 hkc

/-- **`ProxyBefore` for the issue of every tensor copy**: a read of the base word is before a
`fence.proxy.async` that is before the copy's issue, for every byte of the CTA's shared memory. -/
theorem base_before_copy (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (ht : Frame.Tracked (code L Q) X)
    (hE : Bar1Exits L X) (hRR : RoleReads L X) {h kr : Nat} (hr : kr < (X.tr h).length)
    (hb : BaseReadAt Q L X h kr) {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) (hcta : i.1 / L.block = h / L.block)
    (hh : h < L.threads) {l : Loc} (hls : l.space = .shared) (hlc : l.cta = h / L.block) :
    ProxyBefore L X (h, kr) i l := by
  have hgi : i.1 < L.threads := Frame.lt_of_get hX he
  have hsame : SameCta L h i.1 := ⟨hh, hgi, hcta.symm⟩
  have hli : i.2 < (X.tr i.1).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simpa using this
  have hcover : AsyncFenceCovers L (some (.shared .cta)) i.1 l := ⟨hls, by rw [hlc, hcta]⟩
  rcases copy_event_stateW hpre hX hS ht hgi he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, j, hj, hsite, -⟩ | ⟨d, P, hσ, -⟩
  · -- the prologue's copy: after its own `fnc0`
    have hpast : PastPro ProA.Site.fnc0 (.d (.pro d)) := by
      show ProA.Site.fnc0.pc < d.site.pc
      rw [hsite]
      exact ptc_pc_gt j hj
    obtain ⟨j0, hj0, d0, hσ0, hs0⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc0 h' a b) (by decide) (by decide) i.2 _ hσ hpast
    have hj0' : j0 < (X.tr i.1).length := by omega
    obtain ⟨e0, he0⟩ : ∃ e0, X.get (i.1, j0) = some e0 :=
      ⟨_, List.getElem?_eq_getElem hj0'⟩
    obtain ⟨pcf, hev⟩ := fnc_event hX hS hT hgi he0 hσ0 (Or.inl hs0)
    have hfence : X.IsProxyFence (i.1, j0) (.async (some (.shared .cta))) none :=
      ⟨pcf, by rw [he0, hev]⟩
    refine ⟨(i.1, j0), _, _, hfence, hgi, hcover, ⟨hgi, hgi, rfl⟩, ?_, ?_⟩
    · exact base_read_before_late hpre hX hS ht hsame hr hb hσ0 (by simp [tLb_pro])
        (by omega)
    · exact .single (.inl (po_of_source_not_access (X := X) rfl hj0 hli (by
        rw [he0, hev]; rfl)))
  · -- the loader's copy: after the barrier-1 arrival of ordinal 0, which follows `fnc1`
    have hwk : 128 ≤ i.1 % L.block := by
      have := (cls_inv i.2 _ hli.le hσ).not.mp (by exact fun h => h)
      omega
    have hbk : L.block = 256 := hpre.block
    have hblk : 0 < L.block := by omega
    have hb1 : 1 ≤ b1N X i.1 i.2 := by
      obtain ⟨-, t, -, h2, -, -, -, -⟩ := phase_inv hpre hX hS hRR i.2 _ hli.le hσ
      rw [h2]
      have : 1 ≤ (tPh (.w (.loader d P))).2 := by
        simp only [tPh]
        cases hs : d.site <;> simp [wPh, hs]
      omega
    obtain ⟨j0, pcf, hj0, hf0, hc0⟩ := arrival1_before hpre hX (h := i.1) (k := i.2) (r := 0)
      (by omega)
    have hp : j0 + 1 < (X.tr i.1).length := by omega
    have hg0 : i.1 / L.block * L.block < L.threads :=
      lt_of_le_of_lt (Nat.div_mul_le_self i.1 L.block) hgi
    have hd0 : i.1 / L.block * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
    have hcta0 : i.1 / L.block * L.block / L.block = i.1 / L.block := Nat.mul_div_cancel _ hblk
    obtain ⟨i0, pc0, hf00, hc00⟩ := bar1_has hpre hX hE (g := i.1 / L.block * L.block)
      (h := i.1) hf0 hp hcta0
    have hc00' : ((X.tr (i.1 / L.block * L.block)).take i0).countP (Execution.isBarId 1) = 0 := by
      rw [hc00]
      exact hc0
    have he00 : X.get (i.1 / L.block * L.block, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hf00
    have hli0 : i0 < (X.tr (i.1 / L.block * L.block)).length :=
      (List.getElem?_eq_some_iff.mp he00).1
    have hprev : i0 = 0 ∨ ∃ k', i0 = k' + 1 ∧ TT Q L X (i.1 / L.block * L.block, k') := by
      rcases Nat.eq_zero_or_pos i0 with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ⟨i0 - 1, by omega, ?_⟩
        have := ht (i.1 / L.block * L.block) (i0 - 1 + 1) hg0
        exact this
    obtain ⟨s0, hσ0⟩ := state_of_prev hS hX he00 bar_not_ub hprev
    obtain ⟨dd, rfl, hb1'⟩ := dphase_inv hpre hX hS hd0 i0 s0 hli0.le hσ0
    have hbar := event_b1 hpre hX hS he00 hσ0
    rw [isBarId_bar] at hbar
    have h0 : (dPh dd).2 = 0 := by rw [← hb1']; exact hc00'
    obtain ⟨dd', rfl, hs⟩ := dB1_phase0 h0 hbar.symm
    obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc1 h' a b) (by decide) (by decide) i0 _ hσ0
      (by show ProA.Site.fnc1.pc < dd'.site.pc; rw [hs]; decide)
    have hj1' : j1 < (X.tr (i.1 / L.block * L.block)).length := by omega
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (i.1 / L.block * L.block, j1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem hj1'⟩
    obtain ⟨pcf1, hev⟩ := fnc_event hX hS hT hg0 he1 hσ1 (Or.inr hs1)
    have hfence : X.IsProxyFence (i.1 / L.block * L.block, j1) (.async (some (.shared .cta)))
        none := ⟨pcf1, by rw [he1, hev]⟩
    have hsame0 : SameCta L h (i.1 / L.block * L.block) :=
      ⟨hh, hg0, by rw [hcta0]; exact hcta.symm⟩
    have hcover0 : AsyncFenceCovers L (some (.shared .cta)) (i.1 / L.block * L.block) l :=
      ⟨hls, by rw [hlc, hcta0, hcta]⟩
    refine ⟨(i.1 / L.block * L.block, j1), _, _, hfence, hg0, hcover0,
      ⟨hg0, hgi, by rw [hcta0]⟩, ?_, ?_⟩
    · exact base_read_before_late hpre hX hS ht hsame0 hr hb hσ1 (by simp [tLb_pro])
        (by omega)
    · exact Bar.bar1_baseCausality hpre hX ⟨hg0, hgi, hcta0⟩ hf00 hf0 hp
        (by rw [hc00, hc0]) hj1 hj0 hli

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
