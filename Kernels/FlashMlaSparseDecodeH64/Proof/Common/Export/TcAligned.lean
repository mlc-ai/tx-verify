-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0SldArm
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TcSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll

@[expose] public section

/-! # The collective `tcgen05` events of the lanes of a warp agree

The collective events are warps 0-3's (`tc_warp`). At its `k`-th collective a startup lane is at
the allocation (`k = 0`) or the relinquishment (`k = 1`), a warpgroup-0 lane at a collective site
`d`; two lanes of a warp at one `k`:

* `tc_uniform`: are at one pc with one static part. Startup lanes by `k`; a startup and a
  warpgroup-0 lane do not meet at one `k` (the warpgroup's count starts at the startup's two);
  warpgroup-0 lanes at one place (`w0_tcKey` both ways), hence one site (`Wg0.tc_place_inj`; the
  score loads' arm is the warp word's, `w0_sldArm`), whose event is the site's (`EvK`).
* `tc_unexited`: no lane of the warp exits with at most `k` collectives. The exit's state has the
  largest place (`Wg0.place_le`), so `w0_tcKey` puts `k + 1` collectives before it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The static part of the collective event of a warpgroup-0 site. -/
private def siteStatic : Wg0.Site → TcKind
  | .sld _ k => .ld (400 + 32 * k.val) [] .s32x32b
  | .rld c | .old c => .ld (64 * c.val) [] .s32x32b
  | .rst c => .st (64 * c.val) [] .s32x32b
  | .rstw _ => .waitSt
  | .dealloc => .resource .one none (.dealloc 0 512)
  | _ => .waitLd

/-- **The static part of a collective event of warpgroup 0 is its site's.** -/
private theorem evK_static {d : Wg0.Control.D} {e : Event} {w : BitVec 64}
    (hd : Wg0.EvK P L g w d e) (hu : ∀ f, e.kind ≠ .ub f) (hc : isTcColl e = true)
    {ke : TcKind} (he : e.kind = .tc ke) : tcStatic ke = siteStatic d.site := by
  have htc : d.site.isTc = true := by rw [← Wg0.evK_tc hu hd]; exact hc
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at htc ⊢
  cases st <;> simp only [Wg0.Site.isTc, Bool.false_eq_true] at htc <;>
    simp only [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, siteStatic] at hd ⊢
  all_goals first
    | (rcases hd with ⟨vals, hk⟩ | ⟨f, hk⟩
       · rw [hk] at he; simp only [Kind.tc.injEq] at he; subst he; rfl
       · exact absurd hk (hu f))
    | (rw [hd] at he; simp only [Kind.tc.injEq] at he; subst he; rfl)
    | (rcases hd with hk | ⟨f, hk⟩
       · rw [hk] at he; simp only [Kind.tc.injEq] at he; subst he; rfl
       · exact absurd hk (hu f))

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw hnu

/-- **A startup collective** is the allocation (`k = 0`) or the relinquishment (`k = 1`), in
warp 0. -/
private theorem tc_start (hw : warp L g < 4) (hg : g < L.threads) {j k : Nat} {e : Event}
    {d0 : Startup.D} {n0 : Cls → Nat} (hce : isTcColl e = true) (hcnt : tcCnt X g j = k)
    (hσ : Frame.stateAt (thread P L) X g j = some (some (.inl d0, n0)))
    (hxd : Startup.exitOf d0 = none) (hev : Startup.Ev L g d0 e) (hpc : e.pc = d0.site.pc) :
    ((k = 0 ∧ e.pc = 91 ∧
        e.kind = .tc (.resource .one (some (Startup.tmemWordLoc L g)) (.alloc 512))) ∨
      (k = 1 ∧ e.pc = 96 ∧ e.kind = .tc (.resource .one none .relinquish))) ∧
      scmpi .ne .b (warpW L g) 0 = false := by
  obtain ⟨hK, hW0⟩ := w0_tcStart hp hX hFw hnu hw hg hσ hxd hev hce hcnt
  refine ⟨?_, hW0⟩
  rcases hK with ⟨hs, hk⟩ | ⟨hs, hk⟩
  · refine .inl ⟨hk, by rw [hpc, hs]; rfl, ?_⟩
    simpa only [Startup.Ev, hs] using hev
  · refine .inr ⟨hk, by rw [hpc, hs]; rfl, ?_⟩
    simpa only [Startup.Ev, hs] using hev

/-- **A startup lane and a warpgroup-0 lane of a warp are not at one collective ordinal**: the
warpgroup's count starts at the two of the startup. -/
private theorem tc_mixed (hsw : SameWarp L g h) {i k : Nat} {s : Wg0.Control.D}
    {n' : Cls → Nat} (hk1 : k ≤ 1) (hW0 : scmpi .ne .b (warpW L g) 0 = false)
    (hs : Frame.stateAt (thread P L) X h i = some (some (.inr ⟨.inl .wg0, s⟩, n')))
    (hk' : tcCnt X h i ≤ k) (hwh : warp L h < 4) : False := by
  obtain ⟨-, hWe⟩ := warpW_same hp hsw
  obtain ⟨h1, -⟩ := w0_tc hp hX hFw hwh hsw.1.2.1 i (noUbBefore_of_noUb hnu) _ hs
  have hb2 : tcBase L h = 2 := by simp [tcBase, ← hWe, hW0]
  omega

/-- **Two lanes of a warp at their `k`-th collective `tcgen05` event are at one pc with one
static part.** -/
theorem tc_uniform (hsw : SameWarp L g h) {j i k : Nat} {e e' : Event}
    (he : X.get (g, j) = some e) (he' : X.get (h, i) = some e')
    (hc : isTcColl e = true) (hc' : isTcColl e' = true)
    (hk : ((X.tr g).take j).countP isTcColl = k) (hk' : ((X.tr h).take i).countP isTcColl = k) :
    e.pc = e'.pc ∧ ∀ ke kf, e.kind = .tc ke → e'.kind = .tc kf → tcStatic ke = tcStatic kf := by
  have hg : g < L.threads := hsw.1.1
  have hh : h < L.threads := hsw.1.2.1
  have hw := tc_warp hp hX hFw hg he hc
  obtain ⟨hwe, hWe⟩ := warpW_same hp hsw
  have hwh : warp L h < 4 := hwe ▸ hw
  have hub := noUb_kind hnu he
  have hub' := noUb_kind hnu he'
  obtain ⟨σ, hσ, -, -, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨σ', hσ', -, -, hev', hpc'⟩ := ev_at hp hX hFw he' hub'
  have hsw' : SameWarp L h g := ⟨⟨hh, hg, hsw.1.2.2.symm⟩, hsw.2.symm⟩
  have hk2 : tcCnt X g j = k := hk
  have hk3 : tcCnt X h i = k := hk'
  have hj : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hi : i ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1.le
  rcases w0_bst hFw hnu hw hg hσ with ⟨d0, n0, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -⟩ <;>
    rcases w0_bst hFw hnu hwh hh hσ' with ⟨s0, m0, rfl, hxs⟩ | ⟨s, n', rfl, hC', hL', -⟩
  · -- two startup lanes
    change e.pc = d0.site.pc at hpc
    change e'.pc = s0.site.pc at hpc'
    obtain ⟨hK, -⟩ := tc_start hp hX hFw hnu hw hg hc hk hσ hxd hev hpc
    obtain ⟨hK', -⟩ := tc_start hp hX hFw hnu hwh hh hc' hk' hσ' hxs hev' hpc'
    have hcta : g / L.block = h / L.block := hsw.1.2.2
    rcases hK with ⟨h0, p0, k0⟩ | ⟨h1, p1, k1⟩ <;>
      rcases hK' with ⟨h0', p0', k0'⟩ | ⟨h1', p1', k1'⟩ <;> try omega
    · refine ⟨by omega, fun ke kf hke hkf => ?_⟩
      rw [k0, Kind.tc.injEq] at hke
      rw [k0', Kind.tc.injEq] at hkf
      subst hke hkf
      simp only [Startup.tmemWordLoc, hcta, tcStatic]
    · refine ⟨by omega, fun ke kf hke hkf => ?_⟩
      rw [k1, Kind.tc.injEq] at hke
      rw [k1', Kind.tc.injEq] at hkf
      subst hke hkf
      rfl
  · -- a startup lane and a warpgroup-0 lane
    change e.pc = d0.site.pc at hpc
    obtain ⟨hK, hW0⟩ := tc_start hp hX hFw hnu hw hg hc hk hσ hxd hev hpc
    exact (tc_mixed hp hX hFw hnu hsw (by omega) hW0 hσ' hk3.le hwh).elim
  · -- a warpgroup-0 lane and a startup lane
    change e'.pc = s0.site.pc at hpc'
    obtain ⟨hK, hW0⟩ := tc_start hp hX hFw hnu hwh hh hc' hk' hσ' hxs hev' hpc'
    exact (tc_mixed hp hX hFw hnu hsw' (by omega) hW0 hσ hk2.le hw).elim
  · -- two warpgroup-0 lanes
    obtain ⟨hcd, hKd⟩ := hev
    obtain ⟨hcs, hKs⟩ := hev'
    have hsldg := w0_sldArm hFw hnu hw hg hj hσ
    have hsldh := w0_sldArm hFw hnu hwh hh hi hσ'
    have htcd : d.site.isTc = true := by rw [← Wg0.evK_tc hub hKd]; exact hc
    have htcs : s.site.isTc = true := by rw [← Wg0.evK_tc hub' hKs]; exact hc'
    have hpl : Wg0.place d = Wg0.place s := by
      rcases le_total (Wg0.place d) (Wg0.place s) with hle | hle
      · rcases w0_tcKey hp hX hFw hnu hw hsw hσ htcd hk2 hσ' hle with ⟨-, h2⟩ | ⟨h1, -⟩
        · omega
        · exact h1.symm
      · rcases w0_tcKey hp hX hFw hnu hwh hsw' hσ' htcs hk3 hσ hle with ⟨-, h2⟩ | ⟨h1, -⟩
        · omega
        · exact h1
    have hR : Wg0.rounds s.l0 s.l1 = Wg0.rounds d.l0 d.l1 := by
      rw [Wg0.rounds_blocks hL' (Wg0.lens_two (Wg0.tc_reg htcs)),
        Wg0.rounds_blocks hL (Wg0.lens_two (Wg0.tc_reg htcd)), hsw.1.2.2]
    have hsite := Wg0.tc_place_inj hC hC' hR htcd htcs hpl
    have hsite' : d.site = s.site ∨ ∃ a a' k, d.site = .sld a k ∧ s.site = .sld a' k := hsite
    refine ⟨?_, fun ke kf hke hkf => ?_⟩
    · rw [hcd, hcs]
      rcases hsite' with h1 | ⟨a, a', k0, h1, h2⟩
      · rw [h1]
      · rw [h1, h2, hsldg a k0 h1, hsldh a' k0 h2, hWe]
    · rw [evK_static hKd hub hc hke, evK_static hKs hub' hc' hkf]
      rcases hsite' with h1 | ⟨a, a', k0, h1, h2⟩
      · rw [h1]
      · rw [h1, h2]; rfl

/-- **No lane of a warp exits with at most `k` collective `tcgen05` events while another lane of
the warp makes its `k`-th.** -/
theorem tc_unexited (hsw : SameWarp L g h) {j k f pc : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hc : isTcColl e = true)
    (hk : ((X.tr g).take j).countP isTcColl = k) (hx : X.get (h, f) = some ⟨pc, .exit⟩)
    (hle : (X.tr h).countP isTcColl ≤ k) : False := by
  have hg : g < L.threads := hsw.1.1
  have hh : h < L.threads := hsw.1.2.1
  have hw := tc_warp hp hX hFw hg he hc
  obtain ⟨hwe, -⟩ := warpW_same hp hsw
  have hwh : warp L h < 4 := hwe ▸ hw
  have hsw' : SameWarp L h g := ⟨⟨hh, hg, hsw.1.2.2.symm⟩, hsw.2.symm⟩
  have hk2 : tcCnt X g j = k := hk
  have hub := noUb_kind hnu he
  have hubx := noUb_kind hnu hx
  obtain ⟨σ, hσ, -, -, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨σ', hσ', -, -, hev', -⟩ := ev_at hp hX hFw hx hubx
  have hfl : tcCnt X h f ≤ k := Nat.le_trans (List.take_sublist f (X.tr h)).countP_le hle
  rcases w0_bst hFw hnu hwh hh hσ' with ⟨s0, m0, rfl, hxs⟩ | ⟨s, n', rfl, hC', hL', -⟩
  · exact start_noExit hxs hev' rfl
  obtain ⟨-, hKs⟩ := hev'
  have hexit : s.site = .exit := Proof.Wg0.evK_exit hKs rfl
  rcases w0_bst hFw hnu hw hg hσ with ⟨d0, n0, rfl, hxd⟩ | ⟨d, n, rfl, hC, hL, -⟩
  · change e.pc = d0.site.pc at hpc
    obtain ⟨hK, hW0⟩ := tc_start hp hX hFw hnu hw hg hc hk2 hσ hxd hev hpc
    have hk1 : k ≤ 1 := by rcases hK with ⟨h0, -⟩ | ⟨h1, -⟩ <;> omega
    exact tc_mixed hp hX hFw hnu hsw hk1 hW0 hσ' hfl hwh
  · obtain ⟨-, hKd⟩ := hev
    have hj : j ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
    have htcd : d.site.isTc = true := by rw [← Wg0.evK_tc hub hKd]; exact hc
    have hpl : Wg0.place d ≤ Wg0.place s := by
      have h1 := Wg0.place_le hC
      have h2 : Wg0.place s = Wg0.top := by simp [Wg0.place, hexit, Wg0.top]
      omega
    rcases w0_tcKey hp hX hFw hnu hw hsw hσ htcd hk2 hσ' hpl with ⟨-, h2⟩ | ⟨-, h2, -⟩
    · omega
    · rw [hexit] at h2
      cases h2

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
