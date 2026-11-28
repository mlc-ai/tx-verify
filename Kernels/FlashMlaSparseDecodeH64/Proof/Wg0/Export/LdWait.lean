-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Counted
public import Lemmas.Flow.Polls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # A load of warpgroup 0 is waited for

A tensor load of warpgroup 0 (`tcgen05.ld`) is followed, with no other event of the lane between,
by its `tcgen05.wait::ld`: the machine steps from `sld arm 1`, `rld c` and `old c` to the
site of the wait, and from `sld arm 0` to `sld arm 1` (`wg0_ldNext`). So a lane with a later
event that is a barrier event has a wait between the load and that event (`wg0_ldWait`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A site whose event is a Tensor Memory load is a load site. -/
private theorem ld_site {g : Nat} {w : BitVec 64} {d : Wg0.Control.D} {e : Event} {a : Nat}
    {vals : List Value} {sh : TcShape} (h : Wg0.EvK P L g w d e)
    (hk : e.kind = .tc (.ld a vals sh)) :
    (∃ a0 k, d.site = .sld a0 k) ∨ (∃ c, d.site = .rld c) ∨ ∃ c, d.site = .old c := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp [Wg0.EvK, Wg0.PollEv, Wg0.ArrEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
    Wg0.TcLdEv, Wg0.TcStEv, hk] at h ⊢

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- The state after a load of warpgroup 0 is the one of the successor site. -/
private theorem ld_succ {h k pc a : Nat} {vals : List Value} {sh : TcShape} {f' : Event}
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : MbarRow.Wg0At L h pc)
    (hf' : X.get (h, k + 1) = some f') (hu' : ∀ fl, f'.kind ≠ .ub fl) :
    ∃ d s', Wg0.Ev P L h (warpW L h) d ⟨pc, .tc (.ld a vals sh)⟩ ∧
      Wg0.Ev P L h (warpW L h) { d with site := s' } f' ∧
      ((∃ a0, d.site = .sld a0 0 ∧ s' = .sld a0 1) ∨
        ((∀ a0, d.site ≠ .sld a0 0) ∧ (s' = .sldw ∨ ∃ c, s' = .rldw c ∨ s' = .oldw c))) := by
  have hub : ∀ fl, (⟨pc, .tc (.ld a vals sh)⟩ : Event).kind ≠ .ub fl := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hld hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc ⟨hat.2.1, hat.2.2⟩
  have hk := hE.2
  obtain ⟨s', hn, hcase⟩ : ∃ s', Wg0.Control.succ P L h (warpW L h) d ⟨pc, .tc (.ld a vals sh)⟩ =
      some (some { d with site := s' }) ∧
      ((∃ a0, d.site = .sld a0 0 ∧ s' = .sld a0 1) ∨
        ((∀ a0, d.site ≠ .sld a0 0) ∧ (s' = .sldw ∨ ∃ c, s' = .rldw c ∨ s' = .oldw c))) := by
    rcases ld_site hk rfl with ⟨a0, k0, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩
    · fin_cases k0
      · exact ⟨.sld a0 1, by simp [Wg0.Control.succ, hs, Wg0.Control.tcLoad], .inl ⟨a0, hs, rfl⟩⟩
      · exact ⟨.sldw, by simp [Wg0.Control.succ, hs, Wg0.Control.tcLoad],
          .inr ⟨fun a1 h1 => by rw [hs] at h1; simp at h1, .inl rfl⟩⟩
    · exact ⟨.rldw c, by simp [Wg0.Control.succ, hs, Wg0.Control.tcLoad],
        .inr ⟨fun a1 h1 => by rw [hs] at h1; simp at h1, .inr ⟨c, .inl rfl⟩⟩⟩
    · exact ⟨.oldw c, by simp [Wg0.Control.succ, hs, Wg0.Control.tcLoad],
        .inr ⟨fun a1 h1 => by rw [hs] at h1; simp at h1, .inr ⟨c, .inr rfl⟩⟩⟩
  have hσ' : Frame.stateAt (thread P L) X h (k + 1) =
      some (some (.inr ⟨.inl .wg0, { d with site := s' }⟩,
        Code.bump cls n ⟨pc, .tc (.ld a vals sh)⟩)) := by
    have hn' : (frag P L h .wg0).next d ⟨pc, .tc (.ld a vals sh)⟩ =
        some (some { d with site := s' }) := hn
    rw [Frame.stateAt_succ hld, hσ]
    show (thread P L h).next _ _ = _
    rw [next_frag, hn']
    rfl
  obtain ⟨σ', hσ'', hJ', hi', hev', hpc'⟩ := ev_at hp hX hFw hf' hu'
  rw [hσ'] at hσ''
  obtain rfl := Option.some.inj (Option.some.inj hσ'')
  have hr : 103 ≤ f'.pc ∧ f'.pc < 1842 := by
    rw [hpc']
    show 103 ≤ s'.pc ∧ s'.pc < 1842
    rcases hcase with ⟨a0, -, rfl⟩ | ⟨-, rfl | ⟨c, rfl | rfl⟩⟩
    · cases a0 <;> simp [Wg0.Site.pc]
    · simp [Wg0.Site.pc]
    all_goals fin_cases c <;> simp [Wg0.Site.pc]
  obtain ⟨d', n', ⟨⟩, -, hE', -⟩ := wg0_state hJ' hi' hev' hpc' hr
  exact ⟨d, s', hE, hE', hcase⟩

theorem wg0_ldNext {h k pc a : Nat} {vals : List Value} {sh : TcShape} {f' : Event}
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : MbarRow.Wg0At L h pc)
    (hf' : X.get (h, k + 1) = some f') (hu' : ∀ fl, f'.kind ≠ .ub fl) :
    ((pc = 278 ∨ pc = 283) ∧ ∃ a' vals' sh', f' = ⟨pc + 2, .tc (.ld a' vals' sh')⟩) ∨
      ((pc ≠ 278 ∧ pc ≠ 283) ∧ ∃ pc', f' = ⟨pc', .tc .waitLd⟩) := by
  obtain ⟨d, s', hE, hE', hcase⟩ := ld_succ hp hX hFw hld hat hf' hu'
  obtain ⟨hpd, hk⟩ := hE
  obtain ⟨hpf, hk'⟩ := hE'
  rcases hcase with ⟨a0, hs, rfl⟩ | ⟨hns, hs'⟩
  · left
    rw [hs] at hpd
    simp only [Wg0.EvK, Wg0.TcLdEv] at hk'
    obtain ⟨vals', hv⟩ | ⟨fl, hv⟩ := hk'
    · refine ⟨?_, 432, vals', .s32x32b, ?_⟩
      · cases a0 <;> simp [Wg0.Site.pc] at hpd <;> omega
      · obtain ⟨pc', kd⟩ := f'
        simp only at hv hpf
        subst hv
        rw [hpf]
        cases a0 <;> simp [Wg0.Site.pc] at hpd <;> subst hpd <;> rfl
    · exact absurd hv (hu' fl)
  · right
    refine ⟨?_, ?_⟩
    · rcases ld_site hk rfl with ⟨a1, k1, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩ <;> rw [hs] at hpd
      · fin_cases k1
        · exact absurd hs (hns a1)
        · cases a1 <;> simp [Wg0.Site.pc] at hpd <;> omega
      · fin_cases c <;> simp [Wg0.Site.pc] at hpd <;> omega
      · fin_cases c <;> simp [Wg0.Site.pc] at hpd <;> omega
    · obtain ⟨pc', kd⟩ := f'
      refine ⟨pc', ?_⟩
      simp only [Wg0.EvK] at hk'
      rcases hs' with rfl | ⟨c, rfl | rfl⟩ <;> simp only at hk' <;> rw [hk']

omit hp hFw in
/-- The event after another event before a later event of the lane is no undefined behaviour,
if the later event is none. -/
private theorem next_ev {h j e : Nat} {f : Event}
    (hf : X.get (h, e) = some f) (hu : ∀ fl, f.kind ≠ .ub fl) (hj : j < e) :
    ∃ f', X.get (h, j + 1) = some f' ∧ ∀ fl, f'.kind ≠ .ub fl := by
  have hlen : e < (X.tr h).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨f', hf'⟩ : ∃ f', X.get (h, j + 1) = some f' :=
    ⟨_, List.getElem?_eq_getElem (l := X.tr h) (by omega)⟩
  refine ⟨f', hf', fun fl hfl => ?_⟩
  obtain ⟨pc'', kd⟩ := f'
  simp only at hfl
  subst hfl
  have hle := ub_last hX hf' hf
  obtain rfl : e = j + 1 := by omega
  rw [hf] at hf'
  cases hf'
  exact hu fl rfl

/-- **A load of warpgroup 0 is waited for** before any later event of the lane that is neither
undefined behaviour nor a `tcgen05` event: its `tcgen05.wait::ld` lies between them. -/
theorem wg0_ldWaitAt {h k e pc a : Nat} {vals : List Value} {sh : TcShape} {f : Event}
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : MbarRow.Wg0At L h pc)
    (hf : X.get (h, e) = some f) (hu : ∀ fl, f.kind ≠ .ub fl) (hnt : ∀ c, f.kind ≠ .tc c)
    (hke : k < e) :
    ∃ w pc', k < w ∧ w < e ∧ X.get (h, w) = some ⟨pc', .tc .waitLd⟩ := by
  obtain ⟨f', hf', hu'⟩ := next_ev hX hf hu hke
  rcases wg0_ldNext hp hX hFw hld hat hf' hu' with
    ⟨hpc, a', vals', sh', rfl⟩ | ⟨-, pc', rfl⟩
  · have hk1 : k + 1 < e := by
      rcases Nat.lt_or_ge (k + 1) e with h1 | h1
      · exact h1
      · obtain rfl : e = k + 1 := by omega
        rw [hf'] at hf
        cases hf
        exact (hnt _ rfl).elim
    obtain ⟨f'', hf'', hu''⟩ := next_ev hX hf hu hk1
    have hat' : MbarRow.Wg0At L h (pc + 2) := by
      obtain ⟨hw, h1, h2⟩ := hat
      refine ⟨hw, ?_, ?_⟩ <;> omega
    rcases wg0_ldNext hp hX hFw hf' hat' hf'' hu'' with ⟨hpc2, -⟩ | ⟨-, pc'', rfl⟩
    · omega
    · refine ⟨k + 2, pc'', by omega, ?_, hf''⟩
      rcases Nat.lt_or_ge (k + 2) e with h1 | h1
      · exact h1
      · obtain rfl : e = k + 2 := by omega
        rw [hf''] at hf
        cases hf
        exact (hnt _ rfl).elim
  · refine ⟨k + 1, pc', by omega, ?_, hf'⟩
    rcases Nat.lt_or_ge (k + 1) e with h1 | h1
    · exact h1
    · obtain rfl : e = k + 1 := by omega
      rw [hf'] at hf
      cases hf
      exact (hnt _ rfl).elim

/-- **A load of warpgroup 0 is waited for** before a later barrier event of the lane: its
`tcgen05.wait::ld` lies between them. -/
theorem wg0_ldWait {h k e pc a id : Nat} {vals : List Value} {sh : TcShape} {f : Event}
    {cnt : Option Nat} {md : BarMode}
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : MbarRow.Wg0At L h pc)
    (hf : X.get (h, e) = some f) (hb : f.kind = .bar id cnt md) (hke : k < e) :
    ∃ w pc', k < w ∧ w < e ∧ X.get (h, w) = some ⟨pc', .tc .waitLd⟩ :=
  wg0_ldWaitAt hp hX hFw hld hat hf (fun _ h => by rw [hb] at h; cases h)
    (fun _ h => by rw [hb] at h; cases h) hke


/-- **The block of a load of the loop**: a load of warpgroup 0 at a score or rescale site of
block `r` has polled `qkDone j` once per use among blocks `0 … r` and arrived on `soReady j`
once per use among blocks `0 … r - 1`; a rescale load (a column below 400) is of a block `r ≥ 1`
(the rescale arm runs only past the first block, `ArmOk`); any other load is an output load, after
the lane's poll of `svDone` at pc 1184. -/
theorem wg0_ldPlace {h k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : MbarRow.Wg0At L h pc) :
    (∃ r, (a < 400 → 1 ≤ r) ∧ (400 ≤ a → vals.length = 32) ∧ ∀ j : Fin 2,
      okPolls (mbarLoc L (h / L.block) (.qkDone j)) ((X.tr h).take k) = ringUses 2 j (r + 1) ∧
      arrivals (mbarLoc L (h / L.block) (.soReady j)) ((X.tr h).take k) = ringUses 2 j r) ∨
    a < 400 ∧ ∃ jw p, jw < k ∧ X.get (h, jw) = some ⟨1184, .wait (mbarLoc L (h / L.block)
      (.svDone (slot2 (blocksOf P L (h / L.block) - 1)))) p true true .cta⟩ := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc (.ld a vals sh)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hRn, ⟨hpd, hk⟩, -⟩ := wg0_state hJ hi hev hpc ⟨hlo, hhi⟩
  have hR := hRn (state_ub hX hσ he)
  rw [show (fun c => n (.wg0 c)) = fun c => ((X.tr h).take k).countP (Wg0.cls c) from
    funext fun c => state_count hσ (.wg0 c)] at hR
  obtain ⟨-, -, -, hA⟩ := w0_tc hp hX hFw hw (Frame.lt_of_get hX he) k
    (noUbBefore_of_get hX he) _ hσ
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  rcases ld_site hk rfl with ⟨a0, k0, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩
  · left
    simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
    obtain ⟨r, -, hq, ha⟩ := hc
    dsimp only at hq ha
    have hlt : ¬ a < 400 := by
      have := hk
      simp only [hs, Wg0.EvK, Wg0.TcLdEv] at this
      rcases this with ⟨vs, hv⟩ | ⟨f, hf⟩
      · simp only [Kind.tc.injEq, TcKind.ld.injEq] at hv
        omega
      · exact absurd hf (hub f)
    refine ⟨r, fun h' => absurd h' hlt, fun _ => ?_, fun j => ⟨?_, ?_⟩⟩
    · refine scoreLdLen hp hX he rfl ?_
      rw [hpd, hs]
      cases a0 <;> fin_cases k0 <;> simp [Wg0.Site.pc]
    · rw [show mbarLoc L (h / L.block) (.qkDone j) = loc L h (.qkDone j) from rfl,
        wg0_okPolls hp hX hFw hw, hq, Wg0.acq_qk hp]
      have := j.isLt
      unfold Wg0.use Wg0.ind ringUses
      split_ifs <;> omega
    · rw [show mbarLoc L (h / L.block) (.soReady j) = loc L h (.soReady j) from rfl,
        wg0_arrivals hp hX hFw hw, ha, Wg0.arr_so hp]
  · left
    simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
    obtain ⟨r, ⟨-, hRo, hrR, hbi, -⟩, hq, ha⟩ := hc
    dsimp only at hq ha
    have hlt : ¬ 400 ≤ a := by
      have := hk
      simp only [hs, Wg0.EvK, Wg0.TcLdEv] at this
      rcases this with ⟨vs, hv⟩ | ⟨f, hf⟩
      · simp only [Kind.tc.injEq, TcKind.ld.injEq] at hv
        have := c.isLt
        omega
      · exact absurd hf (hub f)
    refine ⟨r, fun _ => ?_, fun h' => absurd h' hlt, fun j => ⟨?_, ?_⟩⟩
    · have hv := hA (by rw [hs]; rfl)
      simp only [Wg0.armV, Wg0.Control.D.words] at hv hbi hRo hrR
      by_contra h0
      obtain rfl : r = 0 := by omega
      rw [hbi, Arith32.scmpi_eq_b_W (n := 1) (by omega) (by omega) (by omega)] at hv
      simp at hv
    · rw [show mbarLoc L (h / L.block) (.qkDone j) = loc L h (.qkDone j) from rfl,
        wg0_okPolls hp hX hFw hw, hq, Wg0.acq_qk hp]
      have := j.isLt
      unfold Wg0.use Wg0.ind ringUses
      split_ifs <;> omega
    · rw [show mbarLoc L (h / L.block) (.soReady j) = loc L h (.soReady j) from rfl,
        wg0_arrivals hp hX hFw hw, ha, Wg0.arr_so hp]
  · right
    have hpc : d.site.pc = pc := hpd.symm
    rw [hs] at hpc
    refine ⟨?_, wg0_old_poll hp hX hFw hw he ⟨c.val, c.isLt, by
      rw [← hpc]; simp only [Wg0.Site.pc]⟩ ⟨hlo, hhi⟩⟩
    have := hk
    simp only [hs, Wg0.EvK, Wg0.TcLdEv] at this
    rcases this with ⟨vs, hv⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.ld.injEq] at hv
      have := c.isLt
      omega
    · exact absurd hf (hub f)

/-- **The block of a rescale load**: the load of chunk `c` of a lane of warpgroup 0 is of a block
`r ≥ 1`, with the polls of `qkDone j` and the arrivals on `soReady j` of `wg0_ldPlace`. -/
theorem wg0_rldPlace (c : Fin 4) {h k a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩)
    (hw : MbarRow.warp L h < 4) :
    ∃ r, 1 ≤ r ∧ ∀ j : Fin 2,
      okPolls (mbarLoc L (h / L.block) (.qkDone j)) ((X.tr h).take k) = ringUses 2 j (r + 1) ∧
      arrivals (mbarLoc L (h / L.block) (.soReady j)) ((X.tr h).take k) = ringUses 2 j r := by
  have hrng : ∀ c : Fin 4, 103 ≤ [716, 817, 918, 1019].getD c.val 0 ∧
      [716, 817, 918, 1019].getD c.val 0 < 1842 := by decide
  have hat : MbarRow.Wg0At L h ([716, 817, 918, 1019].getD c.val 0) :=
    ⟨hw, (hrng c).1, (hrng c).2⟩
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩ : Event).kind ≠
      .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hRn, ⟨hpd, hk⟩, -⟩ := wg0_state hJ hi hev hpc ⟨hlo, hhi⟩
  have hR := hRn (state_ub hX hσ he)
  rw [show (fun c => n (.wg0 c)) = fun c => ((X.tr h).take k).countP (Wg0.cls c) from
    funext fun c => state_count hσ (.wg0 c)] at hR
  obtain ⟨-, -, -, hA⟩ := w0_tc hp hX hFw hw (Frame.lt_of_get hX he) k
    (noUbBefore_of_get hX he) _ hσ
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  rcases ld_site hk rfl with ⟨a0, k0, hs⟩ | ⟨c', hs⟩ | ⟨c', hs⟩
  · exfalso
    rw [hs] at hpd
    cases a0 <;> fin_cases k0 <;> fin_cases c <;> simp [Wg0.Site.pc] at hpd
  · simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
    obtain ⟨r, ⟨-, hRo, hrR, hbi, -⟩, hq, ha⟩ := hc
    dsimp only at hq ha
    refine ⟨r, ?_, fun j => ⟨?_, ?_⟩⟩
    · have hv := hA (by rw [hs]; rfl)
      simp only [Wg0.armV, Wg0.Control.D.words] at hv hbi hRo hrR
      by_contra h0
      obtain rfl : r = 0 := by omega
      rw [hbi, Arith32.scmpi_eq_b_W (n := 1) (by omega) (by omega) (by omega)] at hv
      simp at hv
    · rw [show mbarLoc L (h / L.block) (.qkDone j) = loc L h (.qkDone j) from rfl,
        wg0_okPolls hp hX hFw hw, hq, Wg0.acq_qk hp]
      have := j.isLt
      unfold Wg0.use Wg0.ind ringUses
      split_ifs <;> omega
    · rw [show mbarLoc L (h / L.block) (.soReady j) = loc L h (.soReady j) from rfl,
        wg0_arrivals hp hX hFw hw, ha, Wg0.arr_so hp]
  · exfalso
    rw [hs] at hpd
    fin_cases c' <;> fin_cases c <;> simp [Wg0.Site.pc] at hpd

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
