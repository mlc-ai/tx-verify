-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.RowMem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileBlk
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrStep
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.PageWord
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every block state of a loader lane has its rows' words (`row_inv`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

set_option maxHeartbeats 4000000 in
/-- **Every block state of a loader lane has its rows' words.** -/
theorem row_inv {bb : Nat} (hlo : tilePrefix p bb * p.heads ≤ g / L.block)
    (hhi : g / L.block < tilePrefix p (bb + 1) * p.heads) : ∀ k, k ≤ (X.tr g).length → ∀ b d n,
    Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
    d.site.blk = true → RowInv p bb L X g k d := by
  refine pos_at (I := fun k d => d.site.blk = true → RowInv p bb L X g k d)
    (fun k b h => by simp [Site.blk, bc] at h)
    (fun k b d n e d' he hσ hub hJ hF hev hnu hn hm IH => ?_) hp hX hg hw
  intro hb'
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hIH := fun h => IH k le_rfl b d n hσ hub h
  have hsame : ∀ f, wr d.site f = false → f.same d.v d'.v := hm.keep
  have hA : ∀ j ≤ k, ∀ b d n, Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) →
      n .ub = 0 → AddrOk p L X g j d := fun j hj b d n hσ hub =>
    addr_ok hp hX hg hw j (hj.trans hkl.le) b d n hσ hub
  have hin := fun h => step_in hm hn h hb'
  have hkeep := fun h => step_keep hm hev hn h hb'
  -- the writes of the step
  have hwr : ∀ a bs, X.Writes (g, k) a bs → e.kind = .wr a bs := by
    rintro a bs ⟨pc, h⟩
    rw [show X.get (g, k) = some e from he] at h
    cases h
    rfl
  -- a store's word survives every other step
  have hmono : ∀ {o : Nat} {bs : List Byte}, Mem L X g k o bs →
      (∀ per it, d.site = .pgSt per it → o ≠ 96 + 4 * it.val) →
      (∀ per it, d.site = .rwSt per it → o ≠ 64 + 4 * it.val) →
      (∀ per c it, d.site = .ptS per c it → o ≠ lwO per c it) → Mem L X g (k + 1) o bs := by
    intro o bs h h1 h2 h3
    refine h.mono fun a bs' hw' hl => ?_
    rcases wr_exact hp hev (hwr _ _ hw') with ⟨per, it, hs, hl', -⟩ | ⟨per, it, hs, hl', -⟩ |
      ⟨per, c, it, hs, hl', -⟩
    · rw [hl] at hl'
      simp only [Loc.mk.injEq, true_and] at hl'
      exact h1 per it hs (by omega)
    · rw [hl] at hl'
      simp only [Loc.mk.injEq, true_and] at hl'
      exact h2 per it hs (by omega)
    · rw [hl] at hl'
      simp only [Loc.mk.injEq, true_and] at hl'
      exact h3 per c it hs (by omega)
  have haft := fun h => aft_prev (n14 := not14 (wOf b)) (s := d.site) (s' := d'.site) h
  have hlw : ∀ per c (it : Fin 2), lwO per c it < 64 := by
    intro per c it
    cases per <;> cases c <;> fin_cases it <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the page word
    intro per it hs'
    by_cases hl : ∃ per0 it0, d.site = .pgLd per0 it0
    · obtain ⟨per0, it0, hl⟩ := hl
      have hbk : d.site.blk = true := by rw [hl]; cases per0 <;> rfl
      have hpp : per0 = per ∧ it0 = it := by
        rcases hm.edge with h | h
        · simp only at h; rw [hs', hl] at h; cases h
        · have hc := pt_edges.ok h
          simp only [ptChk, hs', hl, Bool.and_eq_true, beq_iff_eq] at hc
          exact ⟨hc.1.symm, hc.2.symm⟩
      obtain ⟨rfl, rfl⟩ := hpp
      obtain ⟨-, k2, k3, -, -, -, -, k8, k9, -⟩ := blk_step hbk (by rw [hl]; rfl) hev hn
      have hK : KeepW d.v d'.v := ⟨k2, k3, k9, k8⟩
      rw [hK.pgW]
      obtain ⟨i, hi, q, hq, hval⟩ := pg_exact hp hX he hσ hF hl
      obtain ⟨b2, hN⟩ := blk_num hp hg hbk hF (tile_inv hp hX hg hw k hkl.le b d n hσ hub hbk)
      obtain rfl := work_unique hN.lo hN.hi hlo hhi
      have hcond : rowCond p L g d.v per0 it0 = false := by
        obtain ⟨-, -, -, -, -, -, -, hrow⟩ := lfits_blk_of hbk hF
        exact hrow per0 it0 hl
      obtain ⟨s, v, kk⟩ := d
      obtain ⟨pc, kind⟩ := e
      simp only at hl
      subst hl
      simp only [succ] at hn
      cases kind <;> simp only [reduceCtorEq] at hn
      split at hn
      · rename_i a bs x hx
        obtain ⟨y, rfl, rfl⟩ := word32_inv hn
        obtain ⟨hv, hci, hqq⟩ := hval _ _ rfl
        rw [hv] at hx
        simp only [Except.ok.injEq, Value.bits.injEq, true_and] at hx
        have hib : i = b2 := by
          have h1 := hci.symm.trans hN.chosen
          have h2 := congrArg BitVec.toNat h1
          have := hp.shape.2.1
          have := hN.batch
          rw [toNat_W (by omega), toNat_W (by omega)] at h2
          exact h2
        subst hib
        unfold pgW
        simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        rw [← hqq, ← hx]
      · simp at hn
    · have hne : d'.site ∈ nexts (not14 (wOf b)) d.site := by
        rcases hm.edge with h | h
        · exfalso
          simp only at h
          rw [hs'] at h
          obtain ⟨s, v, kk⟩ := d
          simp only at h
          subst h
          simp only [succ, Option.some.injEq] at hn
          subst hn
          cases hs'
        · exact h
      obtain ⟨h1, h2⟩ := pg_skip (fun per it h => hl ⟨per, it, h⟩) hne hn per it hs'
      unfold pgW
      rw [h1, h2]
      rfl
  · -- the stored page words
    intro per it hs'
    obtain ⟨hper, hpos⟩ := aft_of hs'
    have hK := hkeep (by omega)
    have hbk := (hin (by omega)).1
    rw [hK.pgW]
    by_cases hst : d.site = .pgSt per it
    · obtain ⟨pc, kind⟩ := e
      obtain ⟨a, bs, rfl⟩ : ∃ a bs, kind = .wr a bs := st_wr hev hnu (by rw [hst]; rfl)
      rcases wr_exact hp hev rfl with ⟨per1, it1, hs, hl, hbs⟩ | ⟨per1, it1, hs, -⟩ |
        ⟨per1, c, it1, hs, -⟩
      · rw [hst] at hs
        cases hs
        rw [← (hIH hbk).pw per it hst, ← hbs]
        exact Mem.new ⟨pc, he⟩ hl
      · rw [hst] at hs; cases hs
      · rw [hst] at hs; cases hs
    · have haf : aftPg per it d.site = true := by
        rcases hm.edge with h | h
        · exact h ▸ hs'
        · exact (((haft h per).2 it).1 hs').resolve_right hst
      refine hmono ((hIH hbk).pg per it haf) ?_ ?_ ?_
      · intro per1 it1 hs heq
        obtain ⟨hper1, hpos1⟩ := aft_of haf
        rw [hs] at hper1 hpos1
        simp only [perOf, Option.some.injEq] at hper1
        simp only [blkPos] at hpos1
        omega
      · intro per1 it1 hs heq
        omega
      · intro per1 c it1 hs heq
        have := hlw per1 c it1
        omega
  · -- the stored rows
    intro per it hs'
    obtain ⟨hper, hpos⟩ := aft_of hs'
    have hK := hkeep (by omega)
    have hbk := (hin (by omega)).1
    rw [hK.rwW]
    by_cases hst : d.site = .rwSt per it
    · obtain ⟨pc, kind⟩ := e
      obtain ⟨a, bs, rfl⟩ : ∃ a bs, kind = .wr a bs := st_wr hev hnu (by rw [hst]; rfl)
      rcases wr_exact hp hev rfl with ⟨per1, it1, hs, -⟩ | ⟨per1, it1, hs, hl, hbs⟩ |
        ⟨per1, c, it1, hs, -⟩
      · rw [hst] at hs; cases hs
      · rw [hst] at hs
        cases hs
        rw [← hbs]
        exact Mem.new ⟨pc, he⟩ hl
      · rw [hst] at hs; cases hs
    · have haf : aftRw per it d.site = true := by
        rcases hm.edge with h | h
        · exact h ▸ hs'
        · exact (((haft h per).2 it).2.1 hs').resolve_right hst
      refine hmono ((hIH hbk).rw per it haf) ?_ ?_ ?_
      · intro per1 it1 hs heq
        omega
      · intro per1 it1 hs heq
        obtain ⟨hper1, hpos1⟩ := aft_of haf
        rw [hs] at hper1 hpos1
        simp only [blkPos] at hpos1
        omega
      · intro per1 c it1 hs heq
        have := hlw per1 c it1
        omega
  · -- the page word a pointer round reads
    intro per c it hs'
    have hpos : 1 < blkPos d'.site := by
      rcases hs' with h | h <;> rw [h] <;> cases c <;> simp only [blkPos] <;> simp <;> omega
    have hK := hkeep hpos
    have hbk := (hin hpos).1
    rw [hK.pgW]
    by_cases hst : d.site = .ptP per c it
    · have haf : aftPg per it d.site = true := by
        rw [hst]
        cases c <;> fin_cases it <;> simp [aftPg, perOf, blkPos]
      have hM := (hIH hbk).pg per it haf
      obtain ⟨s, vv, kk⟩ := d
      simp only at hst
      subst hst
      obtain ⟨pc, kind⟩ := e
      obtain ⟨a, bs, hk, hl, hz⟩ := ptP_loc hp hev
      simp only at hk
      subst hk
      obtain ⟨j, a', bs', hL, ⟨o, ho, hS⟩, hlen, hb⟩ := load_at hp hX hg hw he hσ hJ hA
        (o := 96 + 4 * it.val) (q := 0) (by rw [hl]; rfl) hz (.inl rfl)
        (by fin_cases it <;> simp [lstOffs]) (fun kk A => lst_ptP per c it kk A)
      have hbs' := hM.eq hL
      have hlo' := hL.2.2.1
      rw [hlo'] at ho
      simp only [Loc.mk.injEq, true_and] at ho
      have hit := it.isLt
      rcases hS with ⟨-, -, x, hpg, hxx⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · obtain rfl := bits_inj (.inl rfl) (hxx.symm.trans hbs')
        simp only [succ] at hn
        split at hn
        · rename_i z hx
          obtain ⟨y, rfl, rfl⟩ := word32_inv hn
          rw [hxx] at hb
          have := rebuild_lt hlen hb (by have := hpg.2; omega) hx
          exact BitVec.eq_of_toNat_eq this
        · simp at hn
      · omega
      · omega
    · have hst' : d.site = .ptR per c it ∨ d.site = .ptS per c it := by
        rcases hm.edge with h | h
        · rcases hs' with h' | h'
          · exact .inl (h.symm.trans h')
          · exact .inr (h.symm.trans h')
        · have hc := pt_edges.ok h
          rcases hs' with h' | h' <;> simp only [ptChk, h', beq_iff_eq] at hc
          · exact (hst hc).elim
          · exact .inl hc
      have hlp : d'.v.lp = d.v.lp := hsame .lp (by
        rcases hst' with h | h <;> rw [h] <;> rfl)
      rw [hlp]
      exact (hIH hbk).lp per c it hst'
  · -- the row a pointer round reads
    intro per c it hs'
    have hpos : 1 < blkPos d'.site := by
      rw [hs']; cases c <;> simp only [blkPos] <;> simp <;> omega
    have hK := hkeep hpos
    have hbk := (hin hpos).1
    rw [hK.rwW]
    by_cases hst : d.site = .ptR per c it
    · have haf : aftRw per it d.site = true := by
        rw [hst]
        cases c <;> fin_cases it <;> simp [aftRw, perOf, blkPos]
      have hM := (hIH hbk).rw per it haf
      obtain ⟨s, vv, kk⟩ := d
      simp only at hst
      subst hst
      obtain ⟨pc, kind⟩ := e
      obtain ⟨a, bs, hk, hl, hz⟩ := ptR_loc hp hev
      simp only at hk
      subst hk
      obtain ⟨j, a', bs', hL, ⟨o, ho, hS⟩, hlen, hb⟩ := load_at hp hX hg hw he hσ hJ hA
        (o := 64 + 4 * it.val) (q := 0) (by rw [hl]; rfl) hz (.inl rfl)
        (by fin_cases it <;> simp [lstOffs]) (fun kk A => lst_ptR per c it kk A)
      have hbs' := hM.eq hL
      have hlo' := hL.2.2.1
      rw [hlo'] at ho
      simp only [Loc.mk.injEq, true_and] at ho
      have hit := it.isLt
      rcases hS with ⟨h, -⟩ | ⟨-, -, x, hr, hxx⟩ | ⟨h, -⟩
      · omega
      · obtain rfl := bits_inj (.inl rfl) (hxx.symm.trans hbs')
        simp only [succ] at hn
        split at hn
        · rename_i z hx
          obtain ⟨y, rfl, rfl⟩ := word32_inv hn
          rw [hxx] at hb
          have := rebuild_lt hlen hb (by unfold RowV at hr; omega) hx
          exact BitVec.eq_of_toNat_eq this
        · simp at hn
      · omega
    · have hst' : d.site = .ptS per c it := by
        rcases hm.edge with h | h
        · exact h.symm.trans hs'
        · have hc := pt_edges.ok h
          simp only [ptChk, hs', beq_iff_eq] at hc
          exact (hst hc).elim
      have hlr : d'.v.lr = d.v.lr := hsame .lr (by rw [hst']; rfl)
      rw [hlr]
      exact (hIH hbk).lr per c it hst'
  · -- the stored addresses
    intro per c it hs'
    have hs0 := hs'
    simp only [aftPt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs0
    have hpos : 1 < blkPos d'.site := by
      have := hs0.1.2
      cases c <;> simp at this <;> omega
    have hK := hkeep hpos
    have hbk := (hin hpos).1
    rw [hK.adW]
    by_cases hst : d.site = .ptS per c it
    · obtain ⟨pc, kind⟩ := e
      obtain ⟨a, bs, rfl⟩ : ∃ a bs, kind = .wr a bs := st_wr hev hnu (by rw [hst]; rfl)
      rcases wr_exact hp hev rfl with ⟨per1, it1, hs, -⟩ | ⟨per1, it1, hs, -⟩ |
        ⟨per1, c1, it1, hs, hl, hbs⟩
      · rw [hst] at hs; cases hs
      · rw [hst] at hs; cases hs
      · rw [hst] at hs
        cases hs
        unfold adW
        rw [← (hIH hbk).lp per c it (.inr hst), ← (hIH hbk).lr per c it hst, ← hbs]
        exact Mem.new ⟨pc, he⟩ hl
    · have haf : aftPt per c it d.site = true := by
        rcases hm.edge with h | h
        · exact h ▸ hs'
        · exact (((haft h per).2 it).2.2 c hs').resolve_right hst
      refine hmono ((hIH hbk).ad per c it haf) ?_ ?_ ?_
      · intro per1 it1 hs heq
        have := hlw per c it
        omega
      · intro per1 it1 hs heq
        have := hlw per c it
        omega
      · intro per1 c1 it1 hs heq
        rw [hs] at haf
        exact pt_off_ne haf heq
  · -- between the two words
    intro per c h hs' hk1
    have hpos : 1 < blkPos d'.site := by rw [hs']; cases c <;> simp [blkPos]
    have hK := hkeep hpos
    have hbk := (hin hpos).1
    rw [hK.adW]
    obtain ⟨s, vv, kk⟩ := d
    have hlws : s = .lw per c h := by
      rcases hm.edge with h' | h'
      · exact h'.symm.trans hs'
      · have hc := lw_edges.ok h'
        simp only [lwChk, hs'] at hc
        exfalso
        cases s <;> simp only [Bool.false_eq_true] at hc
        · simp only [succ] at hn
          split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
          · simp at hk1
          · unfold pkStart at hk1; split at hk1
            · simp at hk1
            · split at hk1 <;> simp at hk1
        · simp only [succ] at hn
          repeat' split at hn
          all_goals simp only [Option.some.injEq] at hn
          all_goals subst hn
          all_goals simp at hk1
    subst hlws
    have haf : aftPt per c h (Site.lw per c h) = true := by
      cases c <;> fin_cases h <;> simp [aftPt, perOf, blkPos]
    have hM := (hIH hbk).ad per c h haf
    obtain ⟨pc, kind⟩ := e
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨bs, hk⟩ := hev0
    simp only [succ] at hn
    subst hk
    simp only at hn
    split at hn
    · rename_i z hx
      obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      have hk0 : kk = 0 := by
        by_contra hne
        have : kk.val ≠ 0 := fun h => hne (Fin.ext h)
        rw [ite_eq_right this] at hs'
        simp at hs'
      subst hk0
      simp only [Fin.val_zero, ↓reduceIte] at hs' ⊢
      obtain ⟨j, a', z, hz, hL, hxz⟩ := lw_half hp hX hg hw he hσ hJ hev hA hx
      obtain rfl := bits_inj (.inr rfl) (hM.eq hL)
      simpa using hxz
    · simp at hn
  · -- in a packet's rows
    intro per c h hr'
    have hpos : 1 < blkPos d'.site := by
      revert hr'
      cases d'.site <;> simp only [rowAt, reduceCtorEq, false_implies] <;> intro _ <;>
        simp only [blkPos] <;> split <;> omega
    have hK := hkeep hpos
    have hbk := (hin hpos).1
    rw [hK.adW]
    by_cases hr : rowAt d.site = some (per, c, h)
    · have e0 : d'.v.l0 = d.v.l0 := hsame .l0 (by
        revert hr; cases d.site <;> simp [wr, rowAt])
      have e1 : d'.v.l1 = d.v.l1 := hsame .l1 (by
        revert hr; cases d.site <;> simp [wr, rowAt])
      rw [e0, e1]
      exact (hIH hbk).row per c h hr
    have hlws : d.site = .lw per c h := by
      rcases hm.edge with h' | h'
      · rw [show d'.site = d.site from h'] at hr'
        exact (hr hr').elim
      · have hc := rows_edges.ok h'
        simp only [rowsChk, hr', Bool.or_eq_true, beq_iff_eq] at hc
        exact hc.resolve_left hr
    obtain ⟨s, vv, kk⟩ := d
    simp only at hlws
    subst hlws
    have haf : aftPt per c h (Site.lw per c h) = true := by
      cases c <;> fin_cases h <;> simp [aftPt, perOf, blkPos]
    have hM := (hIH hbk).ad per c h haf
    obtain ⟨pc, kind⟩ := e
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨bs, hk⟩ := hev0
    simp only [succ] at hn
    subst hk
    simp only at hn
    split at hn
    · rename_i z hx
      obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      have hk1 : kk = 1 := by
        by_contra hne
        have : kk.val = 0 := by
          have := kk.isLt
          have : kk.val ≠ 1 := fun h => hne (Fin.ext h)
          omega
        rw [ite_eq_left this] at hr'
        simp [rowAt] at hr'
      subst hk1
      obtain ⟨j, a', z, hz, hL, hxz⟩ := lw_half hp hX hg hw he hσ hJ hev hA hx
      obtain rfl := bits_inj (.inr rfl) (hM.eq hL)
      refine ⟨(hIH hbk).mid per c h rfl rfl, ?_⟩
      show y.toNat = _
      rw [hxz]
      simp only [Fin.val_one]
      norm_num
      omega
    · simp at hn
  · -- the length
    intro per hne hs'
    obtain ⟨hper, hpos⟩ := aft_of hs'
    have hK := hkeep (by omega)
    have hbk := (hin (by omega)).1
    rw [hK.lenW]
    by_cases hst : d.site = .ptS per false 1
    · obtain ⟨s, vv, kk⟩ := d
      simp only at hst
      subst hst
      simp only [succ, Fin.val_one, one_ne_zero, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      simp only [pkStart, hne, ↓reduceIte, Bool.false_eq_true]
      rfl
    · have haf : aftLen per d.site = true := by
        rcases hm.edge with h | h
        · exact h ▸ hs'
        · exact ((haft h per).1 hs').resolve_right hst
      have hl : d'.v.len = d.v.len := by
        by_cases hpt : ∃ per0 c0 it0, d.site = .ptS per0 c0 it0
        · obtain ⟨per0, c0, it0, h0⟩ := hpt
          obtain ⟨hp1, hp2⟩ := aft_of haf
          obtain ⟨s, vv, kk⟩ := d
          simp only at h0
          subst h0
          have hc0 : c0 = true := by
            cases c0
            · have := it0.isLt
              simp only [blkPos] at hp2
              simp at hp2
              omega
            · rfl
          subst hc0
          simp only [succ] at hn
          split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
          · rfl
          · unfold pkStart
            split
            · rfl
            · rfl
        · exact hsame .len (by revert hpt; cases d.site <;> simp [wr])
      rw [hl]
      exact (hIH hbk).len per hne haf


end

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
