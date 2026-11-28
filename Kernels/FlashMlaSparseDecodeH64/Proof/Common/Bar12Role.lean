-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaExit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Measure
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Measure

@[expose] public section

/-! # Barrier 12 in the roles of warps 4–11

The closing `barrier.sync 12` of every role of warps 4–11 (the MMA lane, the TMA lane, the index
warp, the idle code, warpgroup 2) is a site of its own (the role's bar site) followed by the exit
(the idle code's `ret`). Per role:

* the bar site is the only site at the barrier's pc (`*_pcBar`), and an `exit` event is fired only
  at the exit site (`*_evExit`);
* a step from a site before the barrier does not reach the exit (`*_noExit`): the early return of
  a CTA beyond the batch does not happen (`batch_in`); the bar site steps to the exit;
* a site before the barrier is strictly before its place (`*_preLt`: the block counters are below
  the CTA's block count, below `2 ^ 26`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The MMA lane -/

theorem mma_evEnd {d : Mma.D} {e : Event} (hl : ∀ i, d.site ≠ .leave i) (hev : Mma.Ev L g d e)
    (hk : e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) :
    (d.site = .exit ∧ e.kind = .exit) ∨ d.site = .outBar := by
  obtain ⟨-, hK⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  rcases hk with hk | ⟨c, md, hk⟩ <;>
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv, hk] at hK ⊢
  all_goals exact hl _ rfl

theorem mma_noExit (hp : Pre P L m) {d d' : Mma.D} {f : Event}
    (h : Mma.succ P L g d f = some (some d')) (hb : d.site ≠ .outBar) (hx : d.site ≠ .exit) :
    d'.site ≠ .exit := by
  intro hx'
  have hl : ∀ i, d.site ≠ .leave i := by
    intro i hi
    rw [Mma.succ, hi] at h
    simp at h
  by_cases he : d.site = .elect
  · obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    simp only at he
    subst he
    simp only [Mma.succ] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    split_ifs at hx' with h1
    revert hx'
    unfold Mma.leadNext Mma.afterTopk Mma.lensD
    simp only [batch_in hp g, Bool.false_eq_true, ite_false]
    split_ifs <;> simp
  · exact hb (mma_exit_from ⟨he, hl⟩ h hx' hx)

theorem mma_preLt {d : Mma.D} {n : Mma.Cnt → Nat} (hJ : Mma.RefCore L g d n)
    (hb : d.site ≠ .outBar) (hx : d.site ≠ .exit) : Mma.place d < Mma.endPlace := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  have hi := Mma.off_le s
  have hi' := Mma.idx_le s
  simp only at hb hx
  unfold Mma.place
  split
  · rename_i h; exact absurd h hb
  · rename_i h; exact absurd h hx
  · split_ifs with h
    · obtain ⟨⟨-, -, hR', hr, -⟩, -⟩ := (Mma.core_loop h).1 hJ
      simp only at hR' hr ⊢
      simp only [Mma.endPlace, endSlot, mmaOrg, mmaBlk0, loopBase, mmaOff, stride, blockCap,
        mmaPvc] at hi hi' ⊢
      omega
    · cases s <;> simp only [Mma.Site.ord, Mma.endPlace, endSlot, mmaOrg, loopBase, stride,
        blockCap] <;> omega

/-! ### The TMA lane -/

theorem tma_evEnd {d : Tma.D} {e : Event} (hl : ∀ i, d.site ≠ .leave i) (hev : Tma.Ev L g d e)
    (hk : e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) :
    (d.site = .exit ∧ e.kind = .exit) ∨ d.site = .outBar := by
  obtain ⟨-, hK⟩ := hev
  obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  rcases hk with hk | ⟨c, md, hk⟩ <;>
    cases site <;> simp [Tma.EvK, Tma.Poll, Flow.RdAt, hk] at hK ⊢
  all_goals exact hl _ rfl

theorem tma_noExit (hp : Pre P L m) {d d' : Tma.D} {f : Event}
    (h : Tma.succ P L g d f = some (some d')) (hb : d.site ≠ .outBar) (hx : d.site ≠ .exit) :
    d'.site ≠ .exit := by
  intro hx'
  obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  cases site <;>
    simp only [Tma.succ, Tma.electNext, Tma.ncWord, Tma.word32, Tma.poll, Tma.rdAny] at h
  case outBar => exact hb rfl
  case exit => exact hx rfl
  case elect =>
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    split_ifs at hx'
    exact Tma.lead_ne_exit _ (batch_in hp g) hx'
  all_goals (repeat' split at h)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals (try subst h)
  all_goals (try simp [Tma.afterTopk, Tma.lensD, Tma.loopEntry, Tma.loopEnd, Tma.afterCoord,
    Tma.afterGather, Tma.afterQuad_site] at hx')
  all_goals (try split_ifs at hx')

theorem tma_preLt {d : Tma.D} {n : Tma.Cnt → Nat} (hJ : Tma.RefCore L g d n)
    (hb : d.site ≠ .outBar) (hx : d.site ≠ .exit) : Tma.place d < Tma.endPlace := by
  have hi := Tma.idx_le d.site
  have ho : d.site.ord ≤ 5 + d.site.idx := by cases d.site <;> simp only [Tma.Site.ord] <;> omega
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  simp only at hb hx hi ho
  unfold Tma.place
  split
  · rename_i h; exact absurd h hb
  · rename_i h; exact absurd h hx
  · simp only [Tma.endPlace, endSlot, tmaOrg, loopBase, stride, blockCap, tmaBlk0, tmaOff,
      Tma.Site.idx, Tma.Site.stage, Tma.Site.rdN, Tma.Site.gN] at hi ho ⊢
    split_ifs with h
    · obtain ⟨⟨-, -, hR', hr, -⟩, -⟩ := (Tma.core_loop h).1 hJ
      simp only at hR' hr ⊢
      omega
    · omega

/-! ### Warpgroup 2 -/

theorem deq_evEnd {d : Dequant.Control.D} {e : Event} (hev : Dequant.Ev L g d e)
    (hk : e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) :
    (d.site = .exit ∧ e.kind = .exit) ∨ d.site = .bar := by
  obtain ⟨-, hK⟩ := hev
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  rcases hk with hk | ⟨c, md, hk⟩ <;>
    cases site <;> simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv, hk] at hK ⊢

theorem deq_rawNext (r : Fin 4) (t : Fin 8) : Dequant.Control.rawNext r t ≠ .exit := by
  revert r t; decide

theorem deq_storeNext (r : Fin 4) (t : Fin 8) : Dequant.Control.storeNext r t ≠ .exit := by
  revert r t; decide

theorem deq_noExit (hp : Pre P L m) {d d' : Dequant.Control.D} {f : Event}
    (h : Dequant.Control.succ P L g d f = some (some d')) (hb : d.site ≠ .bar)
    (hx : d.site ≠ .exit) : d'.site ≠ .exit := by
  intro hx'
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site <;> simp only [Dequant.Control.succ, Dequant.Control.poll,
    Dequant.Control.dataRd, Code.ncNext] at h
  case bar => exact hb rfl
  case exit => exact hx rfl
  all_goals (repeat' split at h)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals (try subst h)
  all_goals (try simp [Dequant.Control.afterSmr, batch_in hp g, Dequant.Control.afterA,
    Dequant.Control.loopEntry, Dequant.Control.advance, Dequant.Control.scaleNext,
    deq_rawNext, deq_storeNext] at hx')
  all_goals (try split_ifs at hx')

theorem deq_preLt {d : Dequant.Control.D} {n : Dequant.Cnt → Nat} (hJ : Dequant.Ref L g d n)
    (h0 : n .ub = 0) (hb : d.site ≠ .bar) (hx : d.site ≠ .exit) :
    Dequant.place d < Dequant.endPlace := by
  have hR := Dequant.rounds_lt d.l0 d.l1
  have hi := Dequant.idx_le d.site
  have he := Dequant.elOff_le d
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hJ' := hJ h0
  simp only at hb hx
  cases s <;> simp only [Dequant.place, deqBlk0, Dequant.endPlace, endSlot, deqOrg, loopBase,
    deqOff, stride, blockCap, ne_eq, not_true_eq_false] at hb hx hR hi he ⊢ <;> try omega
  all_goals
    obtain ⟨i, hw, -⟩ := hJ'
    have hb := Dequant.blk_eq hw
    obtain ⟨hlt, -⟩ := hw
    simp only at hb hlt hR ⊢
    rw [hb]
    omega

/-! ### The index warp -/

theorem ix_evEnd {d : Index.D} {e : Event} (hev : Index.Ev P L g d e)
    (hk : e.kind = .exit ∨ ∃ c md, e.kind = .bar 12 c md) :
    (d.site = .exit ∧ e.kind = .exit) ∨ d.site = .bar := by
  obtain ⟨-, hK⟩ := hev
  obtain ⟨site, el, ac, c⟩ := d
  rcases hk with hk | ⟨c', md, hk⟩ <;>
    cases site <;>
      simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv, Index.StoreEv,
          hk] at hK ⊢

theorem ix_first (hp : Pre P L m) : (Index.ofC (ixFirst P L g)).site ≠ .exit := by
  have h := Index.afterA_site (P := P)
    { l0 := pw P.topk, l1 := pw P.extra_topk : IxCtl }
  unfold ixFirst
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split_ifs
  · intro hx
    rw [hx] at h
    simp at h
  · intro hx
    cases hx

theorem ix_noExit {d d' : Index.D} {f : Event} (h : Index.succ P L g d f = some (some d'))
    (hb : d.site ≠ .bar) (hx : d.site ≠ .exit) : d'.site ≠ .exit := by
  intro hx'
  obtain ⟨site, el, ac, c⟩ := d
  cases site <;> simp only [Index.succ, Index.lenNext, Index.ncPair, Index.poll, Code.ncNext] at h
  case bar => exact hb rfl
  case exit => exact hx rfl
  all_goals (try (obtain ⟨r, rfl⟩ := Index.shflNext_some h; simp at hx'))
  all_goals (repeat' split at h)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals (try subst h)
  all_goals (try simp only [Index.ldNext, Index.stNext, Index.ofC] at hx')
  all_goals (try split_ifs at hx')
  all_goals (try simp only [Index.afterSt] at hx')
  all_goals (try split_ifs at hx')
  all_goals (try simp at hx')
  all_goals first
    | exact absurd (hx' ▸ Index.afterA_site (P := P) _) (by decide)
    | exact absurd (hx' ▸ Index.lens_site _) (by decide)
    | exact absurd (hx' ▸ Index.afterPre_site _) (by decide)
    | exact absurd (hx' ▸ Index.mainEnd_site _) (by decide)
    | exact absurd (hx' ▸ Index.afterXpre_site _) (by decide)
    | exact absurd (hx' ▸ Index.xEnd_site _) (by decide)

theorem ix_place {d : Index.D} {n : Index.Cnt → Nat} (hB : Index.Body P L g d n)
    (hx : d.site ≠ .exit) : Index.place L g d n ≤ Index.ixEndPlace ∧
      (d.site ≠ .bar → Index.place L g d n < Index.ixEndPlace) := by
  obtain ⟨i, hpre, -, -, hrc, hct, -⟩ := hB
  have hb : Index.blockOf L g n = i := by
    unfold Index.blockOf
    rw [(hrc 0).2, (hrc 1).2, (hrc 2).2, (hrc 3).2]
    exact Index.ring_sum i
  have hR := Index.rounds_lt d.c.l0 d.c.l1
  obtain ⟨site, el, ac, c⟩ := d
  simp only at hx hpre hct hR ⊢
  unfold Index.place Index.placeAt
  rw [hb]
  have hE : Index.ixEndPlace = ixBlk0 + stride * (blockCap + 4) := by decide
  cases site <;> simp only [Index.Ctr, Index.MainW, Index.XW, Index.preSite, Index.ord,
    forall_const, ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true,
    IsEmpty.forall_iff] at hx hpre hct ⊢
  all_goals (try rw [Index.endAt_eq (by simp only [blockCap]; omega)])
  all_goals rw [hE]
  all_goals simp only [Index.nMin, ixBlk0, loopBase, ixOff, ixOrg, stride, blockCap] at hct ⊢
  all_goals (try omega)
  exact ⟨Nat.le_refl _, trivial⟩

/-! ### The phases -/

def mmaPh : Mma.Site → Nat
  | .outBar => 1
  | .exit => 2
  | _ => 0

def tmaPh : Tma.Site → Nat
  | .outBar => 1
  | .exit => 2
  | _ => 0

def ixPh : IxSite → Nat
  | .bar => 1
  | .exit => 2
  | _ => 0

def idlePh : IdleSite → Nat
  | .bar => 1
  | .ret => 2
  | _ => 0

def deqPh : Dequant.Site → Nat
  | .bar => 1
  | .exit => 2
  | _ => 0

theorem mma_phPlace {d : Mma.D} {n : Mma.Cnt → Nat} (hJ : Mma.RefCore L g d n) :
    (mmaPh d.site = 0 → Mma.place d < Mma.endPlace) ∧
      (mmaPh d.site = 1 → Mma.place d = Mma.endPlace) ∧
      (mmaPh d.site = 2 → Mma.place d = Mma.endPlace + 1) := by
  by_cases hb : d.site = .outBar
  · simp [mmaPh, Mma.place, hb]
  by_cases hx : d.site = .exit
  · simp [mmaPh, Mma.place, hx]
  have h := mma_preLt hJ hb hx
  have h0 : mmaPh d.site = 0 := by unfold mmaPh; split <;> simp_all
  omega

theorem tma_phPlace {d : Tma.D} {n : Tma.Cnt → Nat} (hJ : Tma.RefCore L g d n) :
    (tmaPh d.site = 0 → Tma.place d < Tma.endPlace) ∧
      (tmaPh d.site = 1 → Tma.place d = Tma.endPlace) ∧
      (tmaPh d.site = 2 → Tma.place d = Tma.endPlace + 1) := by
  by_cases hb : d.site = .outBar
  · simp [tmaPh, Tma.place, hb]
  by_cases hx : d.site = .exit
  · simp [tmaPh, Tma.place, hx]
  have h := tma_preLt hJ hb hx
  have h0 : tmaPh d.site = 0 := by unfold tmaPh; split <;> simp_all
  omega

theorem deq_phPlace {d : Dequant.Control.D} {n : Dequant.Cnt → Nat} (hJ : Dequant.Ref L g d n)
    (h0 : n .ub = 0) :
    (deqPh d.site = 0 → Dequant.place d < Dequant.endPlace) ∧
      (deqPh d.site = 1 → Dequant.place d = Dequant.endPlace) ∧
      (deqPh d.site = 2 → Dequant.place d = Dequant.endPlace + 1) := by
  by_cases hb : d.site = .bar
  · simp [deqPh, Dequant.place, hb]
  by_cases hx : d.site = .exit
  · simp [deqPh, Dequant.place, hx]
  have h := deq_preLt hJ h0 hb hx
  have h1 : deqPh d.site = 0 := by unfold deqPh; split <;> simp_all
  omega

theorem ix_phPlace {d : Index.D} {n : Index.Cnt → Nat} (hB : Index.Body P L g d n) :
    (ixPh d.site = 0 → Index.place L g d n < Index.ixEndPlace) ∧
      (ixPh d.site = 1 → Index.place L g d n = Index.ixEndPlace) ∧
      (ixPh d.site = 2 → Index.ixEndPlace < Index.place L g d n) := by
  by_cases hx : d.site = .exit
  · have : Index.ixEndPlace ≤ Index.endAt (Index.blockOf L g n) := Nat.le_max_left _ _
    simp only [ixPh, Index.place, Index.placeAt, hx]
    omega
  obtain ⟨h1, h2⟩ := ix_place hB hx
  by_cases hb : d.site = .bar
  · simp only [ixPh, hb]
    have : Index.ixEndPlace ≤ Index.endAt (Index.blockOf L g n) := Nat.le_max_left _ _
    simp only [Index.place, Index.placeAt, hb] at h1 ⊢
    omega
  have h0 : ixPh d.site = 0 := by unfold ixPh; split <;> simp_all
  have := h2 hb
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
