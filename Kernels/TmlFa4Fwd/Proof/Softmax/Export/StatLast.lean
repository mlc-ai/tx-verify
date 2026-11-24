-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.Prev
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollTc
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The statistics stores before a softmax lane's arrivals on its named barrier

From its second arrival on the barrier with the correction warps, a softmax lane stores its row sum
between the arrival before and this one (`soft_stat_sum`), and at its last arrival, after all
rounds, its row maximum too (`soft_stat_max`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (allSites mem_allSites nexts lz ptsOf passed before
  inBias inPlain preR)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h i : Nat}

/-- A store of lane `h`'s statistics word `n` (the sum `0`, the maximum `1`) before its event `i`,
with no event on its barrier with the correction warps between. -/
def StatBefore (L : Launch) (X : Execution) (h i n : Nat) : Prop :=
  ∃ i' < i, ∃ pc a bs, X.get (h, i') = some ⟨pc, .wr a bs⟩ ∧ a.size = 4 ∧
    a.loc = ⟨.shared, h / L.block, L.sharedBase + 368 + 1024 * n +
      4 * (128 * Softmax.stN L h + h % L.block % 128)⟩ ∧
    ((X.tr h).take i').countP (Execution.isBarId (Prologue.warpIndex L h + 3)) =
      ((X.tr h).take i).countP (Execution.isBarId (Prologue.warpIndex L h + 3))

/-- The store before a site: the statistics store before a later round's arrival, the final stores
before the last. -/
private def stBefore : Softmax.Site → Option Softmax.Site
  | .narr .bias => some (.stat false)
  | .narr .plain => some (.stat true)
  | .finarr => some (.fin 1)
  | .fin 1 => some (.fin 0)
  | _ => none

private theorem stBefore_st {s s0 : Softmax.Site} (h : stBefore s = some s0) :
    (∃ pl, s0 = .stat pl) ∨ ∃ k, s0 = .fin k := by
  unfold stBefore at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

private theorem st_pred : [false, true].all (fun b => allSites.all fun s =>
    (nexts b s).all fun s' =>
      match stBefore s' with | some s0 => s == s0 | none => true) = true := by
  decide +kernel

private theorem nb_tab (b : Bool) :
    (ptsOf b .nb).countP (before (.narr .first)) = 0 ∧
    (ptsOf b .nb).countP (before (.narr .bias)) = 1 ∧
    (ptsOf b .nb).countP (before (.narr .plain)) = 1 ∧
    (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 := by
  cases b <;> decide +kernel

private theorem narr_reg : preR (.narr .first) = true ∧
    inBias (Softmax.Site.narr .bias).pos = true ∧ preR (.narr .bias) = false ∧
    inPlain (Softmax.Site.narr .plain).pos = true ∧ preR (.narr .plain) = false := by
  decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L h < 8)
include hp hX hw

/-- **The store before a state**: at a site after a store, the lane's last event is the store. -/
private theorem st_prev {d : Softmax.Control.D} {n : Cls → Nat} {s0 : Softmax.Site} {e : Event}
    (he : X.get (h, i) = some e) (hσ : Frame.stateAt (thread p L) X h i =
      some (some (SmWarp.sinj p L h d n))) (hs : stBefore d.site = some s0) :
    ∃ j d0 n0 pc a bs, i = j + 1 ∧
      Frame.stateAt (thread p L) X h j = some (some (SmWarp.sinj p L h d0 n0)) ∧
      d0.site = s0 ∧ X.get (h, j) = some ⟨pc, .wr a bs⟩ ∧
      Softmax.StatWord L h (Softmax.statIx s0) a := by
  have hg := Frame.lt_of_get hX he
  have hlen : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := by
    cases i with
    | zero => rw [Frame.stateAt_zero] at hσ; cases hσ
    | succ j => exact ⟨j, rfl⟩
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (h, j) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (show j < (X.tr h).length by omega)⟩
  have hne : ∀ f, e0.kind ≠ .ub f := fun f hf =>
    Frame.noUbBefore_of_get hX he j (by omega) e0 he0 f hf
  have hinit : d ≠ (frag p L h .softmax).init := by
    rintro rfl
    cases hs
  obtain ⟨⟨r, d0⟩, n0, hσ0⟩ := prev_role (show (X.tr h)[j]? = some e0 from he0) hσ hinit
  have hR := (SmWarp.good hp hX hw hg rfl j).2 _ hσ0
  cases r with
  | softmax =>
    have hev := (SmWarp.fired_soft hp hX he0 hσ0 hne).1
    have hst := Frame.stateAt_succ (C := thread p L) (show (X.tr h)[j]? = some e0 from he0)
    rw [hσ, hσ0] at hst
    have hn : (thread p L h).next (SmWarp.sinj p L h d0 n0) e0 =
      some (some (SmWarp.sinj p L h d n)) := hst.symm
    rw [SmWarp.next_sinj] at hn
    obtain ⟨o, ho, hm⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨d1, rfl, hd1⟩ := Option.map_eq_some_iff.mp hm
    have hdd : d1 = d := by
      have := congrArg Prod.fst hd1
      simpa [SmWarp.sinj] using this
    subst hdd
    have hsite : d0.site = s0 := by
      rcases soft_move ho with ⟨h1, hk, -⟩ | ⟨h1, hd, -⟩ | ⟨hm, -⟩
      · exfalso
        rw [h1] at hs
        have hev1 := hev.1
        have hsc : d0.scheduler.site = d0.site := rfl
        cases hs0 : d0.site <;> rw [hs0] at hs <;> simp only [stBefore, reduceCtorEq] at hs <;>
          simp only [Softmax.Ev, hsc, hs0] at hev1 <;>
          rcases hk with ⟨_, _, _, _, hk⟩ | ⟨_, _, hk⟩ <;> rw [hk] at hev1 <;>
          simp at hev1
      · exfalso
        rw [h1] at hs
        revert hs hd
        cases d0.site <;> simp [stBefore, Softmax.Site.delayed]
      · have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp st_pred (lz L h)
          (by cases lz L h <;> simp)) d0.site (mem_allSites _)) d1.site hm
        rw [hs] at this
        simpa using this
    have hst0 : (∃ pl, d0.site = .stat pl) ∨ ∃ k, d0.site = .fin k := by
      rw [hsite]
      exact stBefore_st hs
    have hw0 : ∃ a bs, e0.kind = .wr a bs := by
      have hev1 := hev.1
      have hsc : d0.scheduler.site = d0.site := rfl
      rcases hst0 with ⟨pl, h0⟩ | ⟨k, h0⟩ <;> simp only [Softmax.Ev, hsc, h0] at hev1 <;>
        exact hev1.resolve_right fun ⟨f, hf⟩ => hne f hf
    obtain ⟨a, bs, hk⟩ := hw0
    obtain ⟨t, ins, o', hat, hi', hc, hf⟩ :=
      Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he0 hσ0 hne
    have hword := Softmax.stat_word hp (d := d0.scheduler) hat (by
      have h := hi'.1
      change Softmax.Control.Inv d0 at h
      rcases hst0 with ⟨pl, h0⟩ | ⟨k, h0⟩ <;> simp only [Softmax.Control.Inv, h0] at h <;>
        (change (d0.k = 0 ∧ d0.acc = [] ∧ d0.site.first = true) ∨ d0.site.midOk d0.k d0.acc
         rw [h0]; exact h))
      hc hf hst0 hk
    obtain ⟨pc, kd⟩ := e0
    simp only at hk
    subst hk
    refine ⟨j, d0, n0, pc, a, bs, rfl, hσ0, hsite, he0, ?_⟩
    have : d0.scheduler.site = s0 := hsite
    rwa [this] at hword
  | _ => exact hR.elim

omit hp hX hw in
private theorem bar_take {j pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (h, j) = some ⟨pc, .wr a bs⟩) (id : Nat) :
    ((X.tr h).take (j + 1)).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id) := by
  rw [List.take_add_one, show (X.tr h)[j]? = _ from he]
  simp [Execution.isBarId]

include hFw in
/-- The state of a lane at an arrival on its barrier with the correction warps. -/
private theorem arr_state {pc : Nat}
    (he : X.get (h, i) =
      some ⟨pc, .bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩) :
    ∃ d n rb rp c ns nv, Frame.stateAt (thread p L) X h i =
        some (some (SmWarp.sinj p L h d n)) ∧ Softmax.RefQ p L h d.scheduler c rb rp ∧
      SmWarp.SFits p L h d.scheduler ns nv ∧ (d.site = .finarr ∨ ∃ r, d.site = .narr r) ∧
      ((X.tr h).take i).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) = c .nb := by
  have hub : ∀ f, (⟨pc, .bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩ : Event).kind ≠
    .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    have hx : exit L h s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
    | _ => simp [Startup.Ev] at hev
  · obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
    refine ⟨d, n, rb, rp, c, _, _, hσ, hQ, hF, ?_, ?_⟩
    · rcases soft_bar_site hev.1 with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨h1, -⟩
      · omega
      · split at h1 <;> omega
      · exact h1
    · rw [soft_isBarId hw, count hσ, hLk _ rfl]

/-- From the store before a state. -/
private theorem before_of {d : Softmax.Control.D} {n : Cls → Nat} {s0 : Softmax.Site} {e : Event}
    (he : X.get (h, i) = some e) (hσ : Frame.stateAt (thread p L) X h i =
      some (some (SmWarp.sinj p L h d n))) (hs : stBefore d.site = some s0) :
    StatBefore L X h i (Softmax.statIx s0) := by
  obtain ⟨j, d0, n0, pc, a, bs, rfl, -, -, he0, h1, h2⟩ := st_prev hp hX hw he hσ hs
  exact ⟨j, by omega, pc, a, bs, he0, h1, h2, (bar_take he0 _).symm⟩

include hFw

/-- **The row sum is stored before an arrival but the first.** -/
theorem soft_stat_sum {pc : Nat}
    (he : X.get (h, i) =
      some ⟨pc, .bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩)
    (hA : 1 ≤ ((X.tr h).take i).countP (Execution.isBarId (Prologue.warpIndex L h + 3))) :
    StatBefore L X h i 0 := by
  obtain ⟨d, n, rb, rp, c, ns, nv, hσ, hQ, -, hs, hc⟩ := arr_state hp hX hFw hw he
  rcases hs with hs | ⟨r, hs⟩
  · obtain ⟨j, d0, n0, pc0, a0, bs0, rfl, hσ0, hs0, he0, -⟩ :=
      st_prev hp hX hw he hσ (s0 := .fin 1) (by rw [hs]; rfl)
    obtain ⟨i', hi, pc', a, bs, h1, h2, h3, h4⟩ :=
      before_of hp hX hw he0 hσ0 (s0 := .fin 0) (by rw [hs0]; rfl)
    exact ⟨i', by omega, pc', a, bs, h1, h2, h3, h4.trans (bar_take he0 _).symm⟩
  · cases r with
    | first =>
      exfalso
      have hs' : d.scheduler.site = .narr .first := hs
      have h1 := hQ.cnt .nb rfl
      obtain ⟨rfl, rfl⟩ := hQ.pre (by rw [hs']; exact narr_reg.1)
      simp only [passed, hs', (nb_tab (lz L h)).1, Nat.zero_mul, Nat.add_zero] at h1
      omega
    | bias => exact before_of hp hX hw he hσ (s0 := .stat false) (by rw [hs]; rfl)
    | plain => exact before_of hp hX hw he hσ (s0 := .stat true) (by rw [hs]; rfl)

/-- **The row maximum is stored before the last arrival**, after the tile's rounds. -/
theorem soft_stat_max {pc T : Nat}
    (he : X.get (h, i) =
      some ⟨pc, .bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩)
    (hT : SoftRounds p L h T)
    (hA : ((X.tr h).take i).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) = T) :
    StatBefore L X h i 1 := by
  obtain ⟨d, n, rb, rp, c, ns, nv, hσ, hQ, hF, hs, hc⟩ := arr_state hp hX hFw hw he
  rcases hs with hs | ⟨r, hs⟩
  · exact before_of hp hX hw he hσ (s0 := .fin 1) (by rw [hs]; rfl)
  · exfalso
    have hs' : d.scheduler.site = .narr r := hs
    obtain ⟨t1, t2, t3, t4, t5⟩ := nb_tab (lz L h)
    obtain ⟨g1, g2, g3, g4, g5⟩ := narr_reg
    have h1 := hQ.cnt .nb rfl
    simp only [passed, hs', t4, t5, Nat.mul_one] at h1
    obtain ⟨T', hT', h2, h3⟩ := soft_round_lt hQ hF (by rw [hs']; rfl) (by rw [hs']; rfl) (by
      rw [hs']
      cases r
      · exact .inl g1
      · exact .inr (.inl g2)
      · exact .inr (.inr g4))
    obtain rfl := hT.unique hT'
    rw [hs'] at h3
    cases r with
    | first => rw [t1] at h1; omega
    | bias => rw [t2] at h1; have := h3.resolve_left (by rw [g3]; simp); omega
    | plain => rw [t3] at h1; have := h3.resolve_left (by rw [g5]; simp); omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
