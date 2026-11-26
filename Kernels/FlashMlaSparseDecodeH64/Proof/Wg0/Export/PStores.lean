-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Flow.Polls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Lemmas.Flow.CountTake

@[expose] public section

/-! # A lane's P stores precede its arrival on `soReady`

An arrival of a lane of warpgroup 0 at pc 1122 (the end of block `r`) follows, in the lane's
trace, the lane's 16 P stores `(k, el)` of the block (`wg0_pStores`): the states before it are, by
`Wg0.ppos_pred` and a backward walk, the stores' states and the rescale arm's, which fire no
arrival. So the store's arrivals before it are the arrival's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem get_lt {y t : Nat} (h : t < (X.tr y).length) : ∃ e, X.get (y, t) = some e :=
  ⟨_, List.getElem?_eq_getElem h⟩

private theorem site_arrS (s : Wg0.Site) (h : s.pc = 1122) : s = .arrS := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- The event of a state of the sequence has the state's kind. -/
private theorem ev_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y t : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {p : Nat} (ho : Wg0.ppos d = some p) {e : Event} (he : X.get (y, t) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    Wg0.EvK P L y (warpW L y) d e ∧ (∀ f, e.kind ≠ .ub f) ∧ e.pc = d.site.pc := by
  obtain ⟨σ, hσ', hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  have hpc' : e.pc = d.site.pc := hpc
  have hr := Wg0.ppos_pc ho
  obtain ⟨d', n', h, -, hE, -⟩ := wg0_state hJ hi hev hpc (by omega)
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hE.2, hub, hpc'⟩

/-- **The backward walk**: a state at position `p` has, for each position `q < min p 16`, an earlier
state at `q` with no arrival between. -/
private theorem pwalk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {y : Nat} (hw : warp L y < 4)
    (hy : y < L.threads) :
    ∀ j, j < (X.tr y).length → ∀ (d : Wg0.Control.D) (n : Cls → Nat) (p : Nat),
      Frame.stateAt (thread P L) X y j = some (some (.inr ⟨.inl .wg0, d⟩, n)) →
      Wg0.ppos d = some p → ∀ q, q < p → q < 16 →
      ∃ i < j, ∃ (d' : Wg0.Control.D) (n' : Cls → Nat),
        Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
        Wg0.ppos d' = some q ∧
        ∀ l, arrivals l ((X.tr y).take i) = arrivals l ((X.tr y).take j) := by
  intro j
  induction j with
  | zero =>
    intro hj d n p hσ ho q hq _
    rcases wg0_pred_pre hFw (LaneUbFree.of_inner hnu hw hj) hw hy hj.le hσ with
      ⟨t', ht', -⟩ | hs
    · omega
    · simp [Wg0.ppos, hs] at ho
  | succ j ih =>
    intro hj d n p hσ ho q hq hq16
    rcases wg0_pred_pre hFw (LaneUbFree.of_inner hnu hw hj) hw hy hj.le hσ with
      ⟨t', ht', d', n', e, he, hs', hS⟩ | hs
    · obtain rfl : j = t' := by omega
      obtain ⟨p', hp', hrel⟩ := Wg0.ppos_pred hS ho (by omega)
      have hge : X.get (y, j) = some e := he
      obtain ⟨hE, hub, -⟩ := ev_of hp hX hFw hs' hp' hge
        (noUb_kind_of_lt hX hge (Nat.lt_succ_self j) hj)
      have hcnt : ∀ l, arrivals l ((X.tr y).take (j + 1)) = arrivals l ((X.tr y).take j) :=
        fun l => countP_take_succ_false hge (by
          have := Wg0.ppos_noArr hp' (by have := Wg0.ppos_le ho; omega) hE
          obtain ⟨pc, kd⟩ := e
          cases kd <;> simp only [arrivesOn, sourceArrive]
          rename_i m' tx' n' rel' sc'
          simp only [decide_eq_false_iff_not]
          rintro rfl
          exact this _ tx' n' rel' sc' rfl)
      by_cases hqp : q = p'
      · exact ⟨j, by omega, d', n', hs', by rw [hp', hqp], fun l => (hcnt l).symm⟩
      · obtain ⟨i, hi, d2, n2, h2, o2, hc⟩ := ih (by omega) d' n' p' hs' hp' q (by omega) hq16
        exact ⟨i, by omega, d2, n2, h2, o2, fun l => (hc l).trans (hcnt l).symm⟩
    · simp [Wg0.ppos, hs] at ho

/-- **A lane's arrival on `soReady` follows its 16 P stores of the block**: the store `(k, el)`
writes the four bytes `4 el` after the lane's place of store `k`, and no arrival lies between it
and the arrival. -/
theorem wg0_pStores (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h ia tx cnt : Nat} {l : Loc} {rel : Bool}
    {sc : MbarScope} (hw : warp L h < 4)
    (he : X.get (h, ia) = some ⟨1122, .arrive l tx cnt rel sc⟩) (k : Fin 4) (el : Fin 4) :
    ∃ i < ia, ∃ a bs, X.get (h, i) = some ⟨704 + k.val, .wr a bs⟩ ∧ a.size = 4 ∧
      a.loc = wsLoc L (h / L.block)
      (204800 + 4096 * (tidOf L h / 32 / 2) + 512 * (tidOf L h / 32 % 2) +
        16 * (tidOf L h % 32) + 1024 * k.val + 4 * el.val) ∧
      ∀ l', arrivals l' ((X.tr h).take i) = arrivals l' ((X.tr h).take ia) := by
  have hg := Frame.lt_of_get hX he
  have hil : ia < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hr : 103 ≤ 1122 ∧ (1122 : Nat) < 1842 := by omega
  have hub : ∀ f, (⟨1122, .arrive l tx cnt rel sc⟩ : Event).kind ≠ .ub f := fun _ h => by
    cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, -, -⟩ := wg0_state hJ hi hev hpc hr
  have hs : d.site = .arrS := site_arrS _ hpc.symm
  have ho : Wg0.ppos d = some 17 := by simp [Wg0.ppos, hs]
  obtain ⟨i, hi', d', n', hσ', ho', hc⟩ := pwalk hp hX hFw (noUbInner hX) hw hg ia hil d n 17 hσ ho
    (4 * k.val + el.val) (by omega) (by omega)
  obtain ⟨e, he'⟩ := get_lt (X := X) (y := h) (t := i) (by omega)
  obtain ⟨hE, hub', hpcE⟩ := ev_of hp hX hFw hσ' ho' he' (noUb_kind_of_lt hX he' hi' hil)
  obtain ⟨k', hk', hq⟩ := Wg0.ppos_ost ho' (by omega)
  have ht : tidOf L h < 128 := MemRow.wg0_tid hw
  obtain ⟨hel, a, bs, hkind, hsz, hloc⟩ := Wg0.ost_acc hp ht hk' hE hub'
  have hkk : k'.val = k.val := by omega
  have hee : d'.el = el.val := by omega
  refine ⟨i, hi', a, bs, ?_, hsz, ?_, hc⟩
  · rw [he']
    obtain ⟨pc, kd⟩ := e
    simp only at hkind hpcE
    rw [hkind, hpcE, hk', show (Wg0.Site.ost k').pc = 704 + k'.val from rfl, hkk]
  · rw [hloc, hkk, hee]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
