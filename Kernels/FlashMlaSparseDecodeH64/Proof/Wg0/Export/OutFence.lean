-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PredArr

@[expose] public section

/-! # The proxy fence before warpgroup 0's softmax-ready arrival

An arrival of a lane of warpgroup 0 at pc 1122 is the event after its proxy fence
(`wg0_fenceArr`), by one step back along the machine (`wg0_back`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-! ### The backward walk -/

/-- **One step back**: the state before a state with `Q` is related to it by `R`. -/
private theorem wg0_back (hFw : Follow P L X) (hnu : NoUbInner L X) {y : Nat}
    (hw : warp L y < 4) (hy : y < L.threads) {t : Nat} (ht : t < (X.tr y).length)
    {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {Q : Wg0.Control.D → Prop} {R : Wg0.Control.D → Wg0.Control.D → Prop} (hQ : Q d)
    (hinit : ∀ d1 : Wg0.Control.D, d1.site = .smr → ¬ Q d1)
    (hstep : ∀ {d0 d1 : Wg0.Control.D} {e : Event},
      (frag P L y .wg0).next d0 e = some (some d1) → Q d1 → R d0 d1) :
    ∃ t', t = t' + 1 ∧ ∃ (d' : Wg0.Control.D) (n' : Cls → Nat),
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧ R d' d := by
  rcases wg0_pred_pre hFw (LaneUbFree.of_inner hnu hw ht) hw hy ht.le hσ with
      ⟨t', rfl, d', n', e, -, hs', hS⟩ | hsm
  · exact ⟨t', rfl, d', n', hs', hstep hS hQ⟩
  · exact absurd hQ (hinit _ hsm)

/-! ### The proxy fence before the softmax-ready arrival -/

private theorem site_arrS (s : Wg0.Site) (h : s.pc = 1122) : s = .arrS := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The event before a softmax-ready arrival is a proxy fence**: an arrival of a lane of warpgroup
0 at pc 1122 is the event after a `fence.proxy.async.shared::cta`. -/
theorem wg0_fenceArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h ia tx cnt : Nat} {l : Loc} {rel : Bool}
    {sc : MbarScope} (hw : warp L h < 4)
    (he : X.get (h, ia) = some ⟨1122, .arrive l tx cnt rel sc⟩) :
    ∃ jf, ia = jf + 1 ∧
      X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none := by
  have hg := Frame.lt_of_get hX he
  have hil : ia < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hr : 103 ≤ 1122 ∧ (1122 : Nat) < 1842 := by omega
  have hub : ∀ f, (⟨1122, .arrive l tx cnt rel sc⟩ : Event).kind ≠ .ub f := fun _ h => by
    cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, -, -⟩ := wg0_state hJ hi hev hpc hr
  have hs : d.site = .arrS := site_arrS _ hpc.symm
  obtain ⟨t', ht', d', n', hσ', hs'⟩ := wg0_back hFw (noUbInner hX) hw hg hil hσ
    (Q := fun d => d.site = .arrS) (R := fun d0 _ => d0.site = .fpx) hs
    (fun d1 h1 h2 => by rw [h1] at h2; cases h2)
    (fun hS hq => Wg0.pred_arrS (P := P) (L := L) (g := h) (w := warpW L h) hS hq)
  obtain ⟨e', he'⟩ : ∃ e', X.get (h, t') = some e' :=
    ⟨_, List.getElem?_eq_getElem (l := X.tr h) (i := t') (by omega)⟩
  have hub' := noUb_kind_of_lt hX he' (by omega) hil
  obtain ⟨σ', hσ'', hJ', hi', hev', hpc'⟩ := ev_at hp hX hFw he' hub'
  rw [hσ'] at hσ''
  cases hσ''
  have hpc2 : e'.pc = 1120 := by
    rw [show e'.pc = Wg0.Site.pc d'.site from hpc', hs']
    rfl
  obtain ⟨d1, n1, h1, -, hE, -⟩ := wg0_state hJ' hi' hev' hpc' (by omega)
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
  obtain ⟨rfl, -⟩ := h1
  have hk := hE.2
  unfold Wg0.EvK at hk
  rw [hs'] at hk
  obtain ⟨pce, ke⟩ := e'
  exact ⟨t', ht', pce, by rw [he']; simp only at hk; rw [hk]⟩
