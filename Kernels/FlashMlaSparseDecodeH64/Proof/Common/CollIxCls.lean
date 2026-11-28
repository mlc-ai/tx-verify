-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The collectives of warp 7 (the index warp)

`ixCls`: the `CollCls` of the lanes of warp 7 of one CTA. Its collectives are shuffles: the
startup's two and the head's, then two per block of the CTA's rows (`ixCn`), counted by the
thread machine's ghost count of shuffles. The only blocking event of the index code is its
barrier, after which the machine is at its exit; the head's `setmaxnreg` is the register request
every lane of the warp makes before its shuffle. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- Every event of the index code but the barrier is unblocking. -/
theorem ix_unblocking {d : Index.D} {e : Event} (hK : Index.EvK P L x d e)
    (hs : d.site ≠ .bar) : Sched.Unblocking e.kind := by
  obtain ⟨site, el, ac, c⟩ := d
  unfold Index.EvK at hK
  simp only at hK hs
  cases site with
  | lenA | lenB => rcases hK with ⟨a, bs, hk⟩ | ⟨f, hk⟩ <;> simp [Sched.Unblocking, hk]
  | pre | pf | xpre | xpf =>
    rcases hK with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩ <;> simp [Sched.Unblocking, hk]
  | wA | wB => rcases hK with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> simp [Sched.Unblocking, hk]
  | sA1 | sA2 | sB1 | sB2 =>
    rcases hK with ⟨a, b, c', r, ok, hk⟩ | ⟨f, hk⟩ <;> simp [Sched.Unblocking, hk]
  | stA | stB | bA | bB =>
    rcases hK with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩ <;> simp [Sched.Unblocking, hk]
  | arrA | arrB | exit => simp [Sched.Unblocking, hK]
  | bar => exact absurd rfl hs

/-- **A lane of warp 7 at the head's shuffle has made its register request**, from its ghost
count. -/
theorem ix_req (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7)
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x (X.tr x).length = some (some σ))
    (hc : CollAt P L x σ) (hn : σ.2 .shfl = 2) :
    ∃ j pc inc n i, X.get (x, j) = some ⟨pc, .setMaxReg inc n i⟩ := by
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n, rfl, hW, hxd⟩ | ⟨s, n, rfl, hs, hn0⟩ | ⟨d, n, rfl⟩
  · have hc' := collAt_iff.mp hc
    rw [pc_startup] at hc'
    obtain ⟨j, hj⟩ := sh_site (by omega) hW hc'
    obtain ⟨site, x1, x2⟩ := d
    simp only at hj
    subst hj
    obtain ⟨h1, -⟩ := hW
    have := j.isLt
    simp only at hn
    omega
  · rcases hs with rfl | rfl
    · have := collAt_iff.mp hc
      rw [pc_smr] at this
      simp [collPcs] at this
    · exact hsh_req hp hX hFw hub hx hσ
  · obtain ⟨b, hsh, -⟩ := ix_facts hp hX hFw (noUbBefore_of_noUb hub) hσ hx hw
    have : (ixS P L x d n).2 .shfl = n .shfl := rfl
    omega

/-- **After a blocking event of a lane of warp 7** the machine runs on, at no collective, or
(after the head's `setmaxnreg`) at the head's shuffle, at which every lane of the warp that is
at it has made its request. -/
theorem ix_last (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x = 7)
    {k : Nat} {σ : (thread P L x).D} {e : Event} (he : X.get (x, k) = some e)
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (hb : ¬ Sched.Unblocking e.kind) :
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' ∨ ((∃ inc n i, e.kind = .setMaxReg inc n i) ∧
        ∀ y σy, IxLane L (x / L.block) y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          σy.2 .shfl = σ'.2 .shfl → ∃ j pc inc n i,
            X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  rcases ix_cls2 hFw hx hw hσ with ⟨d, n, rfl, hW, hxd⟩ | ⟨s, n, rfl, hs, hn0⟩ | ⟨d, n, rfl⟩
  · obtain ⟨h1, h2⟩ := startup_last hp hX hFw hub he hσ hb
    exact ⟨h1, fun σ' h => .inl fun hc => h2 σ' h (collAt_iff.mp hc)⟩
  · obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    rcases hs with rfl | rfl
    · have hev' : Wg1.Ev L x .smr e := hev
      obtain ⟨inst, hk⟩ := hev'
      refine ⟨by rw [next_head]; simp [Wg1.succ], fun σ' hn => .inr ⟨⟨_, _, _, hk⟩, ?_⟩⟩
      have hs' := smr_next hn
      intro y σy hy _ hσy hcy hny
      have h2 : σ'.2 .shfl = 2 := by
        rw [hs']
        have : Code.bump cls n e .shfl = n .shfl + if Execution.isShfl e then 1 else 0 := rfl
        have hns : ¬ Execution.isShfl e = true := by
          obtain ⟨pc, kd⟩ := e
          simp only at hk
          subst hk
          simp [Execution.isShfl]
        simp [this, hns, hn0]
      exact ix_req hp hX hFw hub hy.1 hy.2.1 hσy hcy (by rw [hny, h2])
    · have hev' : Wg1.Ev L x .hsh e := hev
      obtain ⟨r, ok, hk⟩ := hev'
      rw [hk] at hb
      simp [Sched.Unblocking] at hb
  · obtain ⟨σ0, hσ0, -, -, hev⟩ := ev_state hp hX hFw he hne
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    have hev' : Index.Ev P L x d e := hev
    obtain ⟨hpc, hK⟩ := hev'
    have hbar : d.site = .bar := by
      by_contra hs
      exact hb (ix_unblocking hK hs)
    have hsu : Index.succ P L x d e = some (some { d with site := .exit }) := by
      obtain ⟨site, el, ac, c⟩ := d
      simp only at hbar
      subst hbar
      simp [Index.succ]
    refine ⟨by rw [next_sub]; show (Index.succ P L x d e).map _ ≠ none; simp [hsu], fun σ' hn => ?_⟩
    obtain ⟨d', hsu', rfl⟩ := ixD_next hn
    rw [hsu] at hsu'
    obtain rfl := Option.some.inj (Option.some.inj hsu')
    exact .inl fun hc => by
      have := ix_coll_site.mp hc
      simp at this

/-- **The collectives of the lanes of warp 7 of CTA `c`.** -/
def ixCls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    (hub : ¬ HasUb X) (c : Nat) : CollCls P L X (IxLane L c) (collS P L) where
  cn := ixCn P L c
  slot := ixSlot
  nc := fun _ σ => σ.2 .shfl
  count := fun {y k σ} hA hσ => ix_count hp hX hFw hub hA.1 hA.2.1 k σ hσ
  at_ := fun {y k σ} hA hσ => by
    have h := ix_at hp hX hFw hub hA.1 hA.2.1 hσ
    rwa [hA.2.2] at h
  isP := fun hA hσ he hc => coll_isP hp hX hσ he hc
  slot_mono := fun {a b} hab hb => ixSlot_mono hab hb
  time_at := fun hA hσ hc => ix_time_at hp hX hFw hub hA.1 hA.2.1 hσ hc
  time_lt := fun {y k σ} hA hσ hc n hn hle => by
    obtain rfl := hA.2.2
    exact ix_time_lt hp hX hFw hub hA.1 hA.2.1 hσ hc hn hle
  static := fun {y z k k' σ σ'} hA hB hσ hσ' hc hc' hn => by
    have h1 := (ix_at hp hX hFw hub hA.1 hA.2.1 hσ).mp hc
    have h2 := (ix_at hp hX hFw hub hB.1 hB.2.1 hσ').mp hc'
    rw [hA.2.2] at h1
    rw [hB.2.2] at h2
    have hn' : σ.2 .shfl = σ'.2 .shfl := hn
    rw [hn', h2] at h1
    have := Option.some.inj h1
    show pcShape _ = pcShape _
    rw [this]
  exit := fun {y k pc σ} hA hσ he n hn => by
    obtain rfl := hA.2.2
    exact ix_exit hp hX hFw hub hA.1 hA.2.1 hσ he hn
  last := fun {y k σ e} hA he hσ hb => by
    obtain rfl := hA.2.2
    obtain ⟨h1, h2⟩ := ix_last hp hX hFw hub hA.1 hA.2.1 he hσ hb
    exact ⟨h1, fun σ' h => ((h2 σ' h).imp_right .inl)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
