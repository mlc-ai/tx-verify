-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.ElectNum
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's elections, by its TMA polls

Standalone fact. A lane of warp 14 makes three elections per successful poll of a Q or Bias empty
barrier, less the ones to come in the group it is in (`elRem`); the drain's poll counts one. A lane
of warp 15 makes none. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The elections still to come in the group a site is in. -/
def elRem : Site → Nat
  | .te _ e => 3 - e.val
  | .ta _ => 2
  | .tc _ c => 1 - c.val
  | .de => 3
  | .da | .exit => 2
  | _ => 0

/-- The edge check. -/
def totChk (b : Bool) (s s' : Site) : Bool :=
  if b then !s.isEl else
    (s' != s || !s.isEl) && elRem s' + (if s.isEl then 1 else 0) ==
      elRem s + 3 * ([16, 24, 336, 344].countP fun o => tag s s' == .acq o)

theorem tot_edges : Edges totChk := by unfold Edges AllSites; decide +kernel

/-- An election of a role, past the startup. -/
def roleEl (e : Event) : Bool := isElectEv e && decide (173 < e.pc)

/-- The elections of its role before a state of a loader lane. -/
abbrev els (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP roleEl

theorem el_pc : AllSites fun s => (!s.isEl || decide (173 < s.pc)) = true := by
  unfold AllSites; decide +kernel

/-- The successful polls of the Q and Bias empty barriers. -/
def tmaPolls (L : Launch) (g : Nat) (n : Cnt → Nat) : Nat :=
  n (.acquire (bl L g 16)) + n (.acquire (bl L g 24)) + n (.acquire (bl L g 336)) +
    n (.acquire (bl L g 344))

variable {p : Params} {L : Launch} {g : Nat}

private theorem polls_step {w : Nat} {d d' : D} {n : Cnt → Nat} {e : Event}
    (hm : Move L g w (d, n) e d') : tmaPolls L g (Code.bump (cls L g) n e) = tmaPolls L g n +
      [16, 24, 336, 344].countP fun o => tag d.site d'.site == .acq o := by
  have hb : ∀ o ∈ [16, 24, 336, 344], Code.bump (cls L g) n e (.acquire (bl L g o)) =
      n (.acquire (bl L g o)) + if tag d.site d'.site = .acq o then 1 else 0 := by
    intro o ho
    rw [bump_tag hm]
    cases tag d.site d'.site <;>
      simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
        Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    case acqRing δ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      have := Nat.mod_lt (n .commit + δ) (show 0 < 3 by decide)
      have hne : ¬ 56 + 8 * ((n .commit + δ) % 3) = o := by omega
      simp [hne]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  unfold tmaPolls
  rw [h1, h2, h3, h4]
  simp only [List.countP_cons, List.countP_nil, beq_iff_eq]
  omega

private theorem els_succ {X : Execution} {k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    els X g (k + 1) = els X g k + if roleEl e then 1 else 0 := by
  have he' : (X.tr g)[k]? = some e := he
  unfold els
  rw [List.take_add_one, he', List.countP_append]
  simp [List.countP_cons]

/-- **The elections of a loader lane** at every state of its role. -/
theorem elect_tot {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : (Prologue.warpIndex L g = 14 →
      els X g k + elRem d.site = 3 * tmaPolls L g (LdWarp.lcn n)) ∧
    (Prologue.warpIndex L g = 15 → els X g k = 0) := by
  refine LdWarp.step_at (w := Prologue.warpIndex L g)
    (I := fun k dn => (Prologue.warpIndex L g = 14 →
      els X g k + elRem dn.1.site = 3 * tmaPolls L g dn.2) ∧
      (Prologue.warpIndex L g = 15 → els X g k = 0)) ?_ ?_ ?_ hp hX hg hw rfl k b d n hσ hub
  · intro b k n _ _ hst
    have h0 : els X g k = 0 := by
      refine hst _ fun s e hE hen => ?_
      obtain ⟨pc, kind⟩ := e
      rw [Bool.eq_false_iff]
      intro hc
      simp only [roleEl, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hk, hpc⟩ := hc
      have := start_el_pc hE hen hk
      omega
    exact ⟨fun _ => by rw [h0]; rfl, fun _ => h0⟩
  · intro k b n d e d' he _ _ hJ _ _ hev hne hn hm h
    simp only at h ⊢
    obtain ⟨h1, h2⟩ := el_site hev hne
    have hel : (if roleEl e then 1 else 0) = if d.site.isEl then 1 else 0 := by
      have hpc := el_pc.ok d.site
      cases hd : d.site.isEl with
      | true =>
        rw [hd] at hpc h2 h1
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hpc
        simp [roleEl, h1.mpr rfl, h2 rfl, hpc]
      | false =>
        have : isElectEv e = false := by
          rw [Bool.eq_false_iff]; intro h'; rw [h1.mp h'] at hd; cases hd
        simp [roleEl, this]
    rw [els_succ he, hel, polls_step hm]
    refine ⟨fun h14 => ?_, fun h15 => ?_⟩
    · have hi := h.1 h14
      rw [h14] at hm hn
      rcases hm.edge with hs | hs
      · simp only at hs
        have hnel : d.site.isEl = false := by
          rw [Bool.eq_false_iff]; exact fun h' => el_move hn h' hs
        rw [hs, tag_self, hnel]
        simpa using hi
      · have hc := tot_edges.ok hs
        simp only [totChk, show not14 14 = false from rfl, Bool.false_eq_true, ite_false,
          Bool.and_eq_true, beq_iff_eq] at hc
        omega
    · have hi := h.2 h15
      rw [h15] at hm hJ
      have hnel : d.site.isEl = false := by
        rw [Bool.eq_false_iff]
        intro h'
        have := hJ.tma (by revert h'; cases d.site <;> simp [Site.isEl, Site.isTma])
        omega
      simp [hnel, hi]
  · intro k dn hk h
    unfold els at h ⊢
    rw [List.take_of_length_le (by omega)] at h ⊢
    exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
