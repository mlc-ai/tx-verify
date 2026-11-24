-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatValsIndex
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The site of a statistics store from its word and its named-barrier ordinal

A softmax lane's store of word 1 is its final store 1; a store of word 0 is a round's factor store
when its ordinal on the barrier with the correction warps is below the tile's rounds, and the final
store 0 when it is the rounds (`soft_stat_site`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (lz ptsOf passed before inBias inPlain preR Site)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h i : Nat}

theorem softRounds_eq {N : Nat} (hN : SoftRounds p L h N) : Values.softRounds p L h = N := by
  have hex : ∃ N, SoftRounds p L h N := ⟨N, hN⟩
  unfold Values.softRounds
  rw [dite_eq_left hex]
  exact hex.choose_spec.unique hN

private theorem nb_tab (b : Bool) : (∀ pl, (ptsOf b .nb).countP (before (.stat pl)) = 1 ∧
      (ptsOf b (.acquire 80)).countP (before (.stat pl)) = 2) ∧
    (∀ j, (ptsOf b .nb).countP (before (.fin j)) = 1 ∧
      (ptsOf b .sst).countP (before (.fin j)) = j.val) ∧
    (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 ∧
    (ptsOf b .sst).countP inBias = 1 ∧ (ptsOf b .sst).countP inPlain = 1 ∧
    (ptsOf b (.acquire 80)).countP inBias = 1 ∧ (ptsOf b (.acquire 80)).countP inPlain = 1 := by
  cases b <;> decide +kernel

private theorem stat_reg : ∀ pl, preR (.stat pl) = false ∧
    (inBias (Site.stat pl).pos = true ∨ inPlain (Site.stat pl).pos = true) := by
  decide +kernel

/-- **The site of a statistics store.** -/
theorem soft_stat_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h < 8) {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) :
    ∃ s : Site, pc = s.pc ∧ Softmax.StatWord L h (Softmax.statIx s) a ∧
      ((∃ pl, s = .stat pl ∧ Tm.sPolls L X h (Prologue.warpIndex L h / 4) i =
          barOrd X h i (Prologue.warpIndex L h + 3) + 1 ∧
          ∀ N, SoftRounds p L h N → barOrd X h i (Prologue.warpIndex L h + 3) < N) ∨
        ∃ j, s = .fin j ∧ ∀ N, SoftRounds p L h N →
          barOrd X h i (Prologue.warpIndex L h + 3) = N) := by
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev⟩
  · exfalso
    have hx : exit L h s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
    | _ => simp [Startup.Ev] at hev
  have hpc : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hev1 := hev.1
  have hsd : d.scheduler.site = d.site := rfl
  have hs : (∃ r, d.site = .stat r) ∨ ∃ r, d.site = .fin r := by
    cases hs : d.site <;> simp only [Softmax.Ev, hsd, hs] at hev1
    case stat r => exact .inl ⟨r, rfl⟩
    case fin r => exact .inr ⟨r, rfl⟩
    all_goals exfalso
    all_goals try simp only [Epilogue.Ev, Softmax.Site.toE, Softmax.tcLdOrUb] at hev1
    all_goals repeat' split at hev1
    all_goals first | contradiction | simp_all [Softmax.rdOrUb]
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hword := Softmax.stat_word hp (d := d.scheduler) hat (by
    have h := hi'.1
    change Softmax.Control.Inv d at h
    change (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
    rcases hs with ⟨pl, h0⟩ | ⟨k, h0⟩ <;> simp only [Softmax.Control.Inv, h0] at h <;>
      (rw [h0]; exact h)) hc hf hs rfl
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := nb_tab (lz L h)
  have hB : barOrd X h i (Prologue.warpIndex L h + 3) = c .nb := by
    unfold barOrd
    rw [soft_isBarId hw, count hσ, hLk _ rfl]
  have hnb := hQ.cnt .nb rfl
  refine ⟨d.site, hpc, hword, ?_⟩
  rcases hs with ⟨pl, hs⟩ | ⟨j, hs⟩
  · left
    have hs' : d.scheduler.site = .stat pl := hs
    have hS := ((Softmax.tm_counts hw hσ).1.trans (hLk _ rfl).symm).trans (hQ.cnt (.acquire 80) rfl)
    simp only [passed, hs', (t1 pl).1, t3, t4, Nat.mul_one] at hnb
    simp only [passed, hs', (t1 pl).2, t7, t8, Nat.mul_one] at hS
    refine ⟨pl, hs, by omega, fun N hN => ?_⟩
    obtain ⟨r1, r2⟩ := stat_reg pl
    obtain ⟨T, hT, -, h3⟩ := soft_round_lt hQ hF (by rw [hs']; rfl) (by rw [hs']; rfl)
      (by rw [hs']; exact .inr r2)
    obtain rfl := hN.unique hT
    have := h3.resolve_left (by rw [hs', r1]; simp)
    omega
  · right
    have hs' : d.scheduler.site = .fin j := hs
    obtain ⟨h1, h2⟩ := Softmax.final_ordinal hQ hF hs'
    change c .sst = _ at h1
    have hst := hQ.cnt .sst rfl
    change c .sst = _ at hst
    simp only [passed, hs', (t2 j).1, t3, t4, Nat.mul_one] at hnb
    simp only [passed, hs', (t2 j).2, t5, t6, Nat.mul_one] at hst
    refine ⟨j, hs, fun N hN => ?_⟩
    rw [softRounds_eq hN] at h1 h2
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
