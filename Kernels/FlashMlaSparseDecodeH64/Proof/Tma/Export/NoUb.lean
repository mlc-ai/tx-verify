-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictGlue
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictRole
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Shape
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepFor
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.NoUbGather
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The TMA warp makes no undefined behaviour

`tma_noUb`: an event fired from a state of the TMA warp of a followed lane is no undefined
behaviour, and the machine stops at it only if it is the exit, when every read of the TMA warp's
code rebuilds a 32-bit word (`CoordWordsBits`, proved from the index warp's stores by
`coord_words_bits`). The state before the event is strictly good (`strict_event`: the step
before it is the TMA warp's strict step, `Tma.stepFor_site`, whose coordinate element is strict
for the bytes it read, `CoordWordsBits`), so the event is the template of its site
(`Tma/NoUbSite.lean`, `Tma/NoUbGather.lean`): the election's mask is the full warp, a length load
reads the row's word through a set pointer, the polls and the coordinate reads name aligned
addresses, and a gather has its map, destination, barrier and coordinate words (the words the
quadruples' loads kept are 32-bit words along the lane, `Tma.CoordInv`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The pcs of the coordinate loads are the TMA code's. -/
private theorem coord_pc_range {s : Tma.Site} (h : Tma.IsCoord s) :
    2162 ≤ s.pc ∧ s.pc < 2332 := by
  obtain ⟨k, hk⟩ := h
  rcases hk with rfl | rfl | rfl | rfl <;> revert k <;> decide

/-- **The coordinate words along the lane after its election are 32-bit words** where the machine
reads them. -/
private theorem tma_coord_inv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hcw : CoordWordsBits L X) (hw : MbarRow.warp L g = 5) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) {i : Nat}
    (hji : j < i) {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    SubR .tma (fun d => Tma.Post d.site ∧ Tma.CoordInv d) σ := by
  refine tma_region hp hX hFw Tma.CoordInv hj (fun d => Tma.coordInv_lead d) ?_ hji hσ
  intro i0 d a n f hσ0 hP hq hf ha
  refine Tma.coordInv_succ hq (fun hc x bs hk => ?_) ha
  have hub : ∀ fl, f.kind ≠ .ub fl := fun fl h => by rw [hk] at h; cases h
  have hget : X.get (g, i0) = some f := hf
  obtain ⟨σ', hσ', -, -, -, hpc⟩ := ev_at hp hX hFw hget hub
  rw [hσ0] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  have hr := coord_pc_range hc
  have hpc' : f.pc = d.site.pc := hpc
  obtain ⟨pc, kd⟩ := f
  simp only at hk hpc'
  subst hk
  exact hcw hget ⟨hw, by omega, by omega⟩

/-- With the extra cache off, the CTA's extra length word is zero. -/
private theorem lenWB_zero (hp : Pre P L m) (h0 : P.extra_topk = 0) :
    lenWB P L (g / L.block) = 0 := by
  unfold lenWB
  split
  · rw [h0]
    rfl
  · rename_i hne
    obtain ⟨x, hx⟩ := len_ptr (b := P.extraTopkLenBase) (by simpa using hne)
    have hm := hp.paramExtraTopkLen
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    have h := (hmem _ (ctaid_lt hp g).2 0 (by decide)).2 _ (ctaid_lt hp g).2
    rw [h0] at h
    rw [rowOf_cta, Nat.le_zero.mp h]
    rfl

/-- **The TMA warp makes no undefined behaviour.** -/
theorem tma_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hcw : CoordWordsBits L X)
    (g k : Nat) (e : Event) (he : X.get (g, k) = some e) (ha : AliveIn P L X g k .tma) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  have hg := Frame.lt_of_get hX he
  have hnb := noUbBefore_of_get hX he
  obtain ⟨t, o, ins, hgood, hc, hf⟩ := strict_event hp hX he hσ (.inr (.inr hr))
    (fun j dj ej hj hej hs hn hT d n hdj => by
      subst hdj
      have hget : X.get (g, j) = some ej := hej
      refine fun {t u} ins hat hinv hc hf => ?_
      refine thread_wg1_stepFor (wg1_inr_stepFor fun _ =>
        Tma.stepFor_site hp d ej fun hcd x bs hk => ?_) ins hat hinv hc hf
      have hub := hnb.ne (by omega) hget
      have hr' : 2162 ≤ ej.pc ∧ ej.pc < 2332 := by
        rw [hk]
        exact coord_pc_range hcd
      obtain ⟨-, -, -, -, -, hw⟩ := tma_at hp hX hFw hget hub hr'
      rw [hk] at hget hr'
      obtain ⟨z, hz⟩ := hcw hget ⟨hw, hr'.1, hr'.2⟩
      exact ⟨_, hz⟩)
  obtain ⟨hat, hinv⟩ := hgood
  have hJ := (follow_iff.mp hFw g hg k).2 σ hσ
  have hRole := state_role hJ hinv
  cases hr with
  | tma d n =>
    cases hRole with
    | tma d' n' hR hok hl hw hpc hrg =>
      have hu : n (.tma .ub) = 0 := (state_count hσ (.tma .ub)).trans (lane5_take_noUb hX he)
      have hcore := hR (state_ub hX hσ he) hu
      have hev := Tma.shape hp hat hinv.1 hc hf
      have hkind : Tma.EvK L g d e := hev.2
      have hu0 : ((X.tr g).take k).countP (cls .ub) = 0 :=
        (state_count hσ .ub).symm.trans (state_ub hX hσ he)
      have hub : ∀ f, e.kind ≠ .ub f := by
        cases hs : d.site with
        | elect => exact Tma.noUb_elect d hs hat hinv.1 hc hf
        | loadTopk => exact Tma.noUb_lens hp d hok (.inl hs) hat hinv.1 hc hf
        | loadExtra => exact Tma.noUb_lens hp d hok (.inr hs) hat hinv.1 hc hf
        | qWait => exact Tma.noUb_qWait hp d hs hat hinv.1 hc hf
        | storeWait => exact Tma.noUb_storeWait hp d hs hat hinv.1 hc hf
        | coordWait => exact Tma.noUb_coordWait hp d hs hat hinv.1 hc hf
        | rawWait => exact Tma.noUb_rawWait hp d hs hat hinv.1 hc hf
        | coord0 kk => exact Tma.noUb_coord hp d ⟨kk, .inl hs⟩ hat hinv.1 hc hf
        | coord1 kk => exact Tma.noUb_coord hp d ⟨kk, .inr (.inl hs)⟩ hat hinv.1 hc hf
        | coord2 kk => exact Tma.noUb_coord hp d ⟨kk, .inr (.inr (.inl hs))⟩ hat hinv.1 hc hf
        | coord3 kk => exact Tma.noUb_coord hp d ⟨kk, .inr (.inr (.inr hs))⟩ hat hinv.1 hc hf
        | gather kk =>
          have hloop : d.site.inLoop = true := by rw [hs]; rfl
          obtain ⟨hL, -⟩ := (Tma.core_loop hloop).mp hcore
          obtain ⟨-, -, -, -, -, hbuf, -⟩ := id hL
          obtain ⟨j, hjk, inst, hj⟩ := tma_won_at hp hX hFw hσ hcore (by rw [hs]; simp)
          obtain ⟨dI, nI, heqI, -, hI⟩ := tma_coord_inv hp hX hFw hcw hw hj hjk hσ
          obtain ⟨d3, n3, heq3, -, hw3, -⟩ := tma_win_state hp hX hFw hj hjk hσ hu0
          simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heqI heq3
          obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heqI
          obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq3
          have hmain : Tma.isMain d = true ∨ P.extra_topk ≠ 0 := by
            by_cases h0 : P.extra_topk = 0
            · obtain ⟨-, h1⟩ := tma_words_of_ok (by rw [hs]; simp) (by rw [hs]; simp) hw3
              exact .inl (Tma.isMain_of hL (h1.trans (lenWB_zero hp h0)))
            · exact .inr h0
          exact Tma.noUb_gather hp hg d ⟨kk, hs⟩ hI (Nat.mod_lt d.cnt.toNat (by decide))
            hbuf hmain hat hinv.1 hc hf
        | rawArrive | coordFree | outBar | exit =>
          simp only [Tma.EvK, hs] at hkind
          rw [hkind]
          intro f h
          cases h
        | leave s => exact absurd hs (hl s)
      refine ⟨hub, fun hs => ?_⟩
      have hn : Tma.succ P L g d e = none := thread_next_none_sub (next_none_of_stops he hσ hs)
      obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
      cases site with
      | exit => simpa only [Tma.EvK] using hkind
      | leave s => exact absurd rfl (hl s)
      | elect =>
        simp only [Tma.EvK] at hkind
        rcases hkind with ⟨inst, ld, hk⟩ | ⟨f, hk⟩
        · simp [Tma.succ, Tma.electNext, hk] at hn
        · exact absurd hk (hub f)
      | loadTopk =>
        rw [Tma.tma_topk hp hX he hok hat hc hf rfl] at hn
        cases hn
      | loadExtra =>
        rw [Tma.tma_extra hp hX he hok hat hc hf rfl] at hn
        cases hn
      | qWait | storeWait | coordWait | rawWait =>
        simp only [Tma.EvK, Tma.Poll] at hkind
        rcases hkind with ⟨ok, hk⟩ | ⟨f, hk⟩
        · simp [Tma.succ, Tma.poll, hk] at hn
        · exact absurd hk (hub f)
      | coord0 kk | coord1 kk | coord2 kk | coord3 kk =>
        simp only [Tma.EvK, RdAt] at hkind
        rcases hkind with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
        · simp [Tma.succ, Tma.rdAny, hk] at hn
        · exact absurd hk (hub f)
      | gather kk => simp [Tma.succ] at hn
      | rawArrive => simp [Tma.succ] at hn
      | coordFree => simp [Tma.succ] at hn
      | outBar => simp [Tma.succ] at hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
