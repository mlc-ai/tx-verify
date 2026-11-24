-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingPairHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Lemmas.Flow.Final
import Lemmas.Flow.NthEv

@[expose] public section

/-! # Actual producers of the softmax peer exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSources

open PTX PTX.Flow Wg0 Wg0PeerOrder Wg0PeerTrace MachineTracking

private def exchangePhase : Wg0.Site → Option Nat
  | .exchStore j => some j.val
  | .pairBar => some 8
  | _ => none

private theorem role_previous {P : Params} {L : Launch} {g n : Nat}
    {d prev : D} {e : Event} (hn : Wg0.next P L g prev e = some (some d))
    (hd : exchangePhase d.site = some (n + 1)) :
    exchangePhase prev.site = some n ∧ prev.block = d.block := by
  cases hs : prev.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hs] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp [exchangePhase] at hd
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp [exchangePhase] at hd
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [exchangePhase, Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink,
    Wg0.epiAfterBar, Wg0.loadScores, Wg0.init, Wg0.Site.elems]
  all_goals try split_ifs at hd
  all_goals exact Nat.le_antisymm (Nat.le_of_lt_succ (Fin.isLt _)) (by assumption)

private theorem machine_previous {P : Params} {L : Launch} {g n : Nat}
    {s : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g s e = some (some (.wg0 d)))
    (hd : exchangePhase d.site = some (n + 1)) :
    ∃ prev : D, s = .wg0 prev ∧ exchangePhase prev.site = some n ∧ prev.block = d.block := by
  cases s
  case wg0 prev =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q hq
      cases hn
      exact ⟨prev, rfl, role_previous hq hd⟩
    · split at hn <;> cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case prologue prev =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals try cases hn
    all_goals rename_i w _ _
    all_goals fin_cases w <;> cases hn
    all_goals
      unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen at hd
      dsimp only at hd
      split_ifs at hd <;> cases hd
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem prior_exchange {P : Params} {L : Launch} {X : Execution}
    {g j n : Nat} {group : Fin 8} {d : D}
    (hlen : j ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hd : exchangePhase d.site = some (group.val + n)) :
    ∃ i q, i + n = j ∧ q.site = .exchStore group ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 q)) := by
  induction n generalizing j d with
  | zero =>
    have hsite : d.site = .exchStore group := by
      have hg := group.isLt
      cases hp : d.site <;> simp [exchangePhase, hp] at hd
      · exact congrArg Wg0.Site.exchStore (Fin.ext hd)
      · omega
    exact ⟨j, d, rfl, hsite, rfl, hs⟩
  | succ n ih =>
    cases j with
    | zero => rw [Frame.stateAt_zero] at hs; cases hs
    | succ j =>
      have hj : j < (X.tr g).length := by omega
      have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [Frame.stateAt_succ (C := Machine.code P L) he] at hs
      cases hp : Frame.stateAt (Machine.code P L) X g j with
      | none => simp [hp] at hs
      | some st =>
        cases st with
        | none => simp [hp] at hs; cases hs
        | some s =>
          rw [hp, Option.bind_some] at hs
          obtain ⟨prev, rfl, hphase, hblock⟩ := machine_previous hs hd
          obtain ⟨i, q, hi, hq, hqb, hstate⟩ := ih hj.le hp hphase
          exact ⟨i, q, by omega, hq, hqb.trans hblock, hstate⟩

/-- Every actual pair barrier was preceded by the selected store of that same block. -/
theorem exchange_before_pair {P : Params} {L : Launch} {X : Execution}
    {g j : Nat} {d : D} {e : Event}
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .pairBar) (group : Fin 8) :
    ∃ i < j, ∃ (q : D) (ew : Event),
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧ X.get (g, i) = some ew := by
  have hg := group.isLt
  have hphase : exchangePhase d.site = some (group.val + (8 - group.val)) := by
    simp only [hsite, exchangePhase, Option.some.injEq]
    omega
  obtain ⟨i, q, hi, hq, hb, hst⟩ :=
    prior_exchange (PTX.len_of_get he).le hd hphase
  have hlt : i < j := by omega
  have hlen : i < (X.tr g).length := hlt.trans (PTX.len_of_get he)
  exact ⟨i, hlt, q, (X.tr g)[i], hst, hq, hb, List.getElem?_eq_getElem hlen⟩

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

/-- The source of a peer load is the same lane in the other warp of its named pair. -/
def partner (L : Launch) (g : Nat) : Nat :=
  ctaOf L g * L.block + (32 * (warpOf L g ^^^ 2) + laneOf L g)

private theorem partner_geometry {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warpOf L g < 4) :
    SameCta L (partner L g) g ∧ wgOf L (partner L g) = 0 ∧
      warpOf L (partner L g) ^^^ 2 = warpOf L g ∧
      warpOf L (partner L g) % 2 = warpOf L g % 2 ∧ laneOf L (partner L g) = laneOf L g := by
  let w := warpOf L g ^^^ 2
  let t := 32 * w + laneOf L g
  have hbit : ∀ w : Fin 4,
      (w.val ^^^ 2) < 4 ∧ (w.val ^^^ 2) ^^^ 2 = w.val ∧ (w.val ^^^ 2) % 2 = w.val % 2 := by
    decide
  have hb : w < 4 ∧ w ^^^ 2 = warpOf L g ∧ w % 2 = warpOf L g % 2 :=
    hbit ⟨warpOf L g, hw⟩
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have ht : t < L.block := by rw [hpre.block]; dsimp [t]; omega
  have hCta : ctaOf L (partner L g) = ctaOf L g := by
    change (ctaOf L g * L.block + t) / L.block = _
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt ht),
      Nat.div_eq_of_lt ht, Nat.zero_add]
  have htid : tidOf L (partner L g) = t := by
    rw [tidOf_eq hpre]
    change (ctaOf L g * L.block + t) % 384 = t
    have ht' : t < 384 := hpre.block ▸ ht
    rw [hpre.block, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht']
  have hWarp : warpOf L (partner L g) = w := by unfold warpOf; rw [htid]; dsimp [t]; omega
  have hLane : laneOf L (partner L g) = laneOf L g := by
    unfold laneOf at ⊢
    rw [htid]
    change t % 32 = laneOf L g
    dsimp only [t]
    omega
  exact ⟨⟨NamedBar.cta_thread_lt (NamedBar.cta_lt hg) ht, hg, hCta⟩,
    by unfold wgOf; rw [htid]; dsimp [t]; omega, hWarp ▸ hb.2.1, hWarp ▸ hb.2.2, hLane⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The passed pair barrier has its actual producer's arrival in that same block, whether the
producer is still in the warp pair or has already exited the kernel. -/
theorem actual_partner_pair_before_read {g i cut : Nat} {d : D} {e : Event} {group : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hr : d.site = .peerRead group) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := partner L g
    ∃ wb rb tagw tagr dw dr, rb < i ∧ SameCta L w g ∧
      X.IsBarrier (w, wb) (10 + warpOf L g % 2) (some 64) tagw ∧
      X.IsBarrier (g, rb) (10 + warpOf L g % 2) (some 64) tagr ∧
      Frame.stateAt (Machine.code P L) X w wb = some (some (.wg0 dw)) ∧
      Frame.stateAt (Machine.code P L) X g rb = some (some (.wg0 dr)) ∧
      dw.site = .pairBar ∧ dw.block = d.block ∧ dr.block = d.block := by
  dsimp only
  let p : Fin 2 := ⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩
  let w := partner L g
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hv, _, _⟩ := Frame.fired_site hs hX he hd
  have hinv : Wg0.Inv P L g d := hv
  obtain ⟨hcta, hwg, _, hSamePar, _⟩ := partner_geometry hpre hg hinv.warpLt
  have hw := hcta.1
  obtain ⟨rb, hrb, tagr, dr, hreader, hsReader, hsr, hbr⟩ :=
    pair_before_read hpre hX (hs g hg).machine he hd hr
  have hreaderOrd := pairOrdinal hpre hX (hs g hg).machine hreader hsReader hsr
  have hpassed : rb + 1 < (X.tr g).length := by
    have hi : i < (X.tr g).length := PTX.len_of_get he
    omega
  have hwarp : (w % L.block) / 32 ∈ pairWarps p := by
    have hh : warpOf L w < 4 := by
      change tidOf L w / 128 = 0 at hwg
      unfold warpOf
      omega
    have hp : warpOf L w % 2 = p.val := hSamePar
    have hm : warpOf L w ∈ pairWarps p := by
      simp only [pairWarps, Finset.mem_insert, Finset.mem_singleton]
      omega
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using hm
  have hexited (hex : ∃ j tag, X.get (w, j) = some ⟨tag, .exit⟩) :
      ∃ wb tagw, X.IsBarrier (w, wb) (10 + p.val) (some 64) tagw ∧
        ((X.tr w).take wb).countP (Execution.isBarId (10 + p.val)) =
          ((X.tr g).take rb).countP (Execution.isBarId (10 + p.val)) := by
    obtain ⟨j, tag, hj⟩ := hex
    have hcount := pair_count_before_softmax_exit hpre hX hs hwg hj
    have hBlocks : blocksOf P L w = blocksOf P L g := by
      have hCta : ctaOf L w = ctaOf L g := hcta.2.2
      simp only [blocksOf, eOf, ctaidY, hCta]
    rw [hSamePar, hBlocks] at hcount
    obtain ⟨wb, eb, _, hget, his, hord⟩ :=
      exists_nthEv (n := d.block) (hinv.blockLt.trans_le hcount)
    obtain ⟨tagw, cnt, mode, hkind⟩ := NamedBar.isBarId_form his
    rw [hkind] at hget
    obtain ⟨_, _, hcnt, hmode⟩ :=
      actual_pair_bar (p := p) hpre hX hs hget
    rw [hcnt, hmode] at hget
    exact ⟨wb, tagw, hget, hord.trans (hbr.symm.trans hreaderOrd.symm)⟩
  obtain ⟨wb, tagw, hwriter, hsameOrd⟩ :=
    (pairSources hpre hX hs p).member_arrival hX (pairShape hpre p)
      hreader hpassed hcta.2.2 hwarp hexited
  have hf : Frame.stateAt (Machine.code P L) X w wb ≠ some none := by
    intro hDismiss
    obtain ⟨j, hj, hBad⟩ := prior_dismissal (PTX.len_of_get hwriter).le hDismiss
    exact hPrior (w, j) ((pairSources hpre hX hs p).same_ordinal_baseCausality hX
      (pairShape hpre p) hcta hwriter hreader hpassed hsameOrd hj (hrb.trans_le hCut) hLen) hBad
  obtain ⟨q, _, hsw, hFire⟩ :=
    RingSourceSites.fired_at_followed hX (hs w hw).machine hf hwriter (by simp)
  obtain ⟨dw, rfl, hSite, _, _, _, _⟩ := pair_fired (p := p) hpre hFire rfl
  have hwOrd := pairOrdinal hpre hX (hs w hw).machine hwriter hsw hSite
  rw [hSamePar] at hwOrd
  exact ⟨wb, rb, tagw, tagr, dw, dr, hrb, hcta, hwriter, hreader, hsw, hsReader, hSite,
    hwOrd.symm.trans (hsameOrd.trans (hreaderOrd.trans hbr)), hbr⟩

/-- Each actual peer read has its partner's actual store, with exact shared footprints and
write-to-read base causality in the block's named barrier generation. -/
theorem actual_source_of_read {g i cut : Nat} {d : D} {group : Fin 8} {ac : Acc}
    {values : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hread : X.Reads (g, i) ac values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hr : d.site = .peerRead group) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := partner L g
    ∃ (j : Nat) (q : D) (a : Acc) (bytes : List Byte),
      Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧ X.Writes (w, j) a bytes ∧
      bytes = (exchangeValue q group.val).toBytes ∧
      ac.loc = a.loc.at (8 * d.sub) ∧ a.size = 16 ∧ ac.size = 8 ∧ d.sub < 2 ∧
      baseCausality L X (w, j) (g, i) := by
  dsimp only
  let w := partner L g
  let p : Fin 2 := ⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩
  have he := hread.choose_spec
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hv, _, _⟩ := Frame.fired_site hs hX he hd
  have hinv : Wg0.Inv P L g d := hv
  obtain ⟨wb, rb, tagw, tagr, dw, dr, hrb, hcta, hwb, hrbEvent, hsw, hsr, hsite, hwbl, hrbl⟩ :=
    actual_partner_pair_before_read hpre hX hs he hd hr hCut hLen hPrior
  obtain ⟨j, hjw, q, ew, hq, hqsite, hqb, hew⟩ := exchange_before_pair hwb hsw hsite group
  have hnoEnd : ¬ Ends ew := by
    intro h
    obtain ⟨_, hrun⟩ := hX.thr w hcta.1
    have hlast := PTX.Flow.Run.end_last hrun hew h
    have hlen : wb < (X.tr w).length := PTX.len_of_get hwb
    omega
  obtain ⟨_, _, hwarp, _, hlane⟩ := partner_geometry hpre hg hinv.warpLt
  obtain ⟨a, bytes, ac', values', hw, hread', hbytes, hloc, hsize, hreadSize, hsub⟩ :=
    matching_accesses hpre hX hs hew he hq hd hqsite hr
      (fun h => hnoEnd (.inr h)) (by simp)
      (fun f h => hnoEnd (.inl ⟨f, h⟩)) (by simp) hcta.2.2 hlane hwarp
  have hacc : ac = ac' := (Kind.rd.inj
    (congrArg Event.kind (Option.some.inj (he.symm.trans hread'.choose_spec)))).1
  subst ac'
  have hord := same_block_order (p := p) hpre hX hs hcta hwb hrbEvent hsw hsr
    (hwbl.trans hrbl.symm) hjw hrb (PTX.len_of_get he)
  exact ⟨j, q, a, bytes, hq, hqsite, hqb.trans hwbl, hw, hbytes, hloc, hsize, hreadSize, hsub, hord⟩

/-- The producer of a tracked peer read is its partner lane in the same block. -/
theorem source_of_read {g i : Nat} {d : D} {group : Fin 8} {ac : Acc} {values : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hread : X.Reads (g, i) ac values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hr : d.site = .peerRead group) :
    let w := partner L g
    ∃ (j : Nat) (q : D) (a : Acc) (bytes : List Byte),
      Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧ X.Writes (w, j) a bytes ∧
      bytes = (exchangeValue q group.val).toBytes ∧
      ac.loc = a.loc.at (8 * d.sub) ∧ a.size = 16 ∧ ac.size = 8 ∧ d.sub < 2 ∧
      baseCausality L X (w, j) (g, i) :=
  actual_source_of_read hpre hX hs hread hd hr le_rfl (PTX.len_of_get hread.choose_spec)
    (fun t _ => tracked_not_dismisses hX ht t)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSources
