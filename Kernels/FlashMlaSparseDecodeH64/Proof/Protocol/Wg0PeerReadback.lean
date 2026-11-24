-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingPairHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Lemmas.Flow.NthEv
import Lemmas.Flow.Final

@[expose] public section

/-! # Read-back of the softmax peer exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback

open PTX PTX.Flow PTX.Proof Wg0 MachineTracking

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

private def count9 (X : Execution) (g i : Nat) : Nat :=
  ((X.tr g).take i).countP (Execution.isBarId 9)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem bar9_before_count {g i n : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hcount : n < count9 X g i) :
    ∃ j < i, ∃ tag, X.IsBarrier (g, j) 9 (some 128) tag ∧ count9 X g j = n := by
  obtain ⟨j, e, hji, he, hb, hord⟩ := exists_nthEv (p := Execution.isBarId 9) (X := X)
    (g := g) (k := i) (n := n) hcount
  obtain ⟨tag, cnt, mode, hk⟩ := NamedBar.isBarId_form hb
  rw [hk] at he
  obtain ⟨_, hcnt, hmode⟩ := MachineTracking.actual_bar9 hpre hX hs he
  rw [hcnt, hmode] at he
  exact ⟨j, hji, tag, he, hord⟩

/-- When two accesses are on different sides of a warpgroup barrier ordinal, that named
barrier orders them. The source lane may already have exited. -/
theorem order_of_bar9_counts {g h i j : Nat} {e f : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hc : SameCta L g h) (hwarp : warpOf L g < 4)
    (hWG : wgOf L g = 0) (he : X.get (g, i) = some e) (hf : X.get (h, j) = some f)
    (hnonbar : Execution.isBarId 9 e = false)
    (hcount : ((X.tr g).take i).countP (Execution.isBarId 9) <
      ((X.tr h).take j).countP (Execution.isBarId 9))
    (hbound : ((X.tr g).take i).countP (Execution.isBarId 9) < 2 * blocksOf P L g + 2) :
    baseCausality L X (g, i) (h, j) := by
  let phase := count9 X g i
  obtain ⟨rb, hrb, tagr, hreader, hro⟩ :=
    bar9_before_count hpre hX hs (n := phase) hcount
  have hj : j < (X.tr h).length := PTX.len_of_get hf
  have hp : rb + 1 < (X.tr h).length := by omega
  have hmember : (g % L.block) / 32 ∈ OutputPublication.stagingWarps := by
    simpa only [OutputPublication.stagingWarps, Finset.mem_range, warpOf, tidOf_eq hpre,
      hpre.block] using hwarp
  have hexited (hex : ∃ k tag, X.get (g, k) = some ⟨tag, .exit⟩) :
      ∃ tagIndex tag, X.IsBarrier (g, tagIndex) 9 (some 128) tag ∧
        count9 X g tagIndex = count9 X h rb := by
    obtain ⟨k, tag, hget⟩ := hex
    have hExit := (MachineTracking.barrier_counts_before_softmax_exit hpre hX hs hWG hget).2
    obtain ⟨wb, _, tagw, hwriter, hwo⟩ :=
      bar9_before_count hpre hX hs (hbound.trans_le hExit)
    exact ⟨wb, tagw, hwriter, hwo.trans hro.symm⟩
  have hSrc := OutputPublication.actual_sources hpre hX hs
  have hShape := OutputPublication.shape hpre
  obtain ⟨wb, tagw, hwriter, hwo⟩ :=
    hSrc.member_arrival hX hShape hreader hp hc.2.2 hmember hexited
  have hbar : Execution.isBarId 9 ⟨tagw, .bar 9 (some 128) .sync⟩ = true := rfl
  have hiw : i < wb := by
    by_contra! hn
    have heq : i ≠ wb := by
      intro hh
      subst i
      have hk := Option.some.inj (he.symm.trans hwriter)
      rw [hk, hbar] at hnonbar
      contradiction
    have hstep := countP_take_succ hwriter hbar
    have hle := countP_take_mono (Execution.isBarId 9) (X.tr g)
      (show wb + 1 ≤ i by omega)
    change count9 X g (wb + 1) ≤ count9 X g i at hle
    change count9 X g (wb + 1) = count9 X g wb + 1 at hstep
    change count9 X g wb = count9 X h rb at hwo
    rw [hstep, hwo, hro] at hle
    exact (Nat.not_succ_le_self _ hle).elim
  exact hSrc.same_ordinal_baseCausality hX hShape hc hwriter hreader hp hwo hiw hrb hj

/-- Overlapping exchange stores belong to the same lane and vector group. -/
theorem exchange_overlap {P : Params} {L : Launch} {mem0 : Mem0}
    {g h : Nat} {j k : Fin 8} {a b : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hg : warpOf L g < 4) (hh : warpOf L h < 4)
    (ha : a.loc = shLoc L g (exchangeBase + exchangeQuad * (warpOf L g ^^^ 2) +
      16 * laneOf L g + exchangeChunk * j.val))
    (hb : b.loc = shLoc L h (exchangeBase + exchangeQuad * (warpOf L h ^^^ 2) +
      16 * laneOf L h + exchangeChunk * k.val))
    (hs : a.size = 16) (ht : b.size = 16) (hac : a.Covers l) (hbc : b.Covers l) :
    g = h ∧ j = k := by
  obtain ⟨_, hcg, hag₁, hag₂⟩ := hac
  obtain ⟨_, hch, hah₁, hah₂⟩ := hbc
  rw [ha] at hcg hag₁ hag₂
  rw [hb] at hch hah₁ hah₂
  rw [hs] at hag₂
  rw [ht] at hah₂
  simp only [shLoc, exchangeBase, exchangeQuad, exchangeChunk] at hcg hch hag₁ hag₂ hah₁ hah₂
  have hlg : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hlh : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hj := j.isLt
  have hk := k.isLt
  have hXor : warpOf L g ^^^ 2 = warpOf L h ^^^ 2 := by omega
  have hGroup : j.val = k.val := by omega
  have hLane : laneOf L g = laneOf L h := by omega
  have cancel : ∀ w : Fin 4, (w.val ^^^ 2) ^^^ 2 = w.val := by decide
  have hWarp : warpOf L g = warpOf L h :=
    (cancel ⟨_, hg⟩).symm.trans ((congrArg (· ^^^ 2) hXor).trans (cancel ⟨_, hh⟩))
  have hCta := hcg.symm.trans hch
  have hTid : tidOf L g = tidOf L h := by
    unfold warpOf at hWarp
    unfold laneOf at hLane
    omega
  unfold ctaOf at hCta
  rw [tidOf_eq hpre, tidOf_eq hpre] at hTid
  rw [hpre.block] at hCta
  exact ⟨by omega, Fin.ext hGroup⟩

private theorem not_swap_to_pair {P : Params} {L : Launch} {g : Nat} {d q : D} {e : Event}
    {j : Fin 8} (hd : d.site = .exchStore j) (hq : q.site = .pairBar)
    (hn : Machine.next P L g (.wg0 d) e = some (some (.wg0 q))) : j.val + 1 = 8 := by
  have hlt := j.isLt
  by_contra hne
  have h : j.val + 1 < 8 := by omega
  cases he : e.kind <;>
    simp only [Machine.next, Wg0.next, Wg0.nextSite, Wg0.writeStep, hd, he, h, ↓reduceDIte] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    rename_i heq
    split_ifs at heq <;> cases heq <;> simp_all

private theorem exchange_to_pair {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i k tag : Nat} {e : Event} {d q : D} {group : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hstore : d.site = .exchStore group)
    (hb : X.IsBarrier (g, k) (10 + warpOf L g % 2) (some 64) tag)
    (hq : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 q)))
    (hsite : q.site = .pairBar) (hblock : d.block = q.block) (hik : i < k) :
    i + (8 - group.val) = k := by
  have hg := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := PTX.len_of_get hb
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  cases o with
  | none =>
    obtain ⟨_, hrun⟩ := hX.thr g hg
    obtain ⟨_, _, hFire⟩ := hf
    have hlast := PTX.Flow.Run.end_last hrun he (fires_none_ends hFire)
    omega
  | some u =>
    obtain ⟨d', hnext, hblk, hnextSite⟩ := Wg0.composed_exchange_next hpre hstore hf
    have hstate := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd] at hstate
    change Frame.stateAt (Machine.code P L) X g (i + 1) = Machine.next P L g (.wg0 d) e at hstate
    rw [hnext] at hstate
    have hNextLen : i + 1 < (X.tr g).length := by omega
    have hget : X.get (g, i + 1) = some (X.tr g)[i + 1] :=
      List.getElem?_eq_getElem hNextLen
    rcases hnextSite with ⟨grp, hgrp, hnextSite⟩ | hnextSite
    · have hlt : i + 1 < k := by
        by_contra! hn
        have hh : i + 1 = k := by omega
        rw [hh, hq] at hstate
        have heq := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hstate))
        rw [heq, hnextSite] at hsite
        cases hsite
      have hrec := exchange_to_pair hpre hX hs hget hstate hnextSite hb hq hsite
        (hblk.trans hblock) hlt
      have hgr := grp.isLt
      omega
    · have hlast := not_swap_to_pair hstore hnextSite hnext
      have h' := Wg0PeerTrace.pairOrdinal hpre hX hs hget hstate hnextSite
      have h'' := Wg0PeerTrace.pairOrdinal hpre hX hs hb hq hsite
      have hKind : (X.tr g)[i + 1].kind = .bar (10 + warpOf L g % 2) (some 64) .sync := by
        obtain ⟨_, hFire⟩ := (hs.produces (hX.thr g hg)).fired_at hget hstate
        exact Wg0PeerTrace.pair_kind hpre hFire hnextSite
      have hbar : Execution.isBarId (10 + warpOf L g % 2) (X.tr g)[i + 1] = true := by
        simp [Execution.isBarId, hKind]
      have hpos := nthEv_unique hget hbar hb (by simp [Execution.isBarId])
        (h'.trans ((hblk.trans hblock).trans h''.symm))
      omega
termination_by k - i
decreasing_by omega

private theorem before_named {X : Execution} {g i k id tag : Nat} {e : Event}
    {n : Option Nat}
    (he : X.get (g, i) = some e) (hnonbar : Execution.isBarId id e = false)
    (hk : X.IsBarrier (g, k) id n tag)
    (hord : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr g).take k).countP (Execution.isBarId id)) :
    i < k := by
  have hb : Execution.isBarId id ⟨tag, .bar id n .sync⟩ = true := by
    simp [Execution.isBarId]
  by_contra! hle
  have hne : i ≠ k := by
    intro hh
    subst i
    have hkind := Option.some.inj (he.symm.trans hk)
    rw [hkind, hb] at hnonbar
    contradiction
  have hmore := countP_take_succ hk hb
  have hMono := countP_take_mono (Execution.isBarId id) (X.tr g)
    (show k + 1 ≤ i by omega)
  rw [hmore, hord] at hMono
  omega

/-- Every other writer at a peer byte is the selected store, precedes that store, or
follows the read. Probability stores share the allocation and are ordered by barrier nine. -/
theorem competing_write_order {g i j cut : Nat} {d q : D} {group : Fin 8} {ac a fp : Acc}
    {v : List (Option Byte)} {bytes raw : List Byte} {other : AsyncCopy.Ref} {k : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hr : X.Reads (g, i) ac v)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hw : X.Writes (Wg0PeerSources.partner L g, j) a bytes)
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)))
    (hqs : q.site = .exchStore group) (hblock : q.block = d.block)
    (hloc : ac.loc = a.loc.at (8 * d.sub)) (hasize : a.size = 16) (hk : k < ac.size)
    (hm : X.MemWrites other fp raw) (hc : fp.Covers (ac.loc.at k)) :
    other = .thread (Wg0PeerSources.partner L g, j) ∨
      ByteCausality L X (ac.loc.at k) other (.thread (Wg0PeerSources.partner L g, j)) ∨
      ByteCausality L X (ac.loc.at k) (.thread (g, i)) other := by
  let w := Wg0PeerSources.partner L g
  let l := ac.loc.at k
  obtain ⟨ha, hrsize, hInv, hsub⟩ := Wg0PeerWrites.read_geometry hpre hX hs hr hd hsite
  have hbits := hInv.warpLt
  have hlane := hInv.laneLt
  have hgrp := group.isLt
  have hsh : l.space = .shared := by simp [l, Loc.at, ha, shLoc]
  have hlow : L.sharedBase + 204800 ≤ l.addr := by
    simp only [l, Loc.at, ha, shLoc, exchangeBase]
    omega
  have hhigh : l.addr < L.sharedBase + 221184 := by
    simp only [l, Loc.at, ha, shLoc, exchangeBase, exchangeQuad, exchangeChunk]
    omega
  have hac : a.Covers l := by
    rw [hrsize] at hk
    simp only [l, hloc, Loc.at, Acc.Covers, Loc.InRange, hasize, true_and]
    omega
  obtain ⟨s, t, rfl, hsWrite, hss, hWg, hWarp, hShape⟩ :=
    Wg0PeerWrites.actual_covered_write hpre hX hs hm hc hsh hlow hhigh
  have hsGet := hsWrite.choose_spec
  have hwGet := hw.choose_spec
  have hrGet := hr.choose_spec
  have hg := Frame.lt_of_get hX hrGet
  have hslt := Frame.lt_of_get hX hsGet
  have hwlt := Frame.lt_of_get hX hwGet
  have hrs : l.cta = ctaOf L g := by simp [l, Loc.at, ha, shLoc]
  obtain ⟨hCtaW, _, hqState, hInvQ, hShapeQ⟩ :=
    Wg0PeerWrites.ordinary_at_followed (i := (w, j)) hpre hX hs hq hw hac hsh hlow hhigh
  have hqEq := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj (hq.symm.trans hqState)))
  subst q
  have hws : l.cta = ctaOf L w := hac.2.1.trans hCtaW
  have hreadCount := Wg0BarrierCount.peerCount hpre hX (hs g hg).machine hrGet hd (.inl hsite)
  have hwriteCount :=
    Wg0BarrierCount.peerCount hpre hX (hs w hwlt).machine hwGet hq (.inr hqs)
  rw [hblock] at hwriteCount
  have hOlder (hcount : count9 X s t < 2 * d.block + 1) :
      ByteCausality L X l (.thread (s, t)) (.thread (w, j)) := by
    have hBlocks : blocksOf P L s = blocksOf P L g := by
      have hCta := hss.symm.trans hrs
      simp only [blocksOf, eOf, ctaidY, hCta]
    have hBound := hInv.blockLt
    apply ByteCausality.direct
    exact .inl (order_of_bar9_counts hpre hX hs ⟨hslt, hwlt, hss.symm.trans hws⟩
      hWarp hWg hsGet hwGet rfl (by rw [hwriteCount]; exact hcount) (by
        change count9 X s t < _
        omega))
  have hLater (hcount : 2 * d.block + 1 < count9 X s t) :
      ByteCausality L X l (.thread (g, i)) (.thread (s, t)) := by
    have hBound := hInv.blockLt
    apply ByteCausality.direct
    exact .inl (order_of_bar9_counts hpre hX hs ⟨hg, hslt, hrs.symm.trans hss⟩
      hInv.warpLt hInv.wg hrGet hsGet rfl (by rw [hreadCount]; exact hcount)
      (by rw [hreadCount]; omega))
  rcases lt_trichotomy (count9 X s t) (2 * d.block + 1) with hBefore | hEqual | hAfter
  · exact .inr (.inl (hOlder hBefore))
  · rcases hShape with ⟨uGroup, hSizeU, hLocU, hCountU⟩ | ⟨m, hm⟩
    · have hqLoc : a.loc = shLoc L w (exchangeBase + exchangeQuad * (warpOf L w ^^^ 2) +
          16 * laneOf L w + exchangeChunk * group.val) := by
        rcases hShapeQ with ⟨k, hk, _, hl⟩ | ⟨k, hk⟩
        · obtain rfl := Wg0.Site.exchStore.inj (hk.symm.trans hqs)
          exact hl
        · rw [hqs] at hk
          cases hk
      obtain ⟨hgid, hgrp⟩ := exchange_overlap hpre hWarp hInvQ.warpLt
        hLocU hqLoc hSizeU hasize hc hac
      change s = w at hgid
      subst s
      subst uGroup
      obtain ⟨wb, _, tagw, _, dw, _, _, _, hwb, _, hsw, _, hdws, hWB, _⟩ :=
        Wg0PeerSources.actual_partner_pair_before_read hpre hX hs hrGet hd hsite hCut hLen hPrior
      let p : Fin 2 := ⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩
      have heq : warpOf L w % 2 = warpOf L g % 2 :=
        (actual_pair_bar (p := p) hpre hX hs hwb).2.1
      rw [← heq] at hwb
      have hwOrd := Wg0PeerTrace.pairOrdinal hpre hX (hs w hwlt).machine hwb hsw hdws
      have huOrd : ((X.tr w).take t).countP (Execution.isBarId (10 + warpOf L w % 2)) =
          d.block := by
        change count9 X w t = _ at hCountU
        omega
      have hlt := before_named hsGet rfl hwb (huOrd.trans (hWB.symm.trans hwOrd.symm))
      obtain ⟨role, hFollow⟩ := FollowedPrefix.state_at hsw hlt.le
      obtain ⟨_, u, hu, _, huShape⟩ :=
        Wg0PeerWrites.ordinary_at_followed (i := (w, t)) hpre hX hs hFollow hsWrite hc
          hsh hlow hhigh
      obtain ⟨hus, huBlock⟩ : u.site = .exchStore group ∧ u.block = d.block := by
        rcases huShape with ⟨k, hk, hsz, hl⟩ | ⟨k, hk⟩
        · obtain ⟨_, rfl⟩ := exchange_overlap hpre hWarp hInvQ.warpLt
            hl hqLoc hsz hasize hc hac
          have hCount := Wg0BarrierCount.peerCount hpre hX (hs w hslt).machine hsGet hu (.inr hk)
          change count9 X w t = _ at hCount
          exact ⟨hk, by omega⟩
        · have hCount := Wg0BarrierCount.probabilityCount hpre hX (hs w hslt).machine hsGet hu hk
          change count9 X w t = _ at hCount
          omega
      have hqOrd := Wg0PeerTrace.exchangeOrdinal hpre hX (hs w hwlt).machine hwGet hq hqs
      have hlt' := before_named hwGet rfl hwb
        (hqOrd.trans (hblock.trans (hWB.symm.trans hwOrd.symm)))
      have hU := exchange_to_pair hpre hX (hs w hwlt).machine hsGet hu hus hwb hsw hdws
        (huBlock.trans hWB.symm) hlt
      have hQ := exchange_to_pair hpre hX (hs w hwlt).machine hwGet hq hqs hwb hsw hdws
        (hblock.trans hWB.symm) hlt'
      have hti : t = j := by omega
      subst t
      exact .inl rfl
    · change count9 X s t = _ at hm
      omega
  · exact .inr (.inr (hLater hAfter))

/-- The actual loaded bytes are the appropriate eight-byte slice of the matching peer store. -/
theorem actual_readback_bytes {g i cut : Nat} {d : D} {group : Fin 8} {ac : Acc}
    {values : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hr : X.Reads (g, i) ac values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ (j : Nat) (q : D) (fp : Acc),
      Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧
      X.Writes (w, j) fp (exchangeValue q group.val).toBytes ∧
      exchangeReady q = true ∧ d.sub < 2 ∧
      values = (((exchangeValue q group.val).toBytes.drop (8 * d.sub)).take 8).map some := by
  dsimp only
  let w := Wg0PeerSources.partner L g
  obtain ⟨j, q, fp, bytes, hq, hqs, hblock, hw, rfl, hloc, hfp, hsize, hsub, horder⟩ :=
    Wg0PeerSources.actual_source_of_read hpre hX hs hr hd hsite hCut hLen hPrior
  let raw := (exchangeValue q group.val).toBytes
  obtain ⟨_, _, _, _, hIn, _, _⟩ := Frame.fired_site hs hX hw.choose_spec hq
  have hInv : Wg0.Inv P L w q := hIn
  have hready := hInv.exchangeWords (by rw [hqs]; rfl)
  have hlen : raw.length = 16 := by
    simp only [raw, Value.toBytes, List.length_map, List.length_range,
      Wg0.exchangeValue_bytes hready]
  refine ⟨j, q, fp, hq, hqs, hblock, hw, hready, hsub, ?_⟩
  have hmem : X.MemReads (.thread (g, i)) ac values := .inl hr
  have hrf := hX.rf (.thread (g, i)) ac values hmem
  have hvlen := hrf.1.trans hsize
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 8
  · have hka : k < ac.size := hsize ▸ hk
    have hcov : fp.Covers (ac.loc.at k) := by
      simp only [hloc, Loc.at, Acc.Covers, Loc.InRange, hfp, true_and]
      omega
    have hVisible : ByteCausality L X (ac.loc.at k) (.thread (w, j)) (.thread (g, i)) :=
      .direct (.inl horder)
    have hHidden := hX.hidden (.thread (g, i)) ac values k (.thread (w, j)) fp raw
      hmem hka (.inl hw) hcov hVisible
    have hRF := hrf.2 k hka
    cases hsrc : X.rf (.thread (g, i)) k with
    | none => rw [hsrc] at hHidden; exact hHidden.elim
    | some other =>
      rw [hsrc] at hRF hHidden
      obtain ⟨a, bs, hWriter, hCover, hValue⟩ := hRF
      rcases competing_write_order hpre hX hs hr hd hsite hCut hLen hPrior hw hq hqs hblock
          hloc hfp hka hWriter hCover with heq | earlier | later
      · subst other
        rcases hWriter with hWriter | ⟨old, tag, hRmw⟩
        · have hSame := Kind.wr.inj
            (congrArg Event.kind (Option.some.inj (hWriter.choose_spec.symm.trans hw.choose_spec)))
          rw [hSame.1, hSame.2] at hValue
          have hidx : (ac.loc.at k).addr - fp.loc.addr = 8 * d.sub + k := by
            simp only [hloc, Loc.at]
            omega
          have hPackedIdx : 8 * d.sub + k < raw.length := by omega
          have hRaw : (exchangeValue q group.val).toBytes[8 * d.sub + k]? =
              some (raw[8 * d.sub + k]) := List.getElem?_eq_getElem hPackedIdx
          simpa only [wbyte, hidx, List.getElem?_map, List.getElem?_take, List.getElem?_drop,
            ite_eq_left hk, Nat.add_comm k, hRaw, Option.map_some] using hValue
        · exact (GlobalWrites.no_rmw hX ⟨tag, hRmw⟩).elim
      · exact (hHidden earlier).elim
      · exact (hX.noFuture (.thread (g, i)) ac values k other hmem hka hsrc later).elim
  · rw [List.getElem?_eq_none (by omega : values.length ≤ k)]
    apply (List.getElem?_eq_none ?_).symm
    simp only [List.length_map, List.length_take, List.length_drop]
    omega

/-- Each executed peer load rebuilds to the two scores stored by the matching exchange lane. -/
theorem actual_readback_value {g i cut : Nat} {d : D} {group : Fin 8} {ac : Acc}
    {values : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (hr : X.Reads (g, i) ac values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    let w := Wg0PeerSources.partner L g
    ∃ (j : Nat) (q : D) (fp : Acc),
      Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧
      X.Writes (w, j) fp (exchangeValue q group.val).toBytes ∧
      rebuild 3 values = .ok (peerReadValue q group.val d.sub) ∧
      splitValue 64 (peerReadValue q group.val d.sub) =
        (q.peerScores.getD (4 * group.val + 2 * d.sub) (b32 0),
          q.peerScores.getD (4 * group.val + 2 * d.sub + 1) (b32 0)) := by
  obtain ⟨j, q, fp, hq, hqs, hblock, hw, hready, hsub, hbytes⟩ :=
    actual_readback_bytes hpre hX hs hr hd hsite hCut hLen hPrior
  refine ⟨j, q, fp, hq, hqs, hblock, hw, ?_, split_peerReadValue hready _ _⟩
  rw [hbytes]
  exact rebuild_exchange_slice hready _ _ hsub

/-- Readback in a globally tracked execution. -/
theorem readback_value {g i : Nat} {d : D} {group : Fin 8} {ac : Acc} {values : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) ac values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) :
    let w := Wg0PeerSources.partner L g
    ∃ (j : Nat) (q : D) (fp : Acc),
      Frame.stateAt (Machine.code P L) X w j = some (some (.wg0 q)) ∧
      q.site = .exchStore group ∧ q.block = d.block ∧
      X.Writes (w, j) fp (exchangeValue q group.val).toBytes ∧
      rebuild 3 values = .ok (peerReadValue q group.val d.sub) ∧
      splitValue 64 (peerReadValue q group.val d.sub) =
        (q.peerScores.getD (4 * group.val + 2 * d.sub) (b32 0),
          q.peerScores.getD (4 * group.val + 2 * d.sub + 1) (b32 0)) :=
  actual_readback_value hpre hX hs hr hd hsite le_rfl (PTX.len_of_get hr.choose_spec)
    (fun t _ => tracked_not_dismisses hX ht t)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
