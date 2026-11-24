-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0MaxReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RoleSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Lemmas.Order.Order

@[expose] public section

/-! # Ordering the ordinary accesses to the reused softmax shared bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedSoftmaxConflicts

open PTX PTX.Flow PTX.Proof Protocol Wg0 AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Ordinary exchange, probability, row maximum and half-sum storage. -/
def Window (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 204800 ≤ l.addr ∧ l.addr < L.sharedBase + 221696

private def count (X : Execution) (i : EvId) : Nat :=
  ((X.tr i.1).take i.2).countP (Execution.isBarId 9)

private theorem write_access {i : EvId} {a : Acc} {bs : List Byte} (h : X.Writes i a bs) :
    X.Access i a true := .inr (.inl ⟨bs, h, rfl⟩)

private theorem access_nonbar {i : EvId} {a : Acc} {e : Event} {w : Bool}
    (he : X.get i = some e) (ha : X.Access i a w) : Execution.isBarId 9 e = false := by
  rcases ha with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩ <;>
    obtain ⟨_, h⟩ := h
  all_goals simp only [Option.some.inj (he.symm.trans h), Execution.isBarId]

private theorem blocks_eq {g w : Nat} (hc : ctaOf L g = ctaOf L w) :
    blocksOf P L g = blocksOf P L w := by
  simp only [blocksOf, eOf, ctaidY, hc]

private theorem order_of_counts {g i w j : Nat} {d q : D} {a b : Acc} {u v : Bool}
    {e f : Event} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (_ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (w, j) = some f)
    (ha : X.Access (g, i) a u) (hb : X.Access (w, j) b v)
    (hd : Inv P L g d) (hq : Inv P L w q) (hc : ctaOf L g = ctaOf L w)
    (hn : count X (g, i) ≠ count X (w, j))
    (hg : count X (g, i) ≤ 2 * blocksOf P L g + 2)
    (hw : count X (w, j) ≤ 2 * blocksOf P L w + 2) :
    ByteCausality L X l (.thread (g, i)) (.thread (w, j)) ∨
      ByteCausality L X l (.thread (w, j)) (.thread (g, i)) := by
  have hCta : SameCta L g w := ⟨Frame.lt_of_get hX he, Frame.lt_of_get hX hf, hc⟩
  have hBlocks := blocks_eq (P := P) hc
  rcases Nat.lt_or_gt_of_ne hn with hlt | hlt
  · exact .inl (.direct (.inl (Wg0PeerReadback.order_of_bar9_counts hpre hX hs hCta
      hd.warpLt hd.wg he hf (access_nonbar he ha) hlt (by change count X (g, i) < _; omega))))
  · exact .inr (.direct (.inl (Wg0PeerReadback.order_of_bar9_counts hpre hX hs
      ⟨hCta.2.1, hCta.1, hCta.2.2.symm⟩ hq.warpLt hq.wg hf he
      (access_nonbar hf hb) hlt (by change count X (w, j) < _; omega))))

private theorem ordered_same_thread {i j : EvId} {a b : Acc} {l : Loc} {u v : Bool}
    (ha : X.Access i a u) (hb : X.Access j b v) (hc : i.1 = j.1)
    (hn : i ≠ j) (hca : a.Covers l) (hcb : b.Covers l) :
    ByteCausality L X l (.thread i) (.thread j) ∨
      ByteCausality L X l (.thread j) (.thread i) := by
  have hne : i.2 ≠ j.2 := fun h => hn (Prod.ext hc h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact .inl (.direct (.inl (.single (.inl (po_of_overlap ha hb hc hlt ⟨l, hca, hcb⟩)))))
  · exact .inr
      (.direct (.inl (.single (.inl (po_of_overlap hb ha hc.symm hlt ⟨l, hcb, hca⟩)))))

private theorem writer_cta {i : EvId} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hw : X.Writes i a bs) (hc : a.Covers l) (hsh : l.space = .shared) :
    l.cta = ctaOf L i.1 := hc.2.1.trans
      (RoleSharedWrites.shared_cta hpre hs hX ht hw (hc.1.symm.trans hsh))

private theorem probability_geometry {g i : Nat} {d : D} {k : Fin 4} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : X.Writes (g, i) a bs)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hk : d.site = .pStore k) :
    a.loc = shLoc L g (pTileBase + pChunkStride * k.val + 4096 * Wg0.half L g +
      512 * (warpOf L g % 2) + 16 * laneOf L g + 4 * d.sub) ∧ a.size = 4 ∧ d.sub < 4 := by
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX hw.choose_spec)).fired_at
    hw.choose_spec hd
  cases o with
  | none =>
    obtain ⟨_, _, hfire⟩ := hf
    rcases fires_none_ends hfire with ⟨_, h⟩ | h <;> cases h
  | some t =>
    have hf' : (Wg0.code P L g).toMachine.Fired (some d) _ (some t) := hf
    obtain ⟨_, hKind, hLoc, hSize, hSub⟩ := fired_pStore_event hpre hk hf'
    obtain rfl := (Kind.wr.inj hKind).1
    rw [hk] at hLoc
    exact ⟨(Option.some.inj hLoc).symm, hSize, hSub⟩

private theorem probability_same_lane {g w : Nat} {d q : D} {k j : Fin 4} {a b : Acc}
    {l : Loc} (hpre : Pre P L mem0) (hg : warpOf L g < 4) (hw : warpOf L w < 4)
    (ha : a.loc = shLoc L g (pTileBase + pChunkStride * k.val + 4096 * Wg0.half L g +
      512 * (warpOf L g % 2) + 16 * laneOf L g + 4 * d.sub))
    (hb : b.loc = shLoc L w (pTileBase + pChunkStride * j.val + 4096 * Wg0.half L w +
      512 * (warpOf L w % 2) + 16 * laneOf L w + 4 * q.sub))
    (haSize : a.size = 4) (hbSize : b.size = 4) (hd : d.sub < 4) (hq : q.sub < 4)
    (hca : a.Covers l) (hcb : b.Covers l) : g = w := by
  obtain ⟨_, hCtaA, hloA, hhiA⟩ := hca
  obtain ⟨_, hCtaB, hloB, hhiB⟩ := hcb
  simp only [ha, hb, haSize, hbSize, shLoc, pTileBase, pChunkStride, Wg0.half, warpOf,
    laneOf] at hCtaA hCtaB hloA hhiA hloB hhiB hg hw
  have hTid : tidOf L g = tidOf L w := by
    have hSite := k.isLt
    have hOther := j.isLt
    omega
  have hCta := hCtaA.symm.trans hCtaB
  rw [tidOf_eq hpre, tidOf_eq hpre] at hTid
  unfold ctaOf at hCta
  rw [hpre.block] at hCta
  omega

private theorem exchange_classes {g i : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : (∃ j : Fin 8, d.site = .exchStore j) ∨ ∃ j : Fin 4, d.site = .pStore j) :
    (∃ j : Fin 8, d.site = .exchStore j ∧ count X (g, i) = 2 * d.block + 1) ∨
      ∃ j : Fin 4, d.site = .pStore j ∧ count X (g, i) = 2 * d.block + 2 := by
  have h := (hs g (Frame.lt_of_get hX he)).machine
  rcases hsite with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact .inl ⟨j, hj, Wg0BarrierCount.peerCount hpre hX h he hd (.inr hj)⟩
  · exact .inr ⟨j, hj, Wg0BarrierCount.probabilityCount hpre hX h he hd hj⟩

private theorem row_classes {g i : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hInv : Inv P L g d) (hsite : d.site = .rowMax ∨ d.site = .lseStore0) :
    (count X (g, i) = 2 * d.block + 1 ∨ count X (g, i) = 2 * blocksOf P L g + 1) ∧
      count X (g, i) ≤ 2 * blocksOf P L g + 2 := by
  have h := (hs g (Frame.lt_of_get hX he)).machine
  have hLt := hInv.blockLt
  rcases hsite with hMax | hLse
  · have hc : count X (g, i) = 2 * d.block + 1 :=
      Wg0BarrierCount.rowMaxCount hpre hX h he hd (.inl hMax)
    exact ⟨.inl hc, by omega⟩
  · have hc := Wg0BarrierCount.maxReadCount hpre hX h he hd (.inr hLse)
    change count X (g, i) = _ at hc
    rw [ite_eq_left hLse] at hc
    have hLast := hInv.epilogueLast (show d.site.inEpilogue = true by rw [hLse]; rfl)
    exact ⟨.inr (by omega), by omega⟩

private theorem exchange_write_write {r s : Ref} {a b : Acc} {raw bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (ha : X.MemWrites r a raw) (hb : X.MemWrites s b bytes) (hne : r ≠ s)
    (hca : a.Covers l) (hcb : b.Covers l) (hsh : l.space = .shared)
    (hl : L.sharedBase + 204800 ≤ l.addr) (hu : l.addr < L.sharedBase + 221184) :
    ByteCausality L X l r s ∨ ByteCausality L X l s r := by
  obtain ⟨⟨g, i⟩, d, rfl, ha, hd, hInv, hSite⟩ :=
    Wg0PeerWrites.covered_write hpre hX hs ht ha hca hsh hl hu
  obtain ⟨⟨w, j⟩, q, rfl, hb, hq, hInv', hSite'⟩ :=
    Wg0PeerWrites.covered_write hpre hX hs ht hb hcb hsh hl hu
  have hCta := (writer_cta hpre hX hs ht ha hca hsh).symm.trans
    (writer_cta hpre hX hs ht hb hcb hsh)
  have hSame (h : g = w) := ordered_same_thread (L := L) (write_access ha) (write_access hb)
    h (fun hp => hne (congrArg Ref.thread hp)) hca hcb
  have hCountA := exchange_classes hpre hX hs ha.choose_spec hd
    (hSite.imp (fun ⟨k, hk, _, _⟩ => ⟨k, hk⟩) id)
  have hCountB := exchange_classes hpre hX hs hb.choose_spec hq
    (hSite'.imp (fun ⟨k, hk, _, _⟩ => ⟨k, hk⟩) id)
  have hBoundA : count X (g, i) ≤ 2 * blocksOf P L g + 2 := by
    have h : d.block < blocksOf P L g := hInv.blockLt
    rcases hCountA with ⟨_, _, hCount⟩ | ⟨_, _, hCount⟩ <;> rw [hCount] <;> omega
  have hBoundB : count X (w, j) ≤ 2 * blocksOf P L w + 2 := by
    have h : q.block < blocksOf P L w := hInv'.blockLt
    rcases hCountB with ⟨_, _, hCount⟩ | ⟨_, _, hCount⟩ <;> rw [hCount] <;> omega
  have hMixed (h : count X (g, i) ≠ count X (w, j)) :=
    order_of_counts (l := l) hpre hX hs ht ha.choose_spec hb.choose_spec
      (write_access ha) (write_access hb) hInv hInv' hCta h hBoundA hBoundB
  rcases hSite with ⟨ka, hka, hza, hla⟩ | ⟨ka, hka⟩ <;>
    rcases hSite' with ⟨kb, hkb, hzb, hlb⟩ | ⟨kb, hkb⟩
  · exact hSame (Wg0PeerReadback.exchange_overlap hpre hInv.warpLt hInv'.warpLt
      hla hlb hza hzb hca hcb).1
  · have hA := Wg0BarrierCount.peerCount hpre hX
      (hs g (Frame.lt_of_get hX ha.choose_spec)).machine ha.choose_spec hd (.inr hka)
    have hB := Wg0BarrierCount.probabilityCount hpre hX
      (hs w (Frame.lt_of_get hX hb.choose_spec)).machine hb.choose_spec hq hkb
    exact hMixed (by intro heq; simp only [count] at heq; omega)
  · have hA := Wg0BarrierCount.probabilityCount hpre hX
      (hs g (Frame.lt_of_get hX ha.choose_spec)).machine ha.choose_spec hd hka
    have hB := Wg0BarrierCount.peerCount hpre hX
      (hs w (Frame.lt_of_get hX hb.choose_spec)).machine hb.choose_spec hq (.inr hkb)
    exact hMixed (by intro heq; simp only [count] at heq; omega)
  · obtain ⟨hla, hza, hsa⟩ := probability_geometry hpre hX hs ha hd hka
    obtain ⟨hlb, hzb, hsb⟩ := probability_geometry hpre hX hs hb hq hkb
    exact hSame (probability_same_lane hpre hInv.warpLt hInv'.warpLt hla hlb hza hzb
      hsa hsb hca hcb)

/-- Any two distinct performed writes covering a reused softmax byte have byte causality. -/
theorem writes_ordered {r s : Ref} {a b : Acc} {raw bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (ha : X.MemWrites r a raw) (hb : X.MemWrites s b bytes) (hne : r ≠ s)
    (hca : a.Covers l) (hcb : b.Covers l) (hWin : Window L l) :
    ByteCausality L X l r s ∨ ByteCausality L X l s r := by
  obtain ⟨hSh, hLo, hHi⟩ := hWin
  by_cases hEx : l.addr < L.sharedBase + 221184
  · exact exchange_write_write hpre hX hs ht ha hb hne hca hcb hSh hLo hEx
  · obtain ⟨⟨g, i⟩, d, rfl, ha, _, hInv, _, hza, hla⟩ :=
      Wg0MaxWrites.covered_write hpre hX hs ht ha hca hSh (by omega) hHi
    obtain ⟨⟨w, j⟩, q, rfl, hb, _, hInv', _, hzb, hlb⟩ :=
      Wg0MaxWrites.covered_write hpre hX hs ht hb hcb hSh (by omega) hHi
    have hLane :=
      Wg0MaxReadback.word_overlap hpre hInv.warpLt hInv'.wg hla hlb hza hzb hca hcb
    exact ordered_same_thread (write_access ha) (write_access hb) hLane
      (fun h => hne (congrArg Ref.thread h)) hca hcb


private theorem read_access {i : EvId} {a : Acc} {bs : List (Option Byte)}
    (h : X.Reads i a bs) : X.Access i a false := .inl ⟨bs, h, rfl⟩

private theorem exchange_unique {g i j : Nat} {d q : D} {group : Fin 8} {a b : Acc}
    {bs raw : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (ha : X.Writes (g, i) a bs) (hb : X.Writes (g, j) b raw)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hD : d.site = .exchStore group) (hQ : q.site = .exchStore group)
    (hInv : Inv P L g d) (hInv' : Inv P L g q) (hBlock : d.block = q.block) :
    i = j := by
  have hSubD : d.sub = 0 := by
    have h := hInv.subLt
    rw [hD] at h
    change d.sub < 1 at h
    omega
  have hSubQ : q.sub = 0 := by
    have h := hInv'.subLt
    rw [hQ] at h
    change q.sub < 1 at h
    omega
  have hRank : Bound.rank P L g (.wg0 d) = Bound.rank P L g (.wg0 q) := by
    simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, hD, hQ, hBlock, hSubD, hSubQ]
  by_contra hn
  rcases Nat.lt_or_gt_of_ne hn with haLt | hbLt
  · have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX hs ht ha.choose_spec rfl
      (PTX.len_of_get hb.choose_spec).le hd hq haLt
    rw [hRank] at h
    exact (Nat.lt_irrefl _ h).elim
  · have h := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX hs ht hb.choose_spec rfl
      (PTX.len_of_get ha.choose_spec).le hq hd hbLt
    rw [hRank] at h
    exact (Nat.lt_irrefl _ h).elim

private theorem peer_read_write {g i : Nat} {d : D} {group : Fin 8} {r : Ref}
    {a b : Acc} {values : List (Option Byte)} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values) (hw : X.MemWrites r b bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSiteR : d.site = .peerRead group)
    (hca : a.Covers l) (hcb : b.Covers l) (hSh : l.space = .shared)
    (hLo : L.sharedBase + 204800 ≤ l.addr) (hHi : l.addr < L.sharedBase + 221184) :
    ByteCausality L X l (.thread (g, i)) r ∨ ByteCausality L X l r (.thread (g, i)) := by
  obtain ⟨⟨w, j⟩, q, rfl, hw, hq, hInvW, hSiteW⟩ :=
    Wg0PeerWrites.covered_write hpre hX hs ht hw hcb hSh hLo hHi
  obtain ⟨_, _, hInv, _⟩ := Wg0PeerWrites.read_geometry hpre hX hs hr hd hSiteR
  have hCta := (hca.2.1.trans (OrdinaryReadWindow.read_window hpre hX hs ht hr).2.1).symm.trans
    (writer_cta hpre hX hs ht hw hcb hSh)
  have hg := Frame.lt_of_get hX hr.choose_spec
  have hwr := Frame.lt_of_get hX hw.choose_spec
  have hR : count X (g, i) = 2 * d.block + 1 :=
    Wg0BarrierCount.peerCount hpre hX (hs g hg).machine hr.choose_spec hd (.inl hSiteR)
  have hRdLt : d.block < blocksOf P L g := hInv.blockLt
  have hWrLt : q.block < blocksOf P L w := hInvW.blockLt
  have hOrder (hNe : count X (g, i) ≠ count X (w, j))
      (hBound : count X (w, j) ≤ 2 * blocksOf P L w + 2) :=
    order_of_counts (l := l) hpre hX hs ht hr.choose_spec hw.choose_spec
      (read_access hr) (write_access hw) hInv hInvW hCta hNe (by rw [hR]; omega) hBound
  rcases hSiteW with ⟨grp, hSiteW, hSize, hLoc⟩ | ⟨k, hSiteW⟩
  · have hW : count X (w, j) = 2 * q.block + 1 :=
      Wg0BarrierCount.peerCount hpre hX (hs w hwr).machine hw.choose_spec hq (.inr hSiteW)
    by_cases hBlock : q.block = d.block
    · obtain ⟨z, own, fp, payload, hOwn, hOwnSite, hOwnBlock, hWrite, _, hReadLoc,
        hFpSize, hSizeR, hSub, hBefore⟩ := Wg0PeerSources.source_of_read hpre hX hs ht hr hd hSiteR
      have hSourceCover : fp.Covers l := by
        obtain ⟨hsp, hct, hlo, hhi⟩ := hca
        simp only [hReadLoc, Loc.at, hSizeR] at hsp hct hlo hhi
        exact ⟨hsp, hct, by omega, by rw [hFpSize]; omega⟩
      let mate := Wg0PeerSources.partner L g
      have hMem : X.MemWrites (.thread (mate, z)) fp payload := .inl hWrite
      obtain ⟨u, v, hRef, _, hv, hInvV, hTag⟩ :=
        Wg0PeerWrites.covered_write hpre hX hs ht hMem hSourceCover hSh hLo hHi
      obtain rfl := Ref.thread.inj hRef.symm
      change Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) z =
        some (some (.wg0 v)) at hv
      rw [hOwn] at hv
      obtain rfl := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hv))
      obtain ⟨group', hGroup', _, hOwnLoc⟩ : ∃ group' : Fin 8,
          own.site = .exchStore group' ∧ fp.size = 16 ∧
            fp.loc = shLoc L (Wg0PeerSources.partner L g)
              (exchangeBase + exchangeQuad * (warpOf L (Wg0PeerSources.partner L g) ^^^ 2) +
                16 * laneOf L (Wg0PeerSources.partner L g) + exchangeChunk * group'.val) := by
        rcases hTag with h | ⟨_, h⟩
        · exact h
        · rw [hOwnSite] at h
          cases h
      obtain rfl := Site.exchStore.inj (hGroup'.symm.trans hOwnSite)
      obtain ⟨hLane, rfl⟩ := Wg0PeerReadback.exchange_overlap hpre hInvW.warpLt hInvV.warpLt
        hLoc hOwnLoc hSize hFpSize hcb hSourceCover
      change w = mate at hLane
      subst w
      have hj := exchange_unique hpre hX (hs _ hwr).machine ht hw hWrite hq hOwn
        hSiteW hOwnSite hInvW hInvV (hBlock.trans hOwnBlock.symm)
      subst j
      exact .inr (.direct (.inl hBefore))
    · exact hOrder (by rw [hR, hW]; omega) (by rw [hW]; omega)
  · have hW : count X (w, j) = 2 * q.block + 2 :=
      Wg0BarrierCount.probabilityCount hpre hX (hs w hwr).machine hw.choose_spec hq hSiteW
    exact hOrder (by rw [hR, hW]; omega) (by rw [hW]; omega)

private theorem row_read_write {g i : Nat} {d : D} {r : Ref} {a b : Acc}
    {values : List (Option Byte)} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values) (hw : X.MemWrites r b bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSiteR : d.site = .maxRead ∨ d.site = .lseRead)
    (hca : a.Covers l) (hcb : b.Covers l) (hSh : l.space = .shared)
    (hLo : L.sharedBase + 221184 ≤ l.addr) (hHi : l.addr < L.sharedBase + 221696) :
    ByteCausality L X l (.thread (g, i)) r ∨ ByteCausality L X l r (.thread (g, i)) := by
  obtain ⟨⟨w, j⟩, q, rfl, hw, hq, hInvW, hSiteW, _, _⟩ :=
    Wg0MaxWrites.covered_write hpre hX hs ht hw hcb hSh hLo hHi
  obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.fired_site hs hX hr.choose_spec hd
  have hInv : Inv P L g d := hI
  have hCta := (hca.2.1.trans (OrdinaryReadWindow.read_window hpre hX hs ht hr).2.1).symm.trans
    (writer_cta hpre hX hs ht hw hcb hSh)
  have hg := Frame.lt_of_get hX hr.choose_spec
  have hCt := Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine hr.choose_spec hd
  change count X (g, i) = Wg0BarrierCount.ordinal d at hCt
  obtain ⟨hW, hBoundW⟩ := row_classes hpre hX hs hw.choose_spec hq hInvW hSiteW
  have hR : (count X (g, i) = 2 * d.block + 2 ∨ count X (g, i) = 2 * blocksOf P L g + 2) ∧
      count X (g, i) ≤ 2 * blocksOf P L g + 2 := by
    have hBlock := hInv.blockLt
    rcases hSiteR with hMax | hSum
    · simp only [Wg0BarrierCount.ordinal, hMax, Wg0BarrierCount.localOrdinal] at hCt
      exact ⟨.inl hCt, by omega⟩
    · have hLast := hInv.epilogueLast (show d.site.inEpilogue = true by rw [hSum]; rfl)
      simp only [Wg0BarrierCount.ordinal, hSum, Wg0BarrierCount.localOrdinal] at hCt
      exact ⟨.inr (by omega), by omega⟩
  have hNe : count X (g, i) ≠ count X (w, j) := by
    rcases hR.1 with hR | hR <;> rcases hW with hW | hW <;> rw [hR, hW] <;> omega
  exact order_of_counts hpre hX hs ht hr.choose_spec hw.choose_spec (read_access hr)
    (write_access hw) hInv hInvW hCta hNe hR.2 hBoundW

/-- An ordinary read and a performed write of the same reused softmax byte have byte causality. -/
theorem read_write_ordered {g i : Nat} {r : Ref} {a b : Acc}
    {values : List (Option Byte)} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values) (hw : X.MemWrites r b bytes)
    (hca : a.Covers l) (hcb : b.Covers l) (hWin : Window L l) :
    ByteCausality L X l (.thread (g, i)) r ∨ ByteCausality L X l r (.thread (g, i)) := by
  obtain ⟨hSh, hLo, hHi⟩ := hWin
  obtain ⟨d, hd, ⟨⟨_, hSite⟩, hEnd⟩ | ⟨hSite, hStart⟩⟩ :=
    OrdinaryReadWindow.softmax_read_of_cover hpre hX hs ht hr hca hLo hHi
  · exact peer_read_write hpre hX hs ht hr hw hd hSite hca hcb hSh hLo hEnd
  · exact row_read_write hpre hX hs ht hr hw hd hSite hca hcb hSh hStart hHi


/-- In every tracked prefix, a conflicting pair of ordinary accesses is ordered at each shared
softmax byte it covers. -/
theorem ordinary_conflict_ordered {e f : EvId} {a b : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hc : Conflict X (.thread e) (.thread f) a b)
    (ha : a.Covers l) (hb : b.Covers l) (hWin : Window L l) :
    ByteCausality L X l (.thread e) (.thread f) ∨
      ByteCausality L X l (.thread f) (.thread e) := by
  obtain ⟨hne, ea, fb, hA, hB, hWrite, _⟩ := hc
  have plain {i : EvId} {a : Acc} {w : Bool} (h : X.Access i a w) :
      (∃ bytes, X.Reads i a bytes ∧ w = false) ∨ ∃ bytes, X.Writes i a bytes ∧ w = true :=
    (Execution.access_iff_of_not_rmw (fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩)).mp h
  rcases plain hA with ⟨bytes, hRead, hEa⟩ | ⟨bytes, hWr, _⟩ <;>
    rcases plain hB with ⟨raw, hRead', hFb⟩ | ⟨raw, hWr', _⟩
  · rw [hEa, hFb] at hWrite
    simp at hWrite
  · exact read_write_ordered (r := .thread f) hpre hX hs ht hRead (.inl hWr') ha hb hWin
  · exact (read_write_ordered (r := .thread e) hpre hX hs ht hRead' (.inl hWr) hb ha hWin).symm
  · exact writes_ordered (r := .thread e) (s := .thread f) hpre hX hs ht
      (.inl hWr) (.inl hWr') hne ha hb hWin

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedSoftmaxConflicts
