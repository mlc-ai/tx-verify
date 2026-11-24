-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWrites
import Lemmas.Flow.Final

@[expose] public section

/-! # Older writers of the shared probability tile -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource

open PTX PTX.Flow AsyncCopy MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The probability footprint lies inside the reused score-exchange window. -/
theorem probability_byte_bounds (L : Launch) (row : Fin 128) (slot : Fin 64) (b : Fin 2) :
    L.sharedBase + 204800 ≤ pLinearByte L (row.val % 64) slot.val b.val ∧
    pLinearByte L (row.val % 64) slot.val b.val < L.sharedBase + 221184 := by
  have hs := slot.isLt
  have hb := b.isLt
  simp only [pLinearByte]
  omega

/-- A probability store can cover this byte only at its unique lane, site and element. -/
theorem probability_store_coordinates {g cta j : Nat} {d : Wg0.D} {site : Fin 4}
    {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hw : X.Writes (g, j) a bs)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .pStore site) (row : Fin 128) (slot : Fin 64) (b : Fin 2)
    (hc : a.Covers ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩) :
    g = Result.probabilityLane L cta row slot ∧ site.val = slot.val % 32 / 8 ∧
      d.sub = slot.val / 2 % 4 := by
  obtain ⟨tag, he⟩ := hw
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX hs he hd
  cases o with
  | none =>
    obtain ⟨_, _, hF⟩ := hf
    have hends := fires_none_ends hF
    rcases hends with ⟨_, hn⟩ | hn <;> cases hn
  | some u =>
    have hF : (Wg0.code P L g).toMachine.Fired (some d) ⟨tag, .wr a bs⟩ (some u) := hf
    obtain ⟨access, hKind, hLoc, hSize, hsub⟩ := Wg0.fired_pStore_event hpre hsite hF
    obtain rfl := (Kind.wr.inj hKind).1
    rw [hsite] at hLoc
    obtain ⟨addr, hAddr, hA⟩ := Result.pStore_mmaByte (block := d.block)
      (Wg0.head_eq L g) site ⟨d.sub, hsub⟩ 0 0
    have hLocEq : addr = a.loc := Option.some.inj (hAddr.symm.trans hLoc)
    rw [hLocEq] at hA
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero,
      Loc.at, pLinearByte] at hA
    have hCTA : ctaOf L g = cta := (congrArg Loc.cta hA).symm.trans hc.2.1.symm
    have hhead := Wg0.head_lt L g
    have hhalf := Wg0.halfLt ((Exists.choose_spec hF).1.2.warpLt)
    have hsiteLt := site.isLt
    have hslot := slot.isLt
    have hb := b.isLt
    have htid : tidOf L g = 64 * Wg0.half L g + Wg0.head L g := by
      change tidOf L g = 64 * (tidOf L g / 32 / 2) + tidOf L g % 64
      omega
    have hAddr' : a.loc.addr = L.sharedBase + 204800 +
        (16 * Wg0.head L g + 1024 * (4 * Wg0.half L g + site.val) + 4 * d.sub) := by
      have hA' := congrArg Loc.addr hA
      let first := 32 * Wg0.half L g + 2 * (4 * site.val + d.sub)
      change a.loc.addr = L.sharedBase + 204800 + 16 * Wg0.head L g +
        1024 * (first / 8) + 2 * (first % 8) at hA'
      dsimp [first] at hA'
      omega
    have hlow := hc.2.2.1
    have hhigh := hc.2.2.2
    change a.loc.addr ≤ pLinearByte L (row.val % 64) slot.val b.val at hlow
    change pLinearByte L (row.val % 64) slot.val b.val < a.loc.addr + a.size at hhigh
    rw [hAddr'] at hlow hhigh
    rw [hSize] at hhigh
    simp only [pLinearByte] at hlow hhigh
    have hHead : Wg0.head L g = row.val % 64 := by omega
    have hHalf : Wg0.half L g = slot.val / 32 := by omega
    have hLane : g = Result.probabilityLane L cta row slot := by
      have hgc : L.block * ctaOf L g + g % L.block = g := Nat.div_add_mod g L.block
      rw [hCTA] at hgc
      rw [tidOf_eq hpre] at htid
      rw [hpre.block] at hgc
      simp only [Result.probabilityLane, hpre.block, hHead, hHalf] at htid ⊢
      omega
    exact ⟨hLane, by omega, by omega⟩

/-- An actual followed competing write is older or belongs to the same or a later block. -/
theorem competing_followed_base_or_later {cta g j : Nat} {d : Wg0.D} {site : Fin 4} {e : Event}
    {s t : Nat} {q : Machine.ThreadD} {a : Acc} {bytes : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (he : X.get (g, j) = some e) (hCta : ctaOf L g = cta)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .pStore site) (row : Fin 128) (slot : Fin 64) (b : Fin 2)
    (hFollowed : Frame.stateAt (Machine.code P L) X s t = some (some q))
    (hwr : X.Writes (s, t) a bytes)
    (hcover : a.Covers ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩) :
    baseCausality L X (s, t) (g, j) ∨
      ∃ q : Wg0.D, Frame.stateAt (Machine.code P L) X s t = some (some (.wg0 q)) ∧
        ((∃ k : Fin 8, q.site = .exchStore k ∧ d.block < q.block) ∨
         (∃ k : Fin 4, q.site = .pStore k ∧ d.block ≤ q.block)) := by
  obtain ⟨hlo, hhi⟩ := probability_byte_bounds L row slot b
  obtain ⟨hc, q, hq, hInv, hqsite⟩ := Wg0PeerWrites.ordinary_at_followed (i := (s, t)) hpre hX hs
    hFollowed hwr hcover rfl hlo hhi
  have hsCta : ctaOf L s = cta := hc.symm.trans hcover.2.1.symm
  have hS := Frame.lt_of_get hX hwr.choose_spec
  have hG := Frame.lt_of_get hX he
  have hcount := Wg0BarrierCount.probabilityCount hpre hX (hs g hG).machine he hd hsite
  have earlier (hLt : ((X.tr s).take t).countP (Execution.isBarId 9) < 2 * d.block + 2)
      (hBound : ((X.tr s).take t).countP (Execution.isBarId 9) < 2 * Wg0.blocksOf P L s + 2) :
      baseCausality L X (s, t) (g, j) :=
    Wg0PeerReadback.order_of_bar9_counts hpre hX hs
      ⟨hS, hG, hsCta.trans hCta.symm⟩ hInv.warpLt hInv.wg hwr.choose_spec he rfl
      (by rw [hcount]; exact hLt) hBound
  have hB : q.block < Wg0.blocksOf P L s := hInv.blockLt
  rcases hqsite with ⟨k, hk, _, _⟩ | ⟨k, hk⟩
  · by_cases hb : d.block < q.block
    · exact .inr ⟨q, hq, .inl ⟨k, hk, hb⟩⟩
    · have hqcount := Wg0BarrierCount.peerCount hpre hX (hs s hS).machine
        hwr.choose_spec hq (.inr hk)
      exact .inl (earlier (by rw [hqcount]; omega) (by rw [hqcount]; omega))
  · by_cases hb : d.block ≤ q.block
    · exact .inr ⟨q, hq, .inr ⟨k, hk, hb⟩⟩
    · have hqcount := Wg0BarrierCount.probabilityCount hpre hX
        (hs s hS).machine hwr.choose_spec hq hk
      exact .inl (earlier (by rw [hqcount]; omega) (by rw [hqcount]; omega))

variable {cta g j : Nat} {d : Wg0.D} {site : Fin 4} {e : Event} {other : Ref} {a : Acc}
    {bytes : List Byte} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, j) = some e) (hCta : ctaOf L g = cta)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .pStore site) (row : Fin 128)
include hpre hX hs ht he hCta hd hsite row

theorem competing_base_or_later (slot : Fin 64) (b : Fin 2) (hwrite : X.MemWrites other a bytes)
    (hcover : a.Covers ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩) :
    (∃ w : EvId, other = .thread w ∧ baseCausality L X w (g, j)) ∨
      ∃ (w : EvId) (q : Wg0.D), other = .thread w ∧ X.Writes w a bytes ∧
        Frame.stateAt (Machine.code P L) X w.1 w.2 = some (some (.wg0 q)) ∧
        Wg0.Inv P L w.1 q ∧ ctaOf L w.1 = cta ∧
        ((∃ k : Fin 8, q.site = .exchStore k ∧ d.block < q.block) ∨
         (∃ k : Fin 4, q.site = .pStore k ∧ d.block ≤ q.block)) := by
  let loc : Loc := ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩
  obtain ⟨hlo, hhi⟩ := probability_byte_bounds L row slot b
  obtain ⟨⟨s, t⟩, q, rfl, hwr, hq, hInv, hqsite⟩ :=
    Wg0PeerWrites.covered_write hpre hX hs ht hwrite hcover rfl hlo hhi
  have hsCta : ctaOf L s = cta :=
    (RoleSharedWrites.shared_cta hpre hs hX ht hwr hcover.1.symm).symm.trans hcover.2.1.symm
  have hS := Frame.lt_of_get hX hwr.choose_spec
  have hG := Frame.lt_of_get hX he
  have hcount := Wg0BarrierCount.probabilityCount hpre hX (hs g hG).machine he hd hsite
  have earlier (hLt : ((X.tr s).take t).countP (Execution.isBarId 9) < 2 * d.block + 2)
      (hBound : ((X.tr s).take t).countP (Execution.isBarId 9) < 2 * Wg0.blocksOf P L s + 2) :
      baseCausality L X (s, t) (g, j) :=
    Wg0PeerReadback.order_of_bar9_counts hpre hX hs
      ⟨hS, hG, hsCta.trans hCta.symm⟩ hInv.warpLt hInv.wg hwr.choose_spec he rfl
      (by rw [hcount]; exact hLt) hBound
  have hB : q.block < Wg0.blocksOf P L s := hInv.blockLt
  rcases hqsite with ⟨k, hk, _, _⟩ | ⟨k, hk⟩
  · by_cases hb : d.block < q.block
    · exact .inr ⟨(s, t), q, rfl, hwr, hq, hInv, hsCta, .inl ⟨k, hk, hb⟩⟩
    · have hqcount := Wg0BarrierCount.peerCount hpre hX (hs s hS).machine
        hwr.choose_spec hq (.inr hk)
      exact .inl ⟨(s, t), rfl, earlier (by rw [hqcount]; omega) (by rw [hqcount]; omega)⟩
  · by_cases hb : d.block ≤ q.block
    · exact .inr ⟨(s, t), q, rfl, hwr, hq, hInv, hsCta, .inr ⟨k, hk, hb⟩⟩
    · have hqcount := Wg0BarrierCount.probabilityCount hpre hX
        (hs s hS).machine hwr.choose_spec hq hk
      exact .inl ⟨(s, t), rfl, earlier (by rw [hqcount]; omega) (by rw [hqcount]; omega)⟩

/-- The older competing writes are ordered at the byte of the selected probability store. -/
theorem competing_older_or_later (slot : Fin 64) (b : Fin 2) (hwrite : X.MemWrites other a bytes)
    (hcover : a.Covers ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩) :
    let loc : Loc := ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩
    ByteCausality L X loc other (.thread (g, j)) ∨
      ∃ (w : EvId) (q : Wg0.D), other = .thread w ∧ X.Writes w a bytes ∧
        Frame.stateAt (Machine.code P L) X w.1 w.2 = some (some (.wg0 q)) ∧
        Wg0.Inv P L w.1 q ∧ ctaOf L w.1 = cta ∧
        ((∃ k : Fin 8, q.site = .exchStore k ∧ d.block < q.block) ∨
         (∃ k : Fin 4, q.site = .pStore k ∧ d.block ≤ q.block)) := by
  rcases competing_base_or_later hpre hX hs ht he hCta hd hsite row slot b hwrite hcover with
    ⟨w, rfl, hBefore⟩ | hLater
  · exact .inl (.direct (.inl hBefore))
  · exact .inr hLater

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
