-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Words
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # The index warp's `.nc` reads are allocated

The index warp's `.nc` reads are its two length loads (pcs 2360 and 2365: the row's words,
`Index.topk_read`, `Index.extra_read`) and its four pair loads (`index_mainPairAddr`,
`index_extraPairAddr`: words of the lane's index row), whose bytes `Pre` allocates
(`paramTopkLen`, `paramExtraTopkLen`, `idxInput`, `extraIdxInput`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A main index pair read covers allocated input bytes**: word `j` of its row. -/
private theorem main_read (hp : Pre P L m) {x y j : Nat} {a : Acc} (hx : x < P.s_q) (hy : y < P.b)
    (hlt : j < P.topk) (hsz : a.size = 4)
    (hloc : a.loc = ⟨.global, 0, P.indicesBase + 4 * ((y * P.s_q + x) * P.topk + j)⟩) {l : Loc}
    (hc : a.Covers l) : NcRead P m l := by
  obtain ⟨kk, hkk, rfl⟩ := word_cover hloc hsz hc
  have hr := row_lt hx hy hlt
  have e : 4 * P.b * P.s_q * P.topk = 4 * (P.b * P.s_q * P.topk) := by ring
  refine ⟨fun hn => ?_, rfl, ?_⟩
  · have := hp.idxInput y hy x hx j hlt kk hkk
    rw [hn] at this
    cases this
  · exact ncApart_of hp.idxApartO hp.idxApartLse (by omega) (by omega)

/-- **An extra index pair read covers allocated input bytes.** -/
private theorem extra_read (hp : Pre P L m) {x y j : Nat} {a : Acc} (hx : x < P.s_q)
    (hy : y < P.b) (hlt : j < P.extra_topk) (hsz : a.size = 4)
    (hloc : a.loc = ⟨.global, 0, P.extraIndicesBase +
      4 * ((y * P.s_q + x) * P.extra_topk + j)⟩) {l : Loc} (hc : a.Covers l) :
    NcRead P m l := by
  obtain ⟨kk, hkk, rfl⟩ := word_cover hloc hsz hc
  have hr := row_lt hx hy hlt
  have e : 4 * P.b * P.s_q * P.extra_topk = 4 * (P.b * P.s_q * P.extra_topk) := by ring
  have hpos : 0 < P.extra_topk := by omega
  refine ⟨fun hn => ?_, rfl, ?_⟩
  · rcases hp.extraIdxInput with h0 | ⟨-, h⟩
    · omega
    · have := h y hy x hx j hlt kk hkk
      rw [hn] at this
      cases this
  · exact ncApart_of (hp.extraIdxApartO hpos) (hp.extraIdxApartLse hpos) (by omega) (by omega)

/-- **The site of an index warp's `.nc` event**: the machine's state before it satisfies `ixLenOk`,
fires the event from a good concrete state, and is a length load or one of the four pair loads. -/
private theorem index_ncSite (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.IndexAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs) :
    ∃ d : Index.D, ixLenOk P L g d ∧ (∃ t ins o, (Index.code P L g).AtD d t ∧
      (Index.code P L g).inv d ∧ kernel.code[(Index.code P L g).pc d]? = some ins ∧
      Fires ((Index.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) ∧
      e.pc = d.site.pc ∧ (d.site = .lenA ∨ d.site = .lenB ∨ e.pc = 2403 ∨ e.pc = 2429 ∨
        e.pc = 2501 ∨ e.pc = 2517) := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, hE, -⟩ := index_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  have hok := (ix_ok hp hX hσ d n rfl).1
  obtain ⟨t, ins, o, hat', hinv, hc', hf⟩ := ix_fired hp hX he hub hσ
  obtain ⟨hpc1, hK⟩ := hE
  refine ⟨d, hok, ⟨t, ins, o, hat', hinv, hc', hf⟩, hpc1, ?_⟩
  unfold Index.EvK at hK
  rw [hpc1]
  revert hK
  generalize d.site = s
  intro hK
  cases s <;> simp [IxSite.pc, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
    Index.StoreEv, hk] at hK ⊢

/-- **The index warp's `.nc` events rebuild to 32-bit words**, the second length's word being
nonzero only for a positive `extra_topk`. -/
theorem index_ncWord (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.IndexAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs) :
    (∃ y, rebuild 3 bs = .ok (.bits 32 y)) ∧
      (e.pc = 2365 → ∀ y, rebuild 3 bs = .ok (.bits 32 y) → y.toNat % 2 ^ 32 ≠ 0 →
        0 < P.extra_topk) := by
  obtain ⟨d, hok, ⟨t, ins, o, hat', hinv, hc', hf⟩, hpc1, hs⟩ := index_ncSite hp hX hFw he hat hk
  rcases hs with hs | hs | hs | hs | hs | hs
  · simp only [ixLenOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Index.topk_read hp hx hs hat' hinv hc' hf
    obtain ⟨rfl, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    have hw := rebuild_topk hp hX (ctaid_lt hp g).2 hx he ⟨hk, hr.2⟩
    refine ⟨⟨_, hw⟩, fun h => ?_⟩
    have h2 : e.pc = 2360 := by rw [hpc1, hs]; rfl
    exact absurd h (by omega)
  · simp only [ixLenOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Index.extra_read hp hx hs hat' hinv hc' hf
    obtain ⟨rfl, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    have hw := rebuild_extra hp hX (ctaid_lt hp g).2 hx he ⟨hk, hr.2⟩
    refine ⟨⟨_, hw⟩, fun _ y hy hy0 => ?_⟩
    have hm := hp.paramExtraTopkLen
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    have hle := (hmem _ (ctaid_lt hp g).2 0 (by norm_num)).2 _ (ctaid_lt hp g).2
    rw [hw] at hy
    simp only [Except.ok.injEq] at hy
    by_contra h0
    have h1 : P.extraTopkLen (ctaidY L g) = 0 := by omega
    rw [h1] at hy
    obtain ⟨-, rfl⟩ := Value.bits.inj hy
    exact hy0 (by simp)
  all_goals obtain ⟨pc, kd⟩ := e
  all_goals have hk' : kd = .nc a bs := hk
  all_goals subst hk'
  · exact ⟨index_mainPairWord hp hX hFw he (by dsimp only at hs; omega),
      fun h => absurd h (by omega)⟩
  · exact ⟨index_mainPairWord hp hX hFw he (by dsimp only at hs; omega),
      fun h => absurd h (by omega)⟩
  · exact ⟨index_extraPairWord hp hX hFw he (by dsimp only at hs; omega),
      fun h => absurd h (by omega)⟩
  · exact ⟨index_extraPairWord hp hX hFw he (by dsimp only at hs; omega),
      fun h => absurd h (by omega)⟩

/-- **The index warp's `.nc` read covers allocated bytes only.** -/
theorem index_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : IndexAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  obtain ⟨d, hok, ⟨t, ins, o, hat', hinv, hc', hf⟩, hpc1, hs⟩ := index_ncSite hp hX hFw he hat hk
  obtain ⟨pc, kd⟩ := e
  rcases hs with hs | hs | hs | hs | hs | hs
  · simp only [ixLenOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Index.topk_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_topk hp (ctaid_lt hp g).2 hx hk hr l hc
  · simp only [ixLenOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Index.extra_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_extra hp (ctaid_lt hp g).2 hx hk hr l hc
  all_goals have hk' : kd = .nc a bs := hk
  all_goals subst hk'
  all_goals obtain ⟨hx, hy⟩ := ctaid_lt hp g
  all_goals simp only at hs
  · obtain ⟨b, el, -, -, -, hlt, hsz, hloc⟩ := index_mainPairAddr hp hX hFw he (by omega)
    exact main_read hp hx hy hlt hsz hloc hc
  · obtain ⟨b, el, -, -, -, hlt, hsz, hloc⟩ := index_mainPairAddr hp hX hFw he (by omega)
    exact main_read hp hx hy hlt hsz hloc hc
  all_goals obtain ⟨b, el, -, -, -, hlt, hsz, hloc⟩ := index_extraPairAddr hp hX hFw he (by omega)
  all_goals exact extra_read hp hx hy hlt hsz hloc hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
