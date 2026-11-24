-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MOrder
public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead

@[expose] public section

/-!
# The scratch words read as the numbers the warps stored (`ScratchIt`)

The load `ldL` of a default thread `g` in iteration `i` reads the word `r = tid % 4` of its CTA,
four bytes at `sharedBase + 212992 + 4 r`. The proof is the reads-from argument of
`read_byte_of_source`:

* the visible write is the `store10` of iteration `i` of the lane `32 r` of the CTA: that lane has
  its `bar23` of iteration `i` at the reader's count (`member23`), its store is the state before,
  and the barrier orders the store before the reader's load (`Bar.bar128Causal`);
* every other write of a byte of the word (`source_class`): a `store10` of the same iteration
  writes the same bytes (`StoreWord`); one of a later iteration is after the load (`later_after`),
  one of an earlier iteration is before the visible store (`earlier_before`), and the prologue's
  stores of `(num_pre, num_iters)` (words 0 and 1) are before it (`pro_before`); no other write
  reaches the scratch words.

`ldL_value`: the loaded word is the stored value `erealValue .f32 w`; `scratchIt_of`: `ScratchIt`
from `StoreWord` of iteration `i`, `B0At` of iteration `i` and `B0Pos` of the iterations up to `i`,
with `RoleReads` (the barrier-1 order of the prologue).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A list of four bytes with the bytes of a value of four bytes is the value's bytes. -/
theorem bytes4_eq {bs : List (Option Byte)} {V : Value} (hl : bs.length = 4) (hV : V.bytes = 4)
    (h : ∀ kk < 4, bs[kk]? = some (some (V.byteAt kk))) : bs = V.toBytes.map some := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < 4
  · rw [h n hn]
    simp [Value.toBytes, hV, hn]
  · rw [List.getElem?_eq_none (by omega)]
    simp [Value.toBytes, hV]
    omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The scratch load of iteration `i` reads the bytes of the word the warp `r` stored**: the
load event of the state `ldL`, whatever the machine does with them. -/
theorem ldL_bytes (hR : RoleReads L X) {c i : Nat} (hB : B0At Q L X c i)
    (hP : ∀ j ≤ i, B0Pos Q L X c j) {w : EReal} {r : Nat} (hr : r < 4)
    (hw : ∀ {t k : Nat} {d : Sm.D}, t < L.threads → t / L.block = c → t % L.block / 32 = r →
      St Q L X t k = some (some (.d (.sm d))) → d.site = .store10 → d.i = i →
      d.stg.cm4 = erealValue .f32 w)
    {g k1 : Nat} {d1 : Sm.D} {e1 : Event} (hg : g < L.threads) (hgc : g / L.block = c)
    (hgr : g % L.block % 4 = r) (hk : k1 ≤ (X.tr g).length) (hge1 : X.get (g, k1) = some e1)
    (hσ1 : St Q L X g k1 = some (some (.d (.sm d1)))) (hs1 : d1.site = .ldL) (hi1' : d1.i = i) :
    ∃ ac bs, e1 = ⟨evPc d1.site, .rd ac bs⟩ ∧ bs = (erealValue .f32 w).toBytes.map some := by
  have hb256 : L.block = 256 := hpre.block
  have hsh := hpre.sharedRange
  unfold sharedBytes at hsh
  have hthr : L.threads = L.grid * 256 := by unfold Launch.threads; rw [hb256]
  have hi1 : 1 ≤ i := by
    have := midOk_state k1 hk hσ1 (by rw [hs1]; trivial)
    omega
  have hgd := sm_default hk hσ1
  rcases Sv.pred_sm hk hσ1 with ⟨dt, rfl⟩ | ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
  · simp [SmEntry.d0] at hs1
  obtain ⟨hs2, hi2⟩ := prev_ldL hn2 hs1
  have hi2' : d2.i = i := by omega
  -- the load
  have he1 : (X.tr g)[k2 + 1]? = some e1 := hge1
  have hlen1 : k2 + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he1).1
  obtain ⟨u, hF⟩ := fired_cont hX hf hg hge1 hσ1 (by simp [ExitState])
  obtain ⟨ac, bs, hev1, hloc, hsz⟩ :=
    shape_ldL_foot (ProA.sharedOk_of_pre hpre) (fired_sm hF) hs1
  subst hev1
  have hrd : X.MemReads (.thread (g, k2 + 1)) ac bs := Or.inl ⟨_, hge1⟩
  have hbl : bs.length = 4 := by
    have := Consistent.read_length hX hrd
    omega
  have hnb : ∀ {pc : Nat} {cn : Option Nat} {m : BarMode},
      X.get (g, k2 + 1) ≠ some ⟨pc, .bar 0 cn m⟩ := by
    intro pc cn m h
    rw [hge1] at h
    simp at h
  -- the reader's `bar23`
  have hev2 := bar_event hpre hX hf hg he2 hσ2 (by rw [hs2]; trivial)
  rw [hs2] at hev2
  have hge2 : X.get (g, k2) = some ⟨Sm.Site.bar23.pc, .bar 0 (some 128) .sync⟩ := by
    rw [show X.get (g, k2) = some e2 from he2, hev2]
  -- the lane `32 r` of the CTA and its store of iteration `i`
  have hgcl : c < L.grid := by
    rw [← hgc, hb256]
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hL0 : c * L.block + 32 * r < L.threads := by rw [hthr, hb256]; nlinarith
  have hLc : (c * L.block + 32 * r) / L.block = c := by rw [hb256]; omega
  have hLm : (c * L.block + 32 * r) % L.block = 32 * r := by rw [hb256]; omega
  have hLd : (c * L.block + 32 * r) % L.block < 128 := by rw [hLm]; omega
  have hLr : (c * L.block + 32 * r) % L.block / 32 = r := by rw [hLm]; omega
  obtain ⟨a, dl, hσa, hsa, hia, hcnta, hgeta⟩ := member23 hpre hX hf (hP i le_rfl) hg hgc hσ2 hs2
    hi2' hlen1 hL0 hLc hLd
  have hale : a ≤ (X.tr (c * L.block + 32 * r)).length := event_le hgeta
  rcases Sv.pred_sm hale hσa with ⟨dt, hdt⟩ | ⟨a1, ds, es, rfl, hes, hσs, hns⟩
  · rw [hdt] at hsa
    simp [SmEntry.d0] at hsa
  obtain ⟨hss, hsi⟩ := prev_bar23 hns hsa
  have hsi' : ds.i = i := by omega
  have ha1 : a1 < (X.tr (c * L.block + 32 * r)).length := (List.getElem?_eq_some_iff.mp hes).1
  obtain ⟨u', hF'⟩ := fired_cont hX hf hL0 hes hσs (by simp [ExitState])
  obtain ⟨v, hsv, hesv⟩ := shape_store10_val (ProA.sharedOk_of_pre hpre) (fired_sm hF') hss
  rw [hw hL0 hLc hLr hσs hss hsi', (erealValue_store w).1] at hsv
  cases hsv
  rw [hLc, hLr, Nat.mod_eq_of_lt hr] at hesv
  have hwM : X.MemWrites (.thread (c * L.block + 32 * r, a1))
      (EvD.wordAcc ⟨.shared, c, L.sharedBase + 212992 + r * 4⟩ 0)
      (erealValue .f32 w).toBytes :=
    Or.inl ⟨_, by rw [show X.get (c * L.block + 32 * r, a1) = some es from hes, hesv]⟩
  have hvis : baseCausality L X (c * L.block + 32 * r, a1) (g, k2 + 1) :=
    Bar.bar128Causal hpre hX hf.sound hf.tracked hL0 hg (by rw [hLc, hgc]) hLd hgd hgeta hge2
      hcnta (by omega) (by omega) hlen1
  -- the bytes
  have hVb := erealValue_bytes w
  have hbytes : ∀ kk < 4, bs[kk]? = some (some ((erealValue .f32 w).byteAt kk)) := by
    intro kk hkk
    have hl : ac.loc.at kk = ⟨.shared, c, L.sharedBase + r * 4 + 212992 + kk⟩ := by
      rw [hloc]
      simp [Loc.at, hgc, hgr]
    have hcov : (EvD.wordAcc ⟨.shared, c, L.sharedBase + 212992 + r * 4⟩ 0).Covers
        (ac.loc.at kk) := by
      rw [hl]
      refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [EvD.wordAcc] <;> omega
    refine read_byte_of_source hX hrd (by omega) hwM hcov (.inl hvis) ?_
    intro w' dst' bytes' hrf hw' hcov'
    obtain ⟨ev', hev'⟩ := write_present hX hw'
    have hlt' := Frame.lt_of_get hX hev'
    have hTT : TT Q L X (refEvent w') := hf.tracked _ _ hlt'
    rw [hl] at hcov'
    obtain ⟨hs1', hc1', hlo, hhi⟩ := hcov'
    rcases source_class hpre hX hf.sound hw' hs1'.symm hTT with
      ⟨t, kt, s, rfl, htl, hσt, hTW⟩ | ⟨i', -, hc2, h12⟩
    · obtain ⟨pct, hgt⟩ : ∃ pc, X.get (t, kt) = some ⟨pc, .wr dst' bytes'⟩ := by
        rcases hw' with ⟨pc, h⟩ | ⟨old, pc, h⟩
        · exact ⟨pc, h⟩
        · exact absurd h (no_rmw hX)
      have hkt : kt < (X.tr t).length := (List.getElem?_eq_some_iff.mp hgt).1
      cases hTW with
      | stq hi' hs' hl' hz h1 h2 =>
        rw [hl'] at hlo hhi
        simp only [hz] at hhi
        simp only at hlo hhi
        omega
      | st8 hs' ha hb =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
      | st9_0 hs' ha hb =>
        right; left
        have htc : t / L.block = c := by
          rw [ha] at hc1'
          simp [EvD.wordAcc] at hc1'
          exact hc1'.symm
        exact .inl <| pro_before hpre hX hf hR htl hσt hgt hL0 hσs ha1 (by rw [htc, hLc])
      | st9_1 hs' ha hb =>
        right; left
        have htc : t / L.block = c := by
          rw [ha] at hc1'
          simp [EvD.wordAcc] at hc1'
          exact hc1'.symm
        exact .inl <| pro_before hpre hX hf hR htl hσt hgt hL0 hσs ha1 (by rw [htc, hLc])
      | @store10 dt _ _ hs' ha =>
        have htc : t / L.block = c := by
          rw [ha] at hc1'
          simp [EvD.wordAcc] at hc1'
          exact hc1'.symm
        have htd := sm_default hkt.le hσt
        have htr : t % L.block / 32 = r := by
          rw [ha] at hlo hhi
          simp only [EvD.wordAcc] at hlo hhi
          omega
        rcases lt_trichotomy dt.i i with hlt | heq | hgt'
        · right; left
          exact .inl <| earlier_before hpre hX hf (hP dt.i hlt.le) hL0 hLc hσs ha1 hss hsi' htl htc
            hσt hkt hs' rfl hlt
        · right; right
          obtain ⟨u2, hF2⟩ := fired_cont hX hf htl hgt hσt (by simp [ExitState])
          obtain ⟨v2, hsv2, hesv2⟩ :=
            shape_store10_val (ProA.sharedOk_of_pre hpre) (fired_sm hF2) hs'
          rw [hw htl htc htr hσt hs' heq, (erealValue_store w).1] at hsv2
          cases hsv2
          simp only [Event.mk.injEq, Kind.wr.injEq] at hesv2
          obtain ⟨-, rfl, rfl⟩ := hesv2
          rw [hl]
          simp only [wbyte, EvD.wordAcc, htc, htr, Nat.mod_eq_of_lt hr]
          rw [show L.sharedBase + r * 4 + 212992 + kk - (L.sharedBase + 212992 + r * 4) = kk
            by omega]
          simp [Value.toBytes, hVb, hkk]
        · left
          exact .inl <| later_after hpre hX hf hB (hP i le_rfl) hi1 hg hgc hσ2 hs2 hi2' hlen1 hnb
            htl htc hσt hkt hs' hgt'
      | allocWr hs' ha hb =>
        rw [ha] at hlo hhi
        simp only at hlo hhi
        omega
      | stTab hs' ha hb =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
    · simp only at hlo hhi
      have hsr0 := hpre.sharedRange
      unfold sharedBytes at hsr0
      rcases h12 with h12 | h12 <;> omega
  exact ⟨ac, bs, rfl, bytes4_eq hbl hVb hbytes⟩

/-- **The scratch load of iteration `i` returns the word the warp `r` stored.** -/
theorem ldL_value (hR : RoleReads L X) {c i : Nat} (hB : B0At Q L X c i)
    (hP : ∀ j ≤ i, B0Pos Q L X c j) {w : EReal} {r : Nat} (hr : r < 4)
    (hw : ∀ {t k : Nat} {d : Sm.D}, t < L.threads → t / L.block = c → t % L.block / 32 = r →
      St Q L X t k = some (some (.d (.sm d))) → d.site = .store10 → d.i = i →
      d.stg.cm4 = erealValue .f32 w)
    {g k : Nat} {d : Sm.D} (hg : g < L.threads) (hgc : g / L.block = c)
    (hgr : g % L.block % 4 = r) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .shfl11) (hi : d.i = i) :
    d.stg.ld = erealValue .f32 w := by
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs1, hi1'⟩ := prev_shfl11 hn1 hs
  have hge1 : X.get (g, k1) = some e1 := he1
  obtain ⟨ac, bs, hev, hbs⟩ := ldL_bytes hpre hX hf hR hB hP hr hw hg hgc hgr (by omega) hge1
    hσ1 hs1 (by omega)
  subst hev
  obtain ⟨x, hx, hld⟩ := ldL_next hs1 hn1
  rw [hld]
  rw [hbs, (erealValue_store w).2] at hx
  exact (Except.ok.inj hx).symm

/-- **`ScratchIt` of iteration `i`** from the stores of iteration `i` (`StoreWord`), the barrier-0
count of `bar23` of iteration `i` (`B0At`) and the positions of the counts up to `i` (`B0Pos`). -/
theorem scratchIt_of (hR : RoleReads L X) {i : Nat} (hU : ∀ c, StoreWord Q L X c i)
    (hB : ∀ c, B0At Q L X c i) (hP : ∀ c, ∀ j ≤ i, B0Pos Q L X c j) : ScratchIt Q L X i := by
  intro c
  classical
  let W : Nat → EReal := fun r => if h : r < 4 then Classical.choose (hU c r h) else 0
  refine ⟨W, ?_, ?_⟩
  · intro r
    by_cases h : r < 4
    · simp only [W, h, ↓reduceDIte]
      exact (Classical.choose_spec (hU c r h)).1
    · simp only [W, h, ↓reduceDIte]
      exact EReal.zero_ne_top
  · intro g k d hg hgc hσ hs hi
    have hr : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
    have hW : W (g % L.block % 4) = Classical.choose (hU c _ hr) := by simp only [W, hr]; rfl
    rw [hW]
    have hspec := Classical.choose_spec (hU c _ hr)
    have hval : ∀ {k : Nat}, k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.sm d))) →
        d.stg.ld = erealValue .f32 (Classical.choose (hU c _ hr)) := fun hk hσ' =>
      ldL_value hpre hX hf hR (hB c) (hP c) hr hspec.2 hg hgc rfl hk hσ' hs hi
    rw [show d.stg.ld = _ from by
      by_cases hk : k ≤ (X.tr g).length
      · exact hval hk hσ
      · have h1 : Frame.stateAt (code L Q) X g k =
            Frame.stateAt (code L Q) X g (X.tr g).length := Frame.stateAt_of_le (by omega)
        exact hval le_rfl (h1.symm.trans hσ)]
    exact ReadsAs.of_erealValue hspec.1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
