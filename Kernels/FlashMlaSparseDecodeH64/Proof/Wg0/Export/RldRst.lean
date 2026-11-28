-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PlaceWalk
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
import Lemmas.Flow.Arith32Norm
import Lemmas.Flow.TcStLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode

@[expose] public section

/-! # A chunk's rescale load is before its store of the same block

Two events of one lane of warpgroup 0, a chunk-`c` rescale load and a chunk-`c` rescale store with
the same arrivals on `soReady` (one block), are ordered: the machine's place grows along the lane
(`place_lt`) and the load's site is placed before the store's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

private theorem site_rld (s : Wg0.Site) (c : Fin 4)
    (h : s.pc = [716, 817, 918, 1019].getD c.val 0) : s = .rld c := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals fin_cases c
  all_goals first | (intro; rfl) | (intro h; exfalso; revert h; decide)

private theorem site_rst (s : Wg0.Site) (c : Fin 4)
    (h : s.pc = [814, 915, 1016, 1117].getD c.val 0) : s = .rst c := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals fin_cases c
  all_goals first | (intro; rfl) | (intro h; exfalso; revert h; decide)


private theorem site_rldw (s : Wg0.Site) (c : Fin 4)
    (h : s.pc = [717, 818, 919, 1020].getD c.val 0) : s = .rldw c := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals fin_cases c
  all_goals first | (intro; rfl) | (intro h; exfalso; revert h; decide)

/-- The state of a rescale site: its block `r` (the lane's arrivals on `soReady` are the uses
before `r`), the block index word and the place. -/
private theorem rs_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i pc : Nat} {kd : Kind}
    (hub : ∀ f, kd ≠ .ub f) {s : Wg0.Site} (he : X.get (y, i) = some ⟨pc, kd⟩)
    (hs : ∀ d : Wg0.Control.D, d.site.pc = pc → d.site = s)
    (hrng : 103 ≤ pc ∧ pc < 1842) (hloop : s.reg = .loop) (hidx : s.idx = 3) :
    ∃ (d : Wg0.Control.D) (n : Cls → Nat) (r : Nat),
      Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d⟩, n)) ∧ d.site = s ∧
      (∀ j : Fin 2, arrivals (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i) =
        ringUses 2 j r) ∧ d.bi.toNat = r + 1 ∧
      Wg0.EvK P L y (warpW L y) d ⟨pc, kd⟩ := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hRn, hEv, -⟩ := wg0_state hJ hi hev hpc' hrng
  have hsd : d.site = s := hs d hpc'.symm
  have hR := hRn (state_ub hX hσ he)
  rw [show (fun c => n (.wg0 c)) = fun c => ((X.tr y).take i).countP (Wg0.cls c) from
    funext fun c => state_count hσ (.wg0 c)] at hR
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  simp only [Wg0.RefCore, hsd, hloop, hidx, Wg0.RefAt] at hc
  obtain ⟨r, ⟨-, hRo, hrR, hbi, -⟩, hq, ha⟩ := hc
  simp only [Wg0.Control.D.words] at hbi hRo hrR
  exact ⟨d, n, r, hσ, hsd, fun j =>
    (wg0_arrivals hp hX hFw hw _ _).trans ((ha _).trans (Wg0.arr_so hp _ _ _ _)),
    by rw [hbi]; exact toNat_W (by omega), hEv.2⟩


private theorem ru_inj {r r' : Nat} (h0 : ringUses 2 0 r = ringUses 2 0 r')
    (h1 : ringUses 2 1 r = ringUses 2 1 r') : r = r' := by
  unfold ringUses at h0 h1
  omega

/-- **A chunk's rescale load is before its store of the same block**: the load and the store of
chunk `c` of one lane with the same arrivals on `soReady`. -/
theorem wg0_rld_before_rst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i i' a a' : Nat}
    {vals vals' : List Value} {sh sh' : TcShape} {c : Fin 4}
    (hi : X.get (y, i) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩)
    (hi' : X.get (y, i') = some ⟨[814, 915, 1016, 1117].getD c.val 0, .tc (.st a' vals' sh')⟩)
    (harr : ∀ j : Fin 2, arrivals (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i) =
      arrivals (mbarLoc L (y / L.block) (.soReady j)) ((X.tr y).take i')) : i < i' := by
  have hy : y < L.threads := Frame.lt_of_get hX hi
  have hrng : ∀ c : Fin 4, 103 ≤ [716, 817, 918, 1019].getD c.val 0 ∧
      [716, 817, 918, 1019].getD c.val 0 < 1842 ∧ 103 ≤ [814, 915, 1016, 1117].getD c.val 0 ∧
      [814, 915, 1016, 1117].getD c.val 0 < 1842 := by decide
  obtain ⟨hr1, hr1', hr2, hr2'⟩ := hrng c
  obtain ⟨d, n, r, hσ, hs, hr, hbi, -⟩ := rs_state hp hX hFw hw (fun _ h => by cases h) hi
    (fun d h => site_rld d.site c h) ⟨hr1, hr1'⟩ rfl rfl
  obtain ⟨d', n', r', hσ', hs', hr', hbi', -⟩ := rs_state hp hX hFw hw (fun _ h => by cases h) hi'
    (fun d h => site_rst d.site c h) ⟨hr2, hr2'⟩ rfl rfl
  have hrr : r = r' := ru_inj ((hr 0).symm.trans ((harr 0).trans (hr' 0)))
    ((hr 1).symm.trans ((harr 1).trans (hr' 1)))
  subst hrr
  have hpl : Wg0.place d < Wg0.place d' := by
    simp only [Wg0.place, hs, hs', Wg0.regPlace, Wg0.Site.reg, Wg0.elOff, hbi, hbi',
      Wg0.Site.ord]
    omega
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact hlt
  · subst heq
    rw [hi] at hi'
    simp only [Option.some.injEq, Event.mk.injEq] at hi'
    have := hi'.1
    fin_cases c <;> simp at this
  · have := place_lt hFw hw hy (noUbBefore_of_get hX hi) hi' (by simp [Event.counts]) hgt hσ' hσ
    omega


/-- **A rescale load's address**: the load of chunk `c` reads from column `64 c`, `32x32b`. -/
theorem wg0_rld_addr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i a : Nat} {vals : List Value}
    {sh : TcShape} {c : Fin 4}
    (hi : X.get (y, i) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩) :
    a = 64 * c.val ∧ sh = .s32x32b := by
  have hrng : ∀ c : Fin 4, 103 ≤ [716, 817, 918, 1019].getD c.val 0 ∧
      [716, 817, 918, 1019].getD c.val 0 < 1842 := by decide
  obtain ⟨d, n, r, hσ, hs, hr, hbi, hE⟩ := rs_state hp hX hFw hw (fun _ h => by cases h) hi
    (fun d h => site_rld d.site c h) (hrng c) rfl rfl
  have hub : ∀ f, Kind.tc (.ld a vals sh) ≠ .ub f := fun _ h => by cases h
  simp only [Wg0.EvK, hs, Wg0.TcLdEv] at hE
  rcases hE with ⟨vs, hv⟩ | ⟨f, hf⟩
  · simp only [Kind.tc.injEq, TcKind.ld.injEq] at hv
    obtain ⟨h1, -, h3⟩ := hv
    exact ⟨h1, h3⟩
  · exact absurd hf (hub f)

/-- **A rescale store's address and length**: a Tensor Memory store of warpgroup 0 is the store of
some chunk `c`, at column `64 c`, `32x32b`, of 64 words. -/
theorem wg0_rst_addr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i pc a : Nat}
    {vals : List Value} {sh : TcShape}
    (hi : X.get (y, i) = some ⟨pc, .tc (.st a vals sh)⟩) :
    ∃ c : Fin 4, pc = [814, 915, 1016, 1117].getD c.val 0 ∧ a = 64 * c.val ∧
      sh = .s32x32b ∧ vals.length = 64 := by
  have hrng : ∀ c : Fin 4, 103 ≤ [814, 915, 1016, 1117].getD c.val 0 ∧
      [814, 915, 1016, 1117].getD c.val 0 < 1842 := by decide
  have hub : ∀ f, Kind.tc (.st a vals sh) ≠ .ub f := fun _ h => by cases h
  rcases get_source hX hi with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  have hk : (⟨pc, .tc (.st a vals sh)⟩ : Event).kind = .tc (.st a vals sh) := rfl
  have hq := fires_tcSt_op hf hk
  obtain ⟨ta, ss, sh', hop⟩ : ∃ ta ss sh', ins.op = .tcSt ta ss sh' := by
    cases hh : ins.op <;> simp only [hh, tcStOp] at hq <;> first | exact ⟨_, _, _, rfl⟩ | cases hq
  obtain ⟨c, hpc⟩ := rst_of_code hc hop
  simp only at hpc
  obtain ⟨d, n, r, hσ, hs, hr, hbi, hE⟩ := rs_state hp hX hFw hw (fun _ h => by cases h) hi
    (fun d h => site_rst d.site c (by rw [h, hpc])) (by rw [hpc]; exact hrng c) rfl rfl
  simp only [Wg0.EvK, hs, Wg0.TcStEv] at hE
  rcases hE with ⟨vs, hv⟩ | ⟨f', hf'⟩
  · simp only [Kind.tc.injEq, TcKind.st.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    obtain ⟨ins', ta', ss', sh2, hc', hop', hl⟩ := get_tcSt_len hX hi rfl
    have : ss'.length = 64 := stLen_of_code hc' hop'
    exact ⟨c, hpc, rfl, rfl, by omega⟩
  · exact absurd hf' (hub f')

/-- **The event after a rescale load is its wait**: at the pc of chunk `c`'s `rldw`. -/
theorem wg0_rldw_kind (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {i : Nat} {kd : Kind} {c : Fin 4}
    (hi : X.get (y, i) = some ⟨[717, 818, 919, 1020].getD c.val 0, kd⟩)
    (hub : ∀ f, kd ≠ .ub f) : kd = .tc .waitLd := by
  have hrng : ∀ c : Fin 4, 103 ≤ [717, 818, 919, 1020].getD c.val 0 ∧
      [717, 818, 919, 1020].getD c.val 0 < 1842 := by decide
  obtain ⟨d, n, r, hσ, hs, hr, hbi, hE⟩ := rs_state hp hX hFw hw hub hi
    (fun d h => site_rldw d.site c h) (hrng c) (by fin_cases c <;> rfl) (by fin_cases c <;> rfl)
  simp only [Wg0.EvK, hs] at hE
  exact hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
