-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PrevPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepInto
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccOld
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst

@[expose] public section

/-! # The words a staging store reads are its chunk's load

At a staging store `ost2 c j` the block in progress's last output load (`w0EpiO`) is the chunk's
load `old c`, at column `64 c`, after the lane's poll of `svDone` (`w0_epiO_old`): the events from
the load to the store are its wait and staging stores, none of them a load at a pc of `w0OPcs`. -/

/-! # The staging stores of a chunk follow the chunk's load and its wait

The events before the staging store `ost2 c j` of warpgroup 0 are, back to the chunk's output load
(`old c`, a `tcgen05.ld`) and its wait, staging stores of the chunk (`w0_ost2_prev`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

private theorem arrS_not_ost2 {c c' : Control.D} {f : Event} {k : Fin 4} {j : Fin 8}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hc : c.site = .arrS)
    (hs : c'.site = .ost2 k j) : False := by
  simp only [Control.succ, hc] at h
  split at h <;> cases h <;> simp_all

private theorem arrS_not_oldw {c c' : Control.D} {f : Event} {k : Fin 4}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hc : c.site = .arrS)
    (hs : c'.site = .oldw k) : False := by
  simp only [Control.succ, hc] at h
  split at h <;> cases h <;> simp_all

/-- **The staging stores of chunk `c` follow its load and the load's wait** (valid trace). -/
theorem w0_ost2_prev_hub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {c : Fin 4} :
    ∀ (k : Nat), LaneAlive X g k → W0Valid P.scale ((X.tr g).take k) →
    ∀ (j : Fin 8) {e : Event}, X.get (g, k) = some e → e.pc = ost2Base c + j.val →
      ∃ (kl : Nat) (f0 f1 : Event) (a : Nat) (vals : List Value) (sh : TcShape), kl + 2 ≤ k ∧
        X.get (g, kl) = some f0 ∧ f0.pc = [1201, 1361, 1519, 1676].getD c.val 0 ∧
        f0.kind = .tc (.ld a vals sh) ∧ X.get (g, kl + 1) = some f1 ∧
        f1.pc = [1202, 1362, 1520, 1677].getD c.val 0 ∧
        ∀ q, kl + 2 ≤ q → q ≤ k → ∀ ev, X.get (g, q) = some ev →
          ∃ j' : Fin 8, ev.pc = ost2Base c + j'.val := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hal hv0 j e he hpc
    have hrg : 103 ≤ e.pc ∧ e.pc < 1842 := by
      rw [hpc]; fin_cases c <;> simp [ost2Base] <;> omega
    have hge := hrg.1
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := by
      cases k with
      | zero => exact (w0_not_first hp hX hFw he (hal _ e he le_rfl) hrg).elim
      | succ j => exact ⟨j, rfl⟩
    obtain ⟨f, c1, d1, hf, hpcf, hs1, hsucc1, hc1⟩ := w0_step_into_hub hp hX hFw hw he
      (hal _ e he le_rfl) hge hv0 (s := .ost2 c j) (fun s' h => site_pc_ost2 (h.trans hpc))
      (by simp [innerSite, onChain, isStart])
    have hok : succOk c1 d1.c = true := by
      rcases hc1 with h | h
      · exact (arrS_not_ost2 hsucc1 h hs1).elim
      · exact h
    have hstay : ∀ {j' : Fin 8}, c1.site = .ost2 c j' → ∃ (kl : Nat) (f0 f1 : Event) (a : Nat)
        (vals : List Value) (sh : TcShape), kl + 2 ≤ k1 + 1 ∧
        X.get (g, kl) = some f0 ∧ f0.pc = [1201, 1361, 1519, 1676].getD c.val 0 ∧
        f0.kind = .tc (.ld a vals sh) ∧ X.get (g, kl + 1) = some f1 ∧
        f1.pc = [1202, 1362, 1520, 1677].getD c.val 0 ∧
        ∀ q, kl + 2 ≤ q → q ≤ k1 + 1 → ∀ ev, X.get (g, q) = some ev →
          ∃ j'' : Fin 8, ev.pc = ost2Base c + j''.val := by
      intro j' hj'
      have hpcf' : f.pc = ost2Base c + j'.val := by rw [← hpcf, hj']; rfl
      obtain ⟨kl, f0, f1, a, vals, sh, hkl, h0, hp0, hk0, h1, hp1, hq⟩ :=
        ih k1 (by omega) (fun i f' hi hk => hal i f' hi (by omega))
          (Wg0.W0Valid.take_le hv0 (by omega)) j' hf hpcf'
      refine ⟨kl, f0, f1, a, vals, sh, by omega, h0, hp0, hk0, h1, hp1, fun q hq1 hq2 ev hev => ?_⟩
      by_cases hqk : q = k1 + 1
      · subst hqk
        rw [he] at hev
        cases hev
        exact ⟨j, hpc⟩
      · exact hq q hq1 (by omega) ev hev
    rcases succOk_ost2 hok hs1 with h | ⟨j', -, h⟩ | ⟨hj0, h⟩
    · exact hstay h
    · exact hstay h
    · -- the wait of the chunk's load
      have hpcf' : f.pc = [1202, 1362, 1520, 1677].getD c.val 0 := by
        rw [← hpcf, h]; rfl
      obtain ⟨k0, rfl⟩ : ∃ k0, k1 = k0 + 1 := by
        cases k1 with
        | zero =>
          refine (w0_not_first hp hX hFw hf (hal _ _ hf (by omega)) ?_).elim
          rw [hpcf']
          fin_cases c <;> decide
        | succ j => exact ⟨j, rfl⟩
      obtain ⟨f0, c0, d0, hf0, hpcf0, hs0, hsucc0, hc0⟩ := w0_step_into_hub hp hX hFw hw hf
        (hal _ _ hf (by omega)) (by rw [hpcf']; fin_cases c <;> decide)
        (Wg0.W0Valid.take_le hv0 (by omega)) (s := .oldw c)
        (fun s' h => site_pc_inj (h.trans hpcf')) (by fin_cases c <;> decide)
      have hok0 : succOk c0 d0.c = true := by
        rcases hc0 with h | h
        · exact (arrS_not_oldw hsucc0 h hs0).elim
        · exact h
      have hold : c0.site = .old c := succOk_oldw hok0 hs0
      have hsl : Control.succ P L g (warpW L g) c0 f0 = some (some d0.c) := hsucc0
      have hkind : ∃ a vals sh, f0.kind = .tc (.ld a vals sh) := by
        simp only [Control.succ, hold, Control.tcLoad] at hsl
        split at hsl
        · rename_i a vals sh hk
          exact ⟨a, vals, sh, hk⟩
        · cases hsl
      obtain ⟨a, vals, sh, hk⟩ := hkind
      refine ⟨k0, f0, f, a, vals, sh, by omega, hf0, ?_, hk, hf, hpcf', fun q hq1 hq2 ev hev => ?_⟩
      · rw [← hpcf0, hold]; rfl
      · by_cases hqk : q = k0 + 1 + 1
        · subst hqk
          rw [he] at hev
          cases hev
          exact ⟨j, hpc⟩
        · omega

/-- **The staging stores of chunk `c` follow its load and the load's wait** (from `¬ HasUb`). -/
theorem w0_ost2_prev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv0 : W0Trace P X g)
    {c : Fin 4} :
    ∀ (k : Nat) (j : Fin 8) {e : Event}, X.get (g, k) = some e → e.pc = ost2Base c + j.val →
      ∃ (kl : Nat) (f0 f1 : Event) (a : Nat) (vals : List Value) (sh : TcShape), kl + 2 ≤ k ∧
        X.get (g, kl) = some f0 ∧ f0.pc = [1201, 1361, 1519, 1676].getD c.val 0 ∧
        f0.kind = .tc (.ld a vals sh) ∧ X.get (g, kl + 1) = some f1 ∧
        f1.pc = [1202, 1362, 1520, 1677].getD c.val 0 ∧
        ∀ q, kl + 2 ≤ q → q ≤ k → ∀ ev, X.get (g, q) = some ev →
          ∃ j' : Fin 8, ev.pc = ost2Base c + j'.val :=
  fun k j _ he hpc => w0_ost2_prev_hub hp hX hFw hw k (LaneAlive.of_noUb hnu g k)
    (hv0.take k) j he hpc

end Wg0
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The staging store's words** (valid trace): the chunk's load, its address, the poll before
it, and the words the block in progress reads from its last output load. -/
theorem w0_epiO_old (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv0 : W0Trace P X g)
    {c : Fin 4} {j : Fin 8} {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hpc : e.pc = Wg0.ost2Base c + j.val) :
    ∃ (kl jw p a : Nat) (vals : List Value), kl + 2 ≤ k ∧
      X.get (g, kl) = some ⟨[1201, 1361, 1519, 1676].getD c.val 0, .tc (.ld a vals .s32x32b)⟩ ∧
      a = 64 * c.val ∧ jw < kl ∧ X.get (g, jw) = some ⟨1184, .wait (mbarLoc L (g / L.block)
        (.svDone (slot2 (blocksOf P L (g / L.block) - 1)))) p true true .cta⟩ ∧
      w0EpiO (w0Scan ((X.tr g).take k)).2 = vals := by
  obtain ⟨kl, f0, f1, a, vals, sh, hkl, h0, hp0, hk0, h1, hp1, hq⟩ :=
    Wg0.w0_ost2_prev hp hX hFw hnu hw hv0 k j he hpc
  have hrng : ∀ c : Fin 4, 103 ≤ [1201, 1361, 1519, 1676].getD c.val 0 ∧
      [1201, 1361, 1519, 1676].getD c.val 0 < 1842 := by decide
  have hf0 : X.get (g, kl) = some ⟨[1201, 1361, 1519, 1676].getD c.val 0, .tc (.ld a vals sh)⟩ := by
    obtain ⟨pc0, kd0⟩ := f0
    simp only at hp0 hk0
    subst hp0 hk0
    exact h0
  have hub := noUb_kind hnu hf0
  obtain ⟨σ, hσ, hJ, hi, hev, hpc0⟩ := ev_at hp hX hFw hf0 hub
  obtain ⟨d, n, rfl, -, ⟨-, hE⟩, -⟩ := wg0_state hJ hi hev hpc0 (hrng c)
  have hs : d.site = .old c := PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.site_pc_inj (by
    have : [1201, 1361, 1519, 1676].getD c.val 0 = d.site.pc := hpc0
    rw [← this]; rfl)
  simp only [Wg0.EvK, hs, Wg0.TcLdEv] at hE
  obtain ⟨ha, hsh⟩ : a = 64 * c.val ∧ sh = .s32x32b := by
    rcases hE with ⟨vs, hv⟩ | ⟨f, hf⟩
    · simp only [Kind.tc.injEq, TcKind.ld.injEq] at hv
      obtain ⟨h1, -, h3⟩ := hv
      exact ⟨h1, h3⟩
    · exact absurd hf (hub f)
  subst hsh
  obtain ⟨jw, p, hjw, hpoll⟩ := wg0_old_poll hp hX hFw hw hf0
    ⟨c.val, c.isLt, rfl⟩ (hrng c)
  refine ⟨kl, jw, p, a, vals, hkl, hf0, ha, hjw, hpoll, ?_⟩
  have hf1pc : f1.pc ∉ w0OPcs ∧ f1.pc ≠ w0ArrSPc ∧ f1.pc ≠ w0ArrLPc := by
    rw [hp1]; fin_cases c <;> simp [w0OPcs, w0ArrSPc, w0ArrLPc]
  have hf0pc : f0.pc ∈ w0OPcs ∧ f0.pc ≠ w0ArrSPc ∧ f0.pc ≠ w0ArrLPc := by
    rw [hp0]; fin_cases c <;> simp [w0OPcs, w0ArrSPc, w0ArrLPc]
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h0' : (X.tr g)[kl]? = some f0 := h0
  have h1' : (X.tr g)[kl + 1]? = some f1 := h1
  have hbase : w0EpiO (w0Scan ((X.tr g).take (kl + 2))).2 = vals := by
    have htake : (X.tr g).take (kl + 2) = (X.tr g).take kl ++ [f0, f1] := by
      rw [show kl + 2 = (kl + 1) + 1 from rfl, List.take_add_one, List.take_add_one]
      simp [h0', h1']
    have e : (X.tr g).take kl ++ [f0, f1] = ((X.tr g).take kl ++ [f0]) ++ [f1] := by simp
    rw [htake, e, w0Scan_snoc, w0Scan_snoc]
    simp only [hf0pc.2.1, hf1pc.2.1, ite_false]
    unfold w0EpiO w0Last
    simp [List.filterMap_append, hf0pc.1, hf1pc.1, w0TcVals, hk0]
  have key : ∀ d, kl + 2 + d ≤ k →
      w0EpiO (w0Scan ((X.tr g).take (kl + 2 + d))).2 = vals := by
    intro d
    induction d with
    | zero => intro _; exact hbase
    | succ d ih =>
      intro hd
      obtain ⟨ev, hev⟩ : ∃ ev, X.get (g, kl + 2 + d) = some ev :=
        ⟨_, List.getElem?_eq_getElem (l := X.tr g) (i := kl + 2 + d) (by omega)⟩
      obtain ⟨j', hj'⟩ := hq (kl + 2 + d) (by omega) (by omega) ev hev
      have hnp : ev.pc ∉ w0OPcs ∧ ev.pc ≠ w0ArrSPc := by
        rw [hj']
        fin_cases c <;> fin_cases j' <;> simp [Wg0.ost2Base, w0OPcs, w0ArrSPc]
      have htk : (X.tr g).take (kl + 2 + (d + 1)) = (X.tr g).take (kl + 2 + d) ++ [ev] := by
        rw [show kl + 2 + (d + 1) = (kl + 2 + d) + 1 from rfl, List.take_add_one]
        have h' : (X.tr g)[kl + 2 + d]? = some ev := hev
        simp [h']
      rw [htk, w0Scan_snoc]
      simp only [hnp.2, ite_false]
      unfold w0EpiO at ih ⊢
      rw [Wg0.Data.w0Last_snoc]
      simp only [hnp.1, ite_false]
      exact ih (by omega)
  have := key (k - (kl + 2)) (by omega)
  rwa [show kl + 2 + (k - (kl + 2)) = k by omega] at this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
