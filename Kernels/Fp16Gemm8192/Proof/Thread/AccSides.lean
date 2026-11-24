-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoadWords

@[expose] public section

/-! # The two sides of the accumulator ring at its Tensor Memory accesses

Projections of the roles' run invariants at an MMA and at a Tensor Memory load.

* An MMA is issued by an MMA warp (8 or 9) of a leader CTA, holding its buffer's accumulator: its
  accumulator commits before it are one fewer than its successful polls of the buffer's empty
  barrier (`Mma.Counts.acc`, `mma_acc_batch_fact`).
* A load is issued by a consumer warp holding its accumulator: its successful polls of its
  accumulator's full barrier are one more than its arrivals on the empty barrier (`ConsRel`), and
  its next event is the load's wait (`cons_load_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **An MMA holds its buffer's accumulator.** -/
theorem mma_acc_batch_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} {d : ThreadD} {dst : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .tc (.mma dst sp acc mask)) :
    (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) ∧ g / L.block % 2 = 0 ∧
      ((X.tr g).take k).countP
          (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) + 1 =
        okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, false⟩)
          ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨m, s, j, rfl, hs, hlead, -, -⟩ := mma_issue_fact hpre hX hg he hσ hk
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp] at hw
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have h := hC.acc (m.w % 2) (Nat.mod_lt _ (by decide))
  simp only [↓reduceIte, Mma.holdsAcc, hs] at h
  have hww : m.w = g % L.block / 32 := hw.1
  rw [hww] at h
  exact ⟨hw.2, hlead, h⟩

/-- **A load holds its consumer's accumulator, and is followed by its wait.** -/
theorem cons_load_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc a : Nat} {vals : List Value}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    g % L.block / 32 < 8 ∧
      okPolls (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩) ((X.tr g).take k) =
        arrivals (Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, g % L.block / 32 / 4, false⟩)
          ((X.tr g).take k) + 1 ∧
      (k + 1 < (X.tr g).length → X.WaitLd (g, k + 1)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hblk : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ rfl
  -- the site is a load: a wait fires a wait event
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
  obtain ⟨j, hj⟩ : ∃ j, c.site = .load j := by
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, hj⟩
    · rw [hj] at hc hfire
      obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
      have := fires_tcWaitLd hblk hfire
      simp at this
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp, Prologue.warpOf] at hw
  have hrel : Consumer.ConsRel L g c ((X.tr g).take k) := Consumer.accInv hpre hg htr k _ hσ
  have h1 := hrel.1 (Consumer.accIdx L g) (by simp only [Consumer.accIdx, Consumer.tidOf]; omega)
  simp only [↓reduceIte, Consumer.holds, hj] at h1
  refine ⟨hw, h1, fun hlt => ?_⟩
  -- the state after the load is its wait
  have hsucc := Frame.stateAt_succ (C := code L) (X := X) (g := g) (k := k) he
  rw [hσ] at hsucc
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, k + 1) = some e' := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hσ1 : Frame.stateAt (code L) X g (k + 1) =
      some (some (.inr (.cons
        { c with site := .loadWait j, acc := Consumer.loadAcc c.acc j.val vals }))) := by
    rw [hsucc]
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    simp only at hj
    subst hj
    rfl
  obtain ⟨t', ins', o', -, -, hc', hfire'⟩ := Frame.fired_site (fun _ => sound hpre) hX he' hσ1
  change kernel.code[(Consumer.Site.loadWait j).pc]? = some ins' at hc'
  change Fires (Consumer.Site.loadWait j).pc (eventTmpl Prod L g t' ins'.op) e' o' at hfire'
  obtain rfl := Option.some.inj (hc'.symm.trans (Consumer.code_wait j))
  rw [fires_tcWaitLd hblk hfire'] at he'
  exact ⟨_, he'⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
