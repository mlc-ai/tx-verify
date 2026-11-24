-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Lanes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ring
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageRead
import Lemmas.Kernel.ElectSource
import Lemmas.Order.OrderBaseCausality
import Lemmas.Order.OrderWaits
import Lemmas.Protocol.NamedBarArrive
import Lemmas.Protocol.PollIndex
import Lemmas.Tensor.BoxWrite
import Lemmas.Tensor.TensorCompleteConsistentRead
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of bias copies and bias reads

* A softmax lane's events before its stage-barrier event of round `j` precede, in base causality,
  every loader event past the poll of round `j + 1` of the empty barrier (`bias_cause`).
* A byte of a bias stage's window is written only by tensor copies (`BiasWrites`), and the copies
  that write a byte of box `q` are those of the stage's lane with `2 u + q` earlier ones
  (`bias_writer`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Every write to the bias window `[sb + 166912, sb + 232448)` is a tensor copy's. -/
def BiasWrites (L : Launch) (X : Execution) : Prop :=
  ∀ w a bs l, X.MemWrites w a bs → a.Covers l → l.space = .shared →
    L.sharedBase + 166912 ≤ l.addr → l.addr < L.sharedBase + 232448 →
    ∃ i x y k, w = .async i (.write (.load x y k))

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)

include hX in
/-- The lane of warp 14 that won an election wins every election it takes part in. -/
theorem tmaLane_won {k j pc mask mask' inst inst' pc' ld : Nat}
    (hj : X.get (tmaLane L X g, j) =
      some ⟨pc', .elect mask' inst' (laneOf L (tmaLane L X g))⟩)
    (he : X.get (tmaLane L X g, k) = some ⟨pc, .elect mask inst ld⟩) :
    ld = laneOf L (tmaLane L X g) := by
  have hlt := Frame.lt_of_get hX he
  have hw : SameWarp L (tmaLane L X g) (tmaLane L X g) := ⟨⟨hlt, hlt, rfl⟩, rfl⟩
  have e1 := elect_full hX (show X.Elect (tmaLane L X g, k) pc mask inst ld from he)
  have e2 := elect_full hX (show X.Elect (tmaLane L X g, j) pc' mask' inst' _ from hj)
  subst e1 e2
  exact elect_leader hX he hj hw

include hp hX hFw

/-- **A softmax lane's events precede the loader's next round.** -/
theorem bias_cause (hB : TmaBytes X) {st : Fin 2} {h : Nat} (hh : SoftIn L g st.val h)
    {j f : Nat} (hf : f < (X.tr (tmaLane L X g)).length)
    (hpol : j + 2 ≤ okPolls (bE L g st) ((X.tr (tmaLane L X g)).take f)) :
    ∃ i pci, X.get (h, i) = some ⟨pci, .bar (stageId st.val) (some 128) .sync⟩ ∧
      barOrd X h i (stageId st.val) = j ∧
      ∀ e < i, baseCausality L X (h, e) (tmaLane L X g, f) := by
  have hj : j + 1 < okPolls (bE L g st) (X.tr (tmaLane L X g)) := by
    have := Poll.okPolls_mono (bE L g st) (X.tr (tmaLane L X g)) hf.le
    rw [List.take_of_length_le le_rfl] at this
    omega
  obtain ⟨y, z, pcz, i, pci, a, pca, sca, hyc, hz, hza, ha, -, hi, hio, hzo, -, -, hub⟩ :=
    bias_release hp hX hFw hB hh hj
  refine ⟨i, pci, hi, hio, fun e he => ?_⟩
  obtain ⟨w, pcw, par, acq, sc, hwf, hw, hwo⟩ := Poll.exists_nth hpol
  have hnth : Poll.nth X (bE L g st) (tmaLane L X g) (j + 1) = w := by
    rw [← hwo]; exact Poll.nth_eq hw
  rw [hnth] at hub
  have hacq : acq = true := by
    rcases biasFree_use hp hX hFw st hw rfl (fun _ h => by cases h) with
      ⟨-, _, _, hk⟩ | ⟨hk, _⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, -, -, hacq, -⟩ := hk
      exact hacq
    · cases hk
  subst hacq
  have hal : a < (X.tr y).length := by
    have := len_of_get ha
    simpa using this
  have hst := st.isLt
  have hsame : SameCta L h y := ⟨hh.1, Frame.lt_of_get hX hz, hh.2.1.trans hyc.symm⟩
  have b1 := (stage_sources hp hX hFw hst).arrive_sync_baseCausality hX (stage_shape hp hst) hsame
    hi (show X.IsBarrier (y, z) (stageId st.val) (some 128) pcz from hz) (by omega)
    (hio.trans hzo.symm) he hza hal
  have hty := (tmaLane_in (X := X) hp g).1
  have hmeet : ScopesMeet L sca y sc (tmaLane L X g) :=
    ScopesMeet.of_sameCta ⟨Frame.lt_of_get hX hz, Frame.lt_of_get hX hw, hyc.trans hty.symm⟩
  exact b1.tail (.inr (.inr (.inl ⟨(y, a), (tmaLane L X g, w), bE L g st, sca, sc,
    ⟨0, 1, pca, ha⟩, ⟨⟨pcw, par, hw⟩, hub⟩, hmeet, rfl, hwf, hf, rfl, le_rfl⟩)))

/-- **Who writes a byte of a bias box**: a copy of the stage's loader lane whose earlier copies on
the stage's barrier have the box's parity. -/
theorem bias_writer {st q : Fin 2} {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) {x y k : Nat} {l : Loc}
    (hl : TensorCopy.writeLoc s x y k = some l) (hcta : l.cta = g / L.block)
    (hlo : L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) ≤ l.addr)
    (hhi : l.addr < L.sharedBase + (166912 + 32768 * st.val + 16384 * q.val) + 16384) :
    i.1 = tmaLane L X g ∧ s.mbar = bF L g st ∧
      ((X.tr i.1).take i.2).countP (issuesTo (bF L g st)) % 2 = q.val ∧
      ∃ j org, s = inputSpec p L (g / L.block) j org s.mbar ∧
        (Loader.inputSite j).bias = true ∧
        (Loader.inputSite j).sharedOffset = 166912 + 32768 * st.val + 16384 * q.val := by
  obtain ⟨h, c⟩ := i
  obtain ⟨hw, j, org, mb, -, hs⟩ := input_box hp hX hFw he
  obtain ⟨m1, m2, m3, m4, -⟩ := input_map p j
  -- the byte is in the copy's box
  have hbx : l.cta = h / L.block ∧ L.sharedBase + (Loader.inputSite j).sharedOffset ≤ l.addr ∧
      l.addr < L.sharedBase + (Loader.inputSite j).sharedOffset + 16384 := by
    subst hs
    have hf2 : (Loader.inputMap p (Loader.inputSite j)).format.bytes = 2 := by rw [m3]; rfl
    obtain ⟨b1, b2⟩ := box_lt m1 m2 hf2 m4 hl
    obtain ⟨slot, -, rfl⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨rfl, b1, b2⟩
  obtain ⟨c1, c2, c3⟩ := hbx
  have hc : h / L.block = g / L.block := c1.symm.trans hcta
  -- so the box is the stage's box `q`
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 14, (Loader.inputSite j0).sharedOffset =
      166912 + 32768 * st.val + 16384 * q.val := by
    have key : ∀ st q : Fin 2, ∃ j0 : Fin 14, (Loader.inputSite j0).sharedOffset =
        166912 + 32768 * st.val + 16384 * q.val := by decide
    exact key st q
  have hoff := site_apart j j0 (by omega) (by omega)
  have hbar : s.mbar = obj L h (320 + 8 * st.val) := by
    refine ld_bias_bar hp hX hFw hw he st q ?_
    rw [hs]
    show L.sharedBase + (Loader.inputSite j).sharedOffset = _
    omega
  have hbar' : s.mbar = bF L g st := by rw [hbar, obj_cta hc]
  obtain ⟨hlane, -⟩ := tma_copy hp hX hFw (g := g) (b_tmaOff st) he hbar'
  subst hlane
  obtain ⟨-, -, jw, pcw, maskw, instw, -, hjw⟩ := ld_tma_copy hp hX hFw hw (b_tmaOff st) he hbar
  obtain ⟨j', org', hs', hbi, hoff'⟩ := ld_bias_copy hp hX hFw hw
    (fun k pc mask inst ld hk => tmaLane_won hX hjw hk) st he hbar
  have hoo : obj L (tmaLane L X g) (320 + 8 * st.val) = bF L g st := by rw [obj_cta hc]
  rw [hoo] at hoff'
  simp only at hoff'
  have hjj : (Loader.inputSite j').sharedOffset = (Loader.inputSite j).sharedOffset := by
    have := congrArg (fun s : TensorCopy.Spec => s.sharedBase.addr) (hs'.symm.trans hs)
    simp only [inputSpec] at this
    omega
  rw [hc] at hs'
  have hm2 := Nat.mod_lt (((X.tr (tmaLane L X g)).take c).countP (issuesTo (bF L g st)))
    (show 0 < 2 by decide)
  have hq := q.isLt
  refine ⟨rfl, hbar', ?_, j', org', hs', hbi, by omega⟩
  show ((X.tr (tmaLane L X g)).take c).countP (issuesTo (bF L g st)) % 2 = q.val
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
