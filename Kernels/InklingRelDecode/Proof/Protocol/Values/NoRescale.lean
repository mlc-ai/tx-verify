-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.SoftPw
public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSource
import Kernels.InklingRelDecode.Proof.Protocol.Values.DecisionBound
import Kernels.InklingRelDecode.Proof.Protocol.Values.RescaleCell
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BarRound
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
import Kernels.InklingRelDecode.Proof.Softmax.Export.Bar21Run
import Kernels.InklingRelDecode.Proof.Softmax.Export.Producer
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Softmax.Export.PollKeep
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand

@[expose] public section

/-! # A cell no rescale store covers in a round that runs has the factor one

In a round `b` with `0 < b < numIters` of a CTA that ran to completion, lane zero published the
round, so every data lane passed the round's last rendezvous (pc 1012); before it each lane either
skipped the rescale or made its rescale store. When the row's factor is not one, the decision does
not skip (`decision_false`), so the lane owning the cell stored it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A cell no rescale store of a round that runs covers has the factor one in it.** -/
theorem no_rescale_al (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    (hx : ∀ g, g < L.threads → ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩)
    (zero : ∀ c, NoUbLane X (c * L.block)) :
    ∀ c b row col, c < L.grid → row < 64 → col < 128 → Lib.QRowValid Q L c row → 0 < b →
      b < Q.numIters (ctaZ L c) (ctaXc L c) →
      (∀ st, ¬ RescaleAt L X st b ⟨c, 32 * (row / 16) + row % 16, 256 + col⟩) →
      Lib.foldAl Q L c b row = 1 := by
  intro c b row col hc hrow hcol valid hb hbn nost
  by_contra ne
  have blk : L.block = 256 := hp.block
  have hS := fun g k a vals sh (he : X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩) =>
    ld_s_fl hp hX hf hu safe base rows init hG hws ht hmd words nub form he
  have hB : ∀ g, Lib.BiasEv Q L g X := fun g => Softmax.Export.bias_ev hp hX hf
  have hSe : ∀ g, Lib.ScoreEv Q L g X := fun g =>
    score_ev hp hX hf hu safe base rows init hG hws ht hmd words nub form
  have pt : c * L.block < L.threads := by
    simp only [Launch.threads, blk]
    omega
  have pub : Softmax.Export.Published L X (c * L.block) b := by
    by_contra mis
    obtain ⟨-, noexit⟩ := Softmax.Export.prob_short hp hX hf (zero c) pt (by simp [blk])
      (by rw [Nat.mul_div_cancel _ (by omega : 0 < L.block)]; exact hbn) mis
    obtain ⟨pc, hl⟩ := hx _ pt
    rw [List.getLast?_eq_getElem?] at hl
    exact noexit _ pc hl
  obtain ⟨ka, arr, cnt⟩ := pub
  obtain ⟨u0, c0, hu0, bar⟩ := Softmax.Export.arrive_source hp hX arr
  obtain ⟨-, pr⟩ := Softmax.Export.arrival_polls hp hX hf arr
  have r0 : pollRound 1257 ((X.tr (c * L.block)).take u0) = b + 1 := by
    have := Softmax.Export.poll_keep bar (by show 1012 ≠ 1257; omega)
    rw [← this, hu0, pr]
    simp only [cnt]
  obtain ⟨t, ht⟩ : ∃ t, t = c * 256 + 32 * (row / 16) + row % 16 + 16 * (col / 64) := ⟨_, rfl⟩
  have tl : t % L.block < 128 := by rw [blk]; omega
  have tc : t / L.block = c := by rw [blk]; omega
  have passed : u0 + 1 < (X.tr (c * L.block)).length := by
    have : ka < (X.tr (c * L.block)).length := (List.getElem?_eq_some_iff.mp arr).1
    omega
  obtain ⟨ih, c', bar_t, -, rt, -⟩ := peer_bar hp hX hf safe (Or.inr (Or.inr (Or.inr rfl))) bar
    passed (by simp [blk]) tl (by rw [tc, Nat.mul_div_cancel _ (by omega : 0 < L.block)])
  rw [r0] at rt
  have valid_t : Lib.QRowValid Q L (t / L.block) row := by rw [tc]; exact valid
  have ne_t : Lib.foldAl Q L (t / L.block) b row ≠ 1 := by rw [tc]; exact ne
  rcases Softmax.Export.bar21_run hp hX hf bar_t (by omega) with
    ⟨k2, a, b', c', recv, ok, g2, rnd2, skip⟩ | ⟨k2, e, g2, pc2, nu2, rnd2⟩
  · have := decision_false hp hX hf safe hS hB hSe g2 tl (by omega) hrow valid_t ne_t
    rw [skip] at this
    exact Bool.noConfusion this
  · obtain ⟨p2, kd⟩ := e
    change p2 = 2328 at pc2
    subst pc2
    obtain ⟨a, vals, sh, rfl⟩ := st_kind_2328 hp hX hf base g2 nu2
    have cs := st_cell hp hX hf base g2 (col % 64)
    have len := (Softmax.Export.rescale_store hp hX g2).1
    have hl : laneOf L t = t % 32 := by
      unfold laneOf
      rw [blk]
      omega
    have h1 : t % L.block / 32 % 4 * 32 + t % 32 % 16 = 32 * (row / 16) + row % 16 := by
      rw [blk]
      omega
    have h2 : 256 + (if t % 32 < 16 then 0 else 64) + col % 64 = 256 + col := by
      split_ifs <;> omega
    refine nost (t, k2) ⟨a, vals, sh, col % 64, g2, by omega, ?_,
      by show pollRound 1257 ((X.tr t).take k2) = b + 1; omega⟩
    rw [cs, hl, tc, h1, h2]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
