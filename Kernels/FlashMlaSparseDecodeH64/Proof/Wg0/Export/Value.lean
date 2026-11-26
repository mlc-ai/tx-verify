-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Lemmas.Flow.RoleStep
import Lemmas.Flow.StoreElem
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # Warpgroup 0's softmax statistics against the reference

The reference side of the value export: what the loop of warpgroup 0 computes, block by block,
from the words its loads read (`Iface/W0Value.lean`: `w0Next`). Against `Result.Run`
(`Lib/Result/RunState.lean`), whose exponent sequence `c` is arbitrary, the code differs in one
point: it is lazy. The maximum `m` (the code's `%r2492`) moves only when the warp's vote sees a
rise above 6 (`vt`), so a block's probabilities `2 ^ (sc s - m')` may exceed one (up to `2 ^ 6`
for the lane's own columns), and `c = m` is the sequence the code uses. With that `c`, the lane's
partial row sum is exactly the `l_step` of `Run`:

`l' = l * 2 ^ (m - m') + Σ_i w_i * 2 ^ (-m')`, with `w_i = 2 ^ (sc s_i)` for a kept column.

**The probabilities a lane stores** (`w0_pstore_value`, valid rows): the data thread machine
(`threadD`) follows the lane on every trace (`followW`: the data machine never stops the control
machine), and with it the invariants of `Wg0/Data`: the words of the block in progress are the
trace's last loads (`InvW`), the carried statistics are those of the finished blocks (`CarryW`), the
chain's flag is set on the loop's sites (`OkInv`) and the block has its vote at the stores
(`VoteInv`). At a probability store the source register holds the bf16 word of two probabilities
(`w0_block`), and the store writes its bytes (`fires_st_elemBytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

/-- The weight of a column: `2 ^ (sc s)` for a kept column, zero for a dropped one. -/
def w0Weight (sc : ℝ) (s : EReal) : ℝ := if s = ⊥ then 0 else (2 : ℝ) ^ (sc * s.toReal)

theorem w0Prob_eq (sc m : ℝ) (s : EReal) : w0Prob sc m s = w0Weight sc s * (2 : ℝ) ^ (-m) := by
  unfold w0Prob w0Weight
  split_ifs
  · simp
  · rw [← Real.rpow_add (by norm_num), sub_eq_add_neg]


variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

private theorem mem_take_get {f : Event} {j : Nat} (h : f ∈ (X.tr g).take j) :
    ∃ j' < j, X.get (g, j') = some f := by
  obtain ⟨i, hi, hf⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at hf
  rw [List.length_take] at hi
  exact ⟨i, by omega, by rw [← hf]; exact List.getElem?_eq_getElem _⟩

/-- The store's instruction: element `q` is a weak shared store of the pack of two probabilities. -/
private def PStoreOk (a : MemAccess) (j : Nat) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧
    (∀ q < 4, a.srcs[q]? = some (.reg (1115 + 3 * (4 * j + q)))) ∧ a.elem.width = 32

private theorem pstc {pc j : Nat} {a : MemAccess} (h : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hk : PStoreOk a j := by
      refine ⟨rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, fun q hq => ?_, rfl⟩
      match q, hq with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl) :
    ∃ a, kernel.code[pc]? = some ⟨none, .mem a⟩ ∧ PStoreOk a j := ⟨a, h, hk⟩

private theorem pstore_code (j : Fin 4) :
    ∃ a, kernel.code[704 + j.val]? = some ⟨none, .mem a⟩ ∧ PStoreOk a j.val := by
  fin_cases j
  exacts [pstc Flow.code_704, pstc Flow.code_705, pstc Flow.code_706, pstc Flow.code_707]

end Wg0

open Wg0 Wg0.Data Wg0.Gen in
/-- **The probabilities a lane of warpgroup 0 stores** (valid rows): the store at pc `704 + j`
writes the bf16 word of two probabilities, the word `4 j + q` of the block in progress for some
element `q < 4` of the vector store: `w0PWord` of its columns `2 (4 j + q)` and `2 (4 j + q) + 1`
(`Iface/W0Value.lean`, the lane's words and statistics from its trace before the store). -/
theorem w0_pstore_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) {j : Nat} (hj : j < 4) (hpc : e.pc = 704 + j)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    ∀ a bs, e.kind = .wr a bs → ∃ q < 4, a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 / 2) + 512 * (tidOf L g / 32 % 2) +
        16 * (tidOf L g % 32) + 1024 * j + 4 * q) ∧ bs = (Assumptions.bf16Pair
      (w0PWord P.scale ((X.tr g).take k) (2 * (4 * j + q)))
      (w0PWord P.scale ((X.tr g).take k) (2 * (4 * j + q) + 1))).toBytes := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  have hx := w0_scale_rd hp
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ := followW hp hX hFw hw he hub hx hv k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  obtain ⟨n0, hctl⟩ : ∃ n' : Cls → Nat, Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg0, d.c⟩, n')) := ⟨n, control_of_data hst⟩
  obtain ⟨hIW, hOk, hCar, hVote, -⟩ := hI d rfl
  have hsite : d.c.site = .ost ⟨j, hj⟩ := site_pc_ost hj (hpc'.symm.trans hpc)
  have hok : d.ok = true := hOk (by rw [hsite]; rfl)
  obtain ⟨hm, hl, hmx, -⟩ := hCar hok (by rw [hsite]; rfl)
  obtain ⟨f578, hf578, hp578⟩ := hVote hok (by rw [hsite]; rfl)
  have hw0 := hv.now.2 ⟨f578, hf578, hp578⟩
  have hb : BlkIs d.b (w0Words (w0Fin ((X.tr g).take k)).2) := by
    rw [w0Fin_snd]
    exact ⟨hIW.hi, hIW.mw, hIW.pw, hIW.pm, hIW.vt⟩
  obtain ⟨-, -, hwords, -⟩ := w0_block hw0 hx hb hm hl hmx
  obtain ⟨-, hsub, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L d) at hF
  have hF' := ((holds_append _ _ _).mp hF).2
  have hel : d.c.el < 4 := by
    have h1 : d.c.el < Control.elems d.c.site := hinv
    rw [hsite] at h1
    simpa [Control.elems] using h1
  have hdF : dF L d = f_ost (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm
      d.b.vt := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hsite]
    rfl
  rw [hdF] at hF'
  unfold f_ost at hF'
  have hF'' := ((holds_append _ _ _).mp hF').1
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b', w', hb'⟩, hk', hsem', hsrc', hw'⟩ :=
    pstore_code ⟨j, hj⟩
  change kernel.code[d.c.site.pc]? = _ at hcode
  rw [hsite, show (Site.ost ⟨j, hj⟩).pc = 704 + j from rfl, hc'] at hcode
  cases hcode
  have hmem : 1115 + 3 * (4 * j + d.c.el) ∈ (pw_facts4 (lookupD (f_join (scX L) d.b.m d.b.l
      d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4)
      (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) d.b.pm d.b.vt))).map Prod.fst := by
    simp only [pw_facts4, List.map_cons, List.map_nil]
    have hall : ∀ j < 4, ∀ q < 4, 1115 + 3 * (4 * j + q) ∈ [1115, 1118, 1121, 1124, 1127, 1130,
        1133, 1136, 1139, 1142, 1145, 1148, 1151, 1154, 1157, 1160, 2955] := by decide
    exact hall j hj _ hel
  have hreg := holds_of_mem hF'' hmem
  have hblk : lookupD (pw_facts4 (lookupD (f_join (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo
      d.b.hi d.b.mw (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
      (d.b.pw 7) d.b.pm d.b.vt))) (1115 + 3 * (4 * j + d.c.el)) =
      blkOst (scX L) d.b (1115 + 3 * (4 * j + d.c.el)) := by
    unfold blkOst f_ost
    exact (lk_head_mem hmem).symm
  rw [hblk, hwords (4 * j + d.c.el) (by omega)] at hreg
  have hbytes : (Assumptions.bf16Pair
      (w0Prob P.scale (w0Max P.scale (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1
        (w0Words (w0Fin ((X.tr g).take k)).2)) (w0Score (w0Words (w0Fin ((X.tr g).take k)).2)
        (2 * (4 * j + d.c.el))))
      (w0Prob P.scale (w0Max P.scale (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1
        (w0Words (w0Fin ((X.tr g).take k)).2)) (w0Score (w0Words (w0Fin ((X.tr g).take k)).2)
        (2 * (4 * j + d.c.el) + 1)))).bytes = a'.elem.width / 8 := by
    rw [hw']
    simp [Assumptions.bf16Pair, Value.bytes, FloatFmt.bytes]
  obtain ⟨acc, hacc⟩ := fires_st_elemBytes hr' hs' hb' hk' hsem' (by rw [hsub]; exact hsrc' _ hel)
    hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  obtain ⟨σ, hσ, hJ, hi, hev, hpc0⟩ := ev_at hp hX hFw he hub
  obtain ⟨d1, n1, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc0
    ⟨by omega, by omega⟩
  rw [hσ] at hctl
  simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    true_and] at hctl
  obtain ⟨rfl, -⟩ := hctl
  obtain ⟨-, a2, bs2, hk2, hsz2, hl2⟩ := Proof.Wg0.ost_acc hp (MemRow.wg0_tid hw) hsite hE.2 hub
  rw [hk] at hk2
  cases hk2
  exact ⟨d.c.el, hel, hsz2, hl2, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
