-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.VoteValid
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidCore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxPeer
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PeerStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MstWord
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.HasFin
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPlace
public import Lemmas.Flow.ScalarOut

@[expose] public section

/-! # The exchange load keeps warpgroup 0's trace valid

The exchange load at pc 572 reads the word the partner's store at pc 566 wrote (`rmax_read_bytes`
with the partner's valid prefixes below the load). That store's word depends only on the block's
high words, mask word and peer pairs, which the partner's block had read (`w0_block_seen`) and
which agree with a valid block (`w0_early_agree`), so it is a number or negative infinity
(`w0_mst_word`, `SK.ni`): the word keeps the block's words valid. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The word of a store at pc 566 is a scalar number or negative infinity**, from the validity
of the lane's prefix before the store. -/
theorem w0_mst_store (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    (hw : warp L g < 4) {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hpc : e.pc = 566)
    (h : W0Valid P.scale ((X.tr g).take k)) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧ SK.ni.Has v := by
  intro a bs hk
  obtain ⟨w', hw', -, eH, eM, eP, -⟩ := w0_early_agree hp hIn hX hFw hw he
    (fun _ h => by rw [hk] at h; cases h) (Or.inl hpc) h
  have hw'' : W0Ok P.scale { w' with pw := (w0Words (w0Fin ((X.tr g).take k)).2).pw } :=
    ⟨hw'.scale, hw'.hiLen, hw'.hi, hw'.loLen, hw'.lo, hw'.mask,
      fun j hj => by simpa only [eP j hj] using hw'.peer j hj, hw'.pm⟩
  obtain ⟨v, h1, h2, h4⟩ := w0_mst_word hp hX hFw hw he hpc h hw'' eH eM (fun _ => rfl)
    a bs hk
  exact ⟨v, h1, h2, h4⟩

/-- **The exchange load reads the partner's store at pc 566** (valid rows): with the partner's
valid prefixes below the load (`hbelow`), the load at pc 572 of lane `g` returns the word `v` the
partner's store at pc 566 after `2 r + 1` barrier-9 events wrote (`r` the blocks `g` has closed
before the load), a scalar number or negative infinity. -/
theorem w0_pm_peer_read (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨572, .rd a bs⟩)
    (hw : warp L g < 4) (hbelow : W0Below P L X (w0Partner L g) g k) :
    ∃ (j : Nat) (f : Event) (a' : Acc) (ws : List Byte) (v : Value),
      X.get (w0Partner L g, j) = some f ∧ f.pc = 566 ∧ f.kind = .wr a' ws ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take k)).1.length + 1 ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) ∧
      bs = ws.map some ∧ ws = v.toBytes ∧ Scal v ∧ SK.ni.Has v ∧ rebuild 3 bs = .ok v := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, hwh, hdiv, -⟩ := w0Partner_facts hp hw hg
  have hub : ∀ u, (⟨572, .rd a bs⟩ : Event).kind ≠ .ub u := fun _ h => by cases h
  have hcnt := w0_cnt_exch hp hX hFw hw he hub (Or.inl rfl)
  have hrR := w0_len_lt hp hX hFw hw he hub (Or.inr rfl)
  have hpl : ∀ j f, X.get (w0Partner L g, j) = some f → f.pc = 1155 →
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take k)).1.length + 1 → False := by
    intro j f hf h1155 htc hcj
    have h1 := w0Fin_length_st hp hX hFw hwh hf (hbelow j f hf htc).2 (Or.inr h1155) hcj
    have h2 := w0_len_epi hp hX hFw hwh hf (hbelow j f hf htc).2 (Or.inl h1155)
    have h3 : blocksOf P L (w0Partner L g / L.block) = blocksOf P L (g / L.block) := by
      rw [hdiv]
    omega
  have hlen : ∀ j f a' ws, X.get (w0Partner L g, j) = some f → (f.pc = 566 ∨ f.pc = 1155) →
      f.kind = .wr a' ws → Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) →
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take k)).1.length + 1 → ws.length = 4 := by
    intro j f a' ws hf hfpc hk' htc hcj
    rcases hfpc with h566 | h1155
    · obtain ⟨v, h1, -, h3⟩ := w0_mst_store hp hIn hX hFw hwh hf h566
        (Wg0.W0Valid.take_le (hbelow j f hf htc).1 (Nat.le_succ j)) a' ws hk'
      rw [h1]
      simp [Value.toBytes, (SK.clean h3).1]
    · exact (hpl j f hf h1155 htc hcj).elim
  obtain ⟨j, f, a', ws, hf, hfpc, hk', hcj, htc, hbs⟩ := rmax_read_bytes hp hX hFw
    (hIn.bar hp X hX hFw) hw he (Or.inl rfl) hcnt hrR.le hbelow hlen
  have h566 : f.pc = 566 := hfpc.resolve_right fun h1155 => hpl j f hf h1155 htc hcj
  obtain ⟨v, hv1, hv2, hv3⟩ := w0_mst_store hp hIn hX hFw hwh hf h566
    (Wg0.W0Valid.take_le (hbelow j f hf htc).1 (Nat.le_succ j)) a' ws hk'
  refine ⟨j, f, a', ws, v, hf, h566, hk', hcj, htc, hbs, hv1, hv2, hv3, ?_⟩
  rw [hbs, hv1]
  exact rebuild_of_scal (by rw [(SK.clean hv3).1]; omega) hv2

/-- **The word of the exchange load** (valid rows): a clean finite number or negative infinity. -/
theorem w0_pay_pm (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨572, .rd a bs⟩)
    (hw : warp L g < 4) (hbelow : W0Below P L X (w0Partner L g) g k) :
    ∃ v, rebuild 3 bs = .ok v ∧ PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf) := by
  obtain ⟨j, f, a', ws, v, -, -, -, -, -, -, -, -, hv3, hrb⟩ :=
    w0_pm_peer_read hp hIn hX hFw he hw hbelow
  exact ⟨v, hrb, SK.clean hv3, (w0Ok_pm_of_has hv3).2⟩

/-- **The exchange load keeps the trace valid**: the new exchange word differs from the default. -/
theorem w0Valid_snoc_pm (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {k : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨572, .rd a bs⟩)
    (hw : warp L g < 4) (hbelow : W0Below P L X (w0Partner L g) g k)
    (h : W0Valid P.scale ((X.tr g).take k)) :
    W0Valid P.scale ((X.tr g).take (k + 1)) ∧
      (w0Words (w0Fin ((X.tr g).take (k + 1))).2).pm ≠ .pred false := by
  obtain ⟨hb, -, -⟩ := w0_boundSeen hp hX hFw hw he (fun f hf => by cases hf)
    (by show 103 ≤ 572; omega) h
  rw [trace_take_succ he]
  exact w0Core_pm hp.scalePos rfl rfl hb (w0_pay_pm hp hIn hX hFw he hw hbelow) h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
