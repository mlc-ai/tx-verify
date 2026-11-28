-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsSource
public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkSum
public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkResults
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkA
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvB
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSum
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvElems
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoSource
import Kernels.InklingRelDecode.Proof.Protocol.Values.PvVals
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdoReal

@[expose] public section

/-! # The word a score load returns is the sum of the products of its block

The word of the score load of round `r` is the `ResReal` of step 7 of block `r` (`ld_s_source`,
`result_real`), which is the sum over the eight steps of the block of the sixteen products of the
step (`qk_sum`), at the one position of the cell. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load's word as a sum over the steps of a block.** `a` and `b` are the reals of the
operand elements of the QK issues. -/
public theorem ld_s_real (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    {a b : EvId → Nat → Nat → ℝ}
    (Ea : ∀ {i d s acc mask ops row k}, QkIssue X i → X.MmaIssue i d s acc mask →
      X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 64 → k < 16 →
      Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok (a i row k))
    (Eb : ∀ {i d s acc mask ops row k}, QkIssue X i → X.MmaIssue i d s acc mask →
      X.async.mmaDone i = true → X.async.mmaOperands i = some ops → row < 128 → k < 16 →
      Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok (b i row k))
    {t k0 ta vals sh j r} (he : X.get (t, k0) = some ⟨1265, .tc (.ld ta vals sh)⟩)
    (hj : j < vals.length) (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1) :
    ∃ (g : Nat) (ks : Nat → Nat) (row col : Nat), g / L.block = t / L.block ∧
      QkAt X g (ks 7) 7 ∧ pollRound 2462 ((X.tr g).take (ks 7)) = r + 1 ∧
      (∀ i : Fin 8, QkAt X g (ks i.val) i ∧ pollRound 2462 ((X.tr g).take (ks i.val)) = r + 1 ∧
        ∃ d s acc mask, X.MmaIssue (g, ks i.val) d s acc mask ∧
          writeCell s d mask row col = some (tcDataCell L t sh ta j)) ∧
      vals[j]? = some (.float .f32 (∑ i ∈ Finset.range 8, ∑ kk ∈ Finset.range 16,
        a (g, ks i) row kk * b (g, ks i) col kk)) := by
  obtain ⟨src, r0, hrs, hres, hdone, hv⟩ := ld_s_result hp hX hf hu safe base rows init hG hws
    ht hmd words nub form he hj
  obtain ⟨g, k7, rfl, hg, hq, hr⟩ := ld_s_source hp hX hf hu safe base rows init hG he hj s1 hrs
    (result_cell hres)
  obtain ⟨d, s, acc, mask, e7⟩ := id hq
  have E : ElementVals (QkIssue X) L X a b (fun _ _ => 0) (fun _ _ => True) :=
    { b := fun hd hi hdn ho hr' hk => Eb hd hi hdn ho hr' hk
      a := fun hd _ hi hdn ho hr' hk => Ea hd hi hdn ho hr' hk
      store := fun {i src cell old} hd hrd hs' hv' =>
        absurd (store_cell hv')
          (fun hc => qk_nostore hp hX hf hu safe base rows init hG hd hrd hs' hc) }
  have hqi : QkIssue X (g, k7) := ⟨_, d, s, acc, mask, e7, 7, rfl⟩
  obtain ⟨r1, hr1, rr⟩ := result_real hp hX hf base hG E
    (CellOk := fun _ => True) (fun _ _ _ _ => trivial) (qk_closed hp hX hf base) hres hqi hdone
    trivial
  obtain ⟨ks, hks, row, col, facts, hsum⟩ := qk_sum hp hX hf hu safe base rows init hG
    (a := a) (b := b) (sv := fun _ _ => 0) 7 (j := 7) rfl hq rr
  have f7 := facts 7 (by decide)
  refine ⟨g, ks, row, col, hg, ?_, ?_, fun i => ?_, ?_⟩
  · exact f7.1
  · have hk7 : ks 7 = k7 := hks
    rw [hk7]
    exact hr
  · have hi : i.val ≤ 7 := by have := i.isLt; omega
    have hk7 : ks 7 = k7 := hks
    exact ⟨(facts i hi).1, by rw [(facts i hi).2.1]; exact hr, (facts i hi).2.2⟩
  · rw [hv, show r0 = r1 from (Value.float.inj hr1).2, hsum]
    rfl
