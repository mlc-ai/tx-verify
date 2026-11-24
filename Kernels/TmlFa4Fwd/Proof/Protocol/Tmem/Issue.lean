-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
public import Core.Tc.TcMmaSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Lib.SmemElements

@[expose] public section

/-! # The MMA issues' shape and shared operands

* `mma_spec`: the operands of every MMA: the Q stage and the K slot of ring use `2 u` (QK), the V
  slot of ring use `2 u + 1` (PV), as descriptors.
* `qk_bytes`, `pv_bytes`: every shared operand byte lies in the 32768 bytes of that stage or slot.
* `issueShape`: every MMA has Core's issue shape.
* `collectorSafe`: no MMA names a collector. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The operands of a QK MMA.** -/
theorem Qk.spec_eq {g k st u : Nat} {j : Fin 8} (h : Qk L X g k st u j) {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d s acc mask) :
    d = 128 * st ∧ mask = [0, 0, 0, 0] ∧ acc = (j.val != 0) ∧
      s = ⟨qkDsc, qkA L st j, qkB L (2 * u % 3) j, g / L.block, g / L.block, none, {}⟩ := by
  obtain ⟨ha, hb⟩ := h.descs hi
  obtain ⟨pc, da, db, he⟩ := h.issue
  obtain ⟨pc', he'⟩ := hi
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
  simp only at ha hb
  exact ⟨rfl, rfl, rfl, by rw [ha, hb]⟩

/-- **The operands of a PV MMA.** -/
theorem Pv.spec_eq {g k st u : Nat} {j : Fin 8} (h : Pv L X g k st u j) {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d s acc mask) :
    d = 256 + 128 * st ∧ mask = [0, 0, 0, 0] ∧ acc = (j.val != 0 || u != 0) ∧
      s = ⟨pvDsc, pvB L ((2 * u + 1) % 3) j, pvB L ((2 * u + 1) % 3) j, g / L.block, g / L.block,
        some (128 * st + 64 + 8 * j.val), {}⟩ := by
  have hb := h.descs hi
  obtain ⟨pc, db, he⟩ := h.issue
  obtain ⟨pc', he'⟩ := hi
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he'
  simp only at hb
  exact ⟨rfl, rfl, rfl, by rw [hb]⟩

/-- **The shared bytes of a QK MMA's operands.** -/
theorem Qk.bytes (hp : Pre p L m) {g k st u : Nat} {j : Fin 8} (h : Qk L X g k st u j) {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d s acc mask)
    {index : Nat} (hx : index < 4096) :
    (∃ off, off < 32768 ∧ s.byteLoc .a index =
      some ⟨.shared, g / L.block, L.sharedBase + 3072 + 32768 * st + off⟩) ∧
    ∃ off, off < 32768 ∧ s.byteLoc .b index =
      some ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (2 * u % 3) + off⟩ := by
  obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi
  have hs := hp.shared.1
  have hj := j.isLt
  constructor
  · obtain ⟨off, ho, e⟩ := qk_a_byteLoc (s := ⟨qkDsc, qkA L st j, qkB L (2 * u % 3) j, g / L.block,
      g / L.block, none, {}⟩) rfl rfl rfl (base := L.sharedBase + 3072 + 32768 * st +
      16384 * (j.val / 4)) (j := j.val % 4) rfl (by omega) (by omega) hx
    refine ⟨16384 * (j.val / 4) + off, by omega, ?_⟩
    rw [e, Nat.add_assoc]
  · obtain ⟨off, ho, e⟩ := qk_b_byteLoc (s := ⟨qkDsc, qkA L st j, qkB L (2 * u % 3) j, g / L.block,
      g / L.block, none, {}⟩) rfl rfl (base := L.sharedBase + 68608 + 32768 * (2 * u % 3) +
      16384 * (j.val / 4)) (j := j.val % 4) rfl (by omega) (by omega) hx
    refine ⟨16384 * (j.val / 4) + off, by omega, ?_⟩
    rw [e, Nat.add_assoc]

/-- **The shared bytes of a PV MMA's B operand.** -/
theorem Pv.bytes (hp : Pre p L m) {g k st u : Nat} {j : Fin 8} (h : Pv L X g k st u j) {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d s acc mask)
    {index : Nat} (hx : index < 4096) :
    s.byteLoc .a index = none ∧
    ∃ off, off < 32768 ∧ s.byteLoc .b index =
      some ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * ((2 * u + 1) % 3) + off⟩ := by
  obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi
  have hs := hp.shared.1
  refine ⟨?_, pv_b_byteLoc (s := ⟨pvDsc, pvB L ((2 * u + 1) % 3) j, pvB L ((2 * u + 1) % 3) j,
    g / L.block, g / L.block, some (128 * st + 64 + 8 * j.val), {}⟩) rfl rfl
    (base := L.sharedBase + 68608 + 32768 * ((2 * u + 1) % 3)) (j := j.val) rfl j.isLt (by omega)
    hx⟩
  unfold OperandSpec.byteLoc
  simp only [Option.isSome_some, and_self, ↓reduceIte, ite_self]

theorem kDesc_encoded {a : Nat} (h : a < 2 ^ 18) (h16 : a % 16 = 0) : SharedEncoded (kDesc a) :=
  ⟨h, (by decide : (16 : Nat) < 2 ^ 18), (by decide : (1024 : Nat) < 2 ^ 18), h16, by simp [kDesc],
      by simp [kDesc]⟩

theorem mnDesc_encoded {a : Nat} (h : a < 2 ^ 18) (h16 : a % 16 = 0) : SharedEncoded (mnDesc a) :=
  ⟨h, (by decide : (16384 : Nat) < 2 ^ 18), (by decide : (1024 : Nat) < 2 ^ 18), h16, by simp
      [mnDesc], by simp [mnDesc]⟩

/-- **Every MMA has the issue shape.** -/
theorem issueShape (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) : IssueShape L i d s mask := by
  have hm := mma_matches hX hi
  obtain ⟨hw, st, u, j, hst, h⟩ := mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
  have hg : i.1 < L.threads := by
    obtain ⟨pc, he⟩ := hi
    exact Frame.lt_of_get hX (k := i.2) he
  have hsh := hp.shared
  have hj := j.isLt
  have hn : ∀ x, x % 3 < 3 := fun x => Nat.mod_lt _ (by decide)
  rcases h with h | h
  · have hb := fun index hx => h.bytes hp (index := index) hi hx
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h.spec_eq hi
    have hn2 := hn (2 * u)
    have hspec : Spec128 ⟨qkDsc, qkA L st j, qkB L (2 * u % 3) j, i.1 / L.block, i.1 / L.block,
        none, {}⟩ (i.1 / L.block) := ⟨.inl rfl, rfl, rfl⟩
    refine ⟨hg, qkDsc_valid, (by decide : OutputMaskValid .one [0, 0, 0, 0]), hm, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
    · exact kDesc_encoded (by omega) (by omega)
    · exact kDesc_encoded (by omega) (by omega)
    · exact .inl (by omega)
    · intro a ha; cases ha
    · show 128 * st % 2 ^ 16 + 128 ≤ 512
      omega
    · intro op index hx
      have hx' : index < 4096 := by rw [opBytes hspec] at hx; exact hx
      obtain ⟨⟨o1, -, e1⟩, o2, -, e2⟩ := hb index hx'
      cases op
      · exact .inl ⟨_, e1⟩
      · exact .inl ⟨_, e2⟩
  · have hb := fun index hx => h.bytes hp (index := index) hi hx
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h.spec_eq hi
    have hn2 := hn (2 * u + 1)
    have hspec : Spec128 ⟨pvDsc, pvB L ((2 * u + 1) % 3) j, pvB L ((2 * u + 1) % 3) j,
        i.1 / L.block, i.1 / L.block, some (128 * st + 64 + 8 * j.val), {}⟩ (i.1 / L.block) :=
      ⟨.inr rfl, rfl, rfl⟩
    refine ⟨hg, pvDsc_valid, (by decide : OutputMaskValid .one [0, 0, 0, 0]), hm, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
    · exact mnDesc_encoded (by omega) (by omega)
    · exact mnDesc_encoded (by omega) (by omega)
    · exact .inl (by omega)
    · intro a _ hh
      have : halfDatapath pvDsc = true := hh
      exact absurd this (by decide)
    · show (256 + 128 * st) % 2 ^ 16 + 128 ≤ 512
      omega
    · intro op index hx
      have hx' : index < 4096 := by rw [opBytes hspec] at hx; exact hx
      obtain ⟨-, o2, -, e2⟩ := hb index hx'
      cases op
      · refine .inr ⟨rfl, ?_⟩
        unfold aCell
        simp only [Option.bind_some]
        rw [ite_eq_left]
        · exact ⟨_, rfl⟩
        · refine ⟨pvDsc_valid, ?_, ?_, .inl ⟨rfl, by omega⟩⟩
          · show index / 32 < 128
            omega
          · show (128 * st + 64 + 8 * j.val) % 2 ^ 16 + 8 ≤ 512
            omega
      · exact .inl ⟨_, e2⟩

/-- **No MMA reuses a collector.** -/
theorem collectorSafe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : CollectorSafe X :=
  collectorSafe_of_noReuse fun i d s acc mask hi => by
    obtain ⟨hw, st, u, j, hst, h⟩ := mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
    rcases h with h | h
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi
      exact ⟨rfl, rfl⟩
    · obtain ⟨-, -, -, rfl⟩ := h.spec_eq hi
      exact ⟨rfl, rfl⟩

/-- **No MMA instruction is unsafe**, given the values of the completed MMAs. -/
theorem instruction_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      CompletedValues L Assumptions.all X i) : ¬ InstructionUnsafe L Assumptions.all X := fun hn =>
  hn ⟨fun _ _ _ _ _ hi => ⟨issueShape hp hX hFw hi, hV _ _ _ _ _ hi⟩,
    fun _ _ hcp => absurd hcp ((scoreFacts hp hX hFw).no_cp _ _), collectorSafe hp hX hFw⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
