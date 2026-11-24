-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
public import Lemmas.Tensor.LoadWritten
import Lemmas.Tensor.TensorCompleteConsistentRead
import Lemmas.Tensor.TensorReadSources
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bytes a Q or Bias copy writes

Element `(x, y)` of a copy's box is the launch's value at the box's origin plus `(x, y)`
(`inputVal`: the BF16 value of Q, the packed Bias entry, or the descriptor's zero outside the
tensor). A notified copy has written both bytes of every element (`input_written`), and every write
of a copy is one of them (`input_wrote`), when the input arrays are not written
(`InputsUnwritten`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow TensorDescriptor

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- No write covers a byte of an input array. -/
def InputsUnwritten (p : Params) (X : Execution) : Prop :=
  ∀ r ∈ p.inputRegions, ∀ l, r.Contains l → ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l

/-- The input arrays are not written when the input assumption's undefined behaviour is excluded. -/
theorem inputsUnwritten (hp : Pre p L m) (h : ¬ Assumptions.inputReadOnly.ub L m X) :
    InputsUnwritten p X :=
  fun r hr l hl w a _ hw hc => h ⟨w, a, l, hw.intent, hc, p, hp, r, hr, hl⟩

/-- A packed rank-three array: column, row, head. -/
def packed (base cols rows heads : Nat) : TensorAddress.Geometry 3 :=
  ⟨base, 2, ![cols, rows, heads], ![2, 2 * cols * heads, 2 * cols]⟩

/-- A coordinate inside a packed array. -/
def Inside (cols rows heads : Nat) (c : Fin 3 → Int) : Prop :=
  (0 ≤ c 0 ∧ c 0 < cols) ∧ (0 ≤ c 1 ∧ c 1 < rows) ∧ 0 ≤ c 2 ∧ c 2 < heads

open Classical in
theorem packed_lookup (base cols rows heads : Nat) (c : Fin 3 → Int) {k : Nat} (hk : k < 2) :
    TensorAddress.lookup (packed base cols rows heads) c k =
      if Inside cols rows heads c then
        some (base + 2 * (((c 1).toNat * heads + (c 2).toNat) * cols + (c 0).toNat) + k)
      else none := by
  have hb : (∀ axis, 0 ≤ c axis ∧ c axis < ((packed base cols rows heads).extent axis : Int)) ↔
      Inside cols rows heads c := by
    constructor
    · intro h
      exact ⟨by simpa [packed] using h 0, by simpa [packed] using h 1, by simpa [packed] using h 2⟩
    · rintro ⟨h0, h1, h2⟩ axis
      fin_cases axis
      · simpa [packed] using h0
      · simpa [packed] using h1
      · simpa [packed] using h2
  have ha : TensorAddress.byteAddress (packed base cols rows heads) c k =
      base + 2 * (((c 1).toNat * heads + (c 2).toNat) * cols + (c 0).toNat) + k := by
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_three]
    change base + ((c 0).toNat * 2 + (c 1).toNat * (2 * cols * heads) +
      (c 2).toNat * (2 * cols)) + k = _
    ring
  unfold TensorAddress.lookup
  rw [ha]
  by_cases h : Inside cols rows heads c
  · rw [ite_eq_left ⟨hb.mpr h, hk⟩, ite_eq_left h]
  · rw [ite_eq_right (fun ht => h (hb.mp ht.1)), ite_eq_right h]

open Classical in
/-- **The value of an input element** at a tensor coordinate. -/
def inputVal (p : Params) (bias : Bool) (c : Fin 3 → Int) : Option ℝ :=
  if bias then
    if Inside 1280 (p.totalQ + 128) p.heads c then p.bias (c 1).toNat (c 2).toNat (c 0).toNat
    else some 0
  else if Inside 128 p.totalQ p.heads c then some (p.q (c 1).toNat (c 2).toNat (c 0).toNat)
  else some 0

/-- The tensor coordinate of element `(x, y)` of a box at `org`. -/
def boxCoord (org : Fin 3 → Int) (x y : Nat) : Fin 3 → Int := ![org 0 + x, org 1 + y, org 2]

private theorem coord_box {b : TensorTile.Box 3} (hbox : b = ⟨![64, 128, 1], ![1, 1, 1]⟩)
    (org : Fin 3 → Int) {x y : Nat} (hy : y < 128) :
    TensorTile.coord b org (TensorTile.indexOf b x y) = boxCoord org x y := by
  subst hbox
  have hd : y / 128 = 0 := Nat.div_eq_of_lt hy
  funext axis
  fin_cases axis <;>
    simp [TensorTile.coord, TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
      TensorTile.step, boxCoord, Nat.mod_eq_of_lt hy, hd] <;> rfl

private theorem coord_eq {d : Descriptor 2} (hbox : d.box = ⟨![64, 128, 1], ![1, 1, 1]⟩)
    (org : Fin 3 → Int) (slot : TensorTransfer.Slot d) :
    TensorTransfer.coord d org none slot = boxCoord org slot.1.val slot.2.1.val := by
  have hy : slot.2.1.val < 128 := by
    simpa [hbox, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
      using slot.2.1.isLt
  exact coord_box hbox org hy

private theorem biasValue_bytes (o : Option ℝ) : (biasValue o).bytes = 2 := by
  cases o <;> rfl

private theorem contains {base cols rows heads : Nat} {c : Fin 3 → Int} {k : Nat}
    (hk : k < 2) (hin : Inside cols rows heads c) :
    Region.Contains ⟨base, 2 * cols * heads * rows⟩
      ((globalLoc (base + 2 * (((c 1).toNat * heads + (c 2).toNat) * cols +
        (c 0).toNat))).at k) := by
  obtain ⟨h0, h1, h2⟩ := hin
  have hr : (c 1).toNat < rows := by omega
  have hh : (c 2).toNat < heads := by omega
  have hc : (c 0).toNat < cols := by omega
  generalize (c 1).toNat = row at hr ⊢
  generalize (c 2).toNat = head at hh ⊢
  generalize (c 0).toNat = col at hc ⊢
  have hrow := Nat.mul_le_mul_right heads (show row + 1 ≤ rows by omega)
  rw [Nat.add_mul, Nat.one_mul] at hrow
  have hcol := Nat.mul_le_mul_right cols
    (show row * heads + head + 1 ≤ rows * heads by omega)
  rw [Nat.add_mul, Nat.one_mul] at hcol
  have e : 2 * cols * heads * rows = 2 * (rows * heads * cols) := by ring
  rw [e]
  exact ⟨rfl, rfl, by simp only [globalLoc, Loc.at]; omega,
    by simp only [globalLoc, Loc.at]; omega⟩

/-- **The source of an input byte**: an unwritten launch byte holding the element's value, or the
descriptor's zero. -/
theorem input_source (hp : Pre p L m) (hIn : InputsUnwritten p X) {j : Fin 14}
    {org : Fin 3 → Int} (slot : TensorTransfer.Slot (Loader.inputMap p (Loader.inputSite j))) :
    (∃ a, TensorTransfer.globalAddress (Loader.inputMap p (Loader.inputSite j)) org none slot =
        some a ∧
      m (globalLoc a) = some (some ((biasValue (inputVal p (Loader.inputSite j).bias
        (boxCoord org slot.1.val slot.2.1.val))).byteAt slot.2.2.val)) ∧
      ∀ w a' bs, X.MemWrites w a' bs → ¬ a'.Covers (globalLoc a)) ∨
    (TensorTransfer.globalAddress (Loader.inputMap p (Loader.inputSite j)) org none slot = none ∧
      inputVal p (Loader.inputSite j).bias (boxCoord org slot.1.val slot.2.1.val) = some 0) := by
  classical
  have hk : slot.2.2.val < 2 := by
    have h1 := slot.2.2.isLt
    have h2 : (Loader.inputMap p (Loader.inputSite j)).format.bytes = 2 := by
      rw [(input_map p j).2.2.1]; rfl
    omega
  have hbox : (Loader.inputMap p (Loader.inputSite j)).box = ⟨![64, 128, 1], ![1, 1, 1]⟩ := by
    unfold Loader.inputMap; split <;> rfl
  unfold TensorTransfer.globalAddress
  rw [coord_eq hbox]
  generalize boxCoord org slot.1.val slot.2.1.val = c
  generalize slot.2.2.val = k at hk ⊢
  clear hbox
  clear slot
  cases hb : (Loader.inputSite j).bias
  · have hg : geometry (Loader.inputMap p (Loader.inputSite j)) =
        packed p.qBase 128 p.totalQ p.heads := by
      simp only [Loader.inputMap, hb, Bool.false_eq_true, ↓reduceIte, Params.qMap, geometry, packed]
      congr 1
    rw [hg, packed_lookup _ _ _ _ _ hk]
    by_cases hin : Inside 128 p.totalQ p.heads c
    · rw [ite_eq_left hin]
      refine .inl ⟨_, rfl, ?_, ?_⟩
      · have := hp.qBytes (c 1).toNat (by have := hin.2.1; omega) (c 2).toNat
          (by have := hin.2.2; omega) (c 0).toNat (by have := hin.1; omega) k hk
        simpa [inputVal, hin, biasValue, Params.qLoc, globalLoc, Loc.at] using this
      · exact hIn _ (List.mem_cons_self ..) _ (by
          have := contains (base := p.qBase) hk hin
          simpa [globalLoc, Loc.at] using this)
    · rw [ite_eq_right hin]
      exact .inr ⟨rfl, by simp [inputVal, hin]⟩
  · have hg : geometry (Loader.inputMap p (Loader.inputSite j)) =
        packed p.biasBase 1280 (p.totalQ + 128) p.heads := by
      simp only [Loader.inputMap, hb, ↓reduceIte, Params.biasMap, geometry, packed]
      congr 1
    rw [hg, packed_lookup _ _ _ _ _ hk]
    by_cases hin : Inside 1280 (p.totalQ + 128) p.heads c
    · rw [ite_eq_left hin]
      refine .inl ⟨_, rfl, ?_, ?_⟩
      · have := hp.biasBytes (c 1).toNat (by have := hin.2.1; omega) (c 2).toNat
          (by have := hin.2.2; omega) (c 0).toNat (by have := hin.1; omega) k
          (by rw [biasValue_bytes]; exact hk)
        simpa [inputVal, hin, Params.biasLoc, globalLoc, Loc.at] using this
      · exact hIn _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (by
          have := contains (base := p.biasBase) hk hin
          simpa [globalLoc, Loc.at] using this)
    · rw [ite_eq_right hin]
      exact .inr ⟨rfl, by simp [inputVal, hin]⟩

private theorem zero_byte' {f : Fill} {fm : Format} (hf : f = .zero) (hfm : fm = .bf16) (k : Nat) :
    (TensorCopy.Content.filled f fm k).byte = some ((biasValue (some 0)).byteAt k) := by
  rw [hf, hfm]; rfl

private theorem zero_byte {d : Descriptor 2} (hf : d.fill = .zero) (hfm : d.format = .bf16)
    (k : Nat) : (TensorCopy.Content.filled d.fill d.format k).byte =
      some ((biasValue (some 0)).byteAt k) := by
  rw [hf, hfm]; rfl

/-- **A recorded write of a copy** writes the element's byte. -/
theorem input_wrote (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hIn : InputsUnwritten p X) {i : EvId} {o : TensorCopy.Observation} (ho : X.tensor i = some o)
    {c : Nat} {j : Fin 14} {org : Fin 3 → Int} {mb : Loc} (hs : o.spec = inputSpec p L c j org mb)
    {x y k : Nat} {b : Byte} (hw : TensorCopy.writeByte o x y k = some b) :
    b = (biasValue (inputVal p (Loader.inputSite j).bias (boxCoord org x y))).byteAt k := by
  obtain ⟨⟨addr, hIssue⟩, hok, _⟩ := hX.tensor i o ho
  obtain ⟨spec, eff⟩ := o
  simp only at hs
  subst hs
  obtain ⟨slot, hslot, hw'⟩ := Option.bind_eq_some_iff.mp (show
    (TensorTransfer.slotAt (inputSpec p L c j org mb).descriptor x y k).bind _ = some b from hw)
  obtain ⟨content, hcon, hbyte⟩ := Option.bind_eq_some_iff.mp hw'
  have hco := TensorCopy.slotAt_coordinates hslot
  rcases input_source hp hIn (org := org) slot with ⟨a, ha, hm, hun⟩ | ⟨ha, hz⟩
  · have hr : TensorCopy.readLoc (inputSpec p L c j org mb) x y k = some (globalLoc a) := by
      rw [TensorCopy.readLoc_source, hslot]
      have hga : TensorBox.globalAddress (inputSpec p L c j org mb).toTensorBox slot = some a := ha
      simp [TensorCopy.source, hga, globalLoc]
    obtain ⟨rfl, rfl, rfl⟩ := hco
    exact tensor_writeByte_of_initial hX ho hIssue hr hw hm hun
  · have hf := hok.writes slot content hcon
    have hga : TensorBox.globalAddress (inputSpec p L c j org mb).toTensorBox slot = none := ha
    simp only [TensorCopy.source, hga] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hco
    rw [hz]
    rw [hf] at hbyte
    obtain ⟨-, -, hFormat, -, hFill⟩ := input_map p j
    have := zero_byte hFill hFormat slot.2.2.val
    exact Option.some.inj (hbyte.symm.trans this)

/-- **A notified copy has written every byte of its box.** -/
theorem input_written (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hIn : InputsUnwritten p X) {i : EvId} {o : TensorCopy.Observation} (ho : X.tensor i = some o)
    (hn : o.effects.notified = true)
    {c : Nat} {j : Fin 14} {org : Fin 3 → Int} {mb : Loc} (hs : o.spec = inputSpec p L c j org mb)
    {x y k : Nat} {l : Loc} (hl : TensorCopy.writeLoc o.spec x y k = some l) :
    X.MemWrites (.async i (.write (.load x y k))) { loc := l, size := 1 }
      [(biasValue (inputVal p (Loader.inputSite j).bias (boxCoord org x y))).byteAt k] := by
  obtain ⟨⟨addr, hIssue⟩, hok, _⟩ := hX.tensor i o ho
  obtain ⟨slot, hslot, -⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨content, hcon⟩ := hok.complete hn slot
  have hwr : ∃ b, TensorCopy.writeByte o x y k = some b := by
    have hf := hok.writes slot content hcon
    unfold TensorCopy.writeByte
    rw [hslot, Option.bind_some, hcon, Option.bind_some]
    cases hsrc : TensorCopy.source o.spec slot with
    | global a =>
      rw [hsrc] at hf
      obtain ⟨b, -, rfl⟩ := hf
      exact ⟨b, rfl⟩
    | fill mode fmt kk =>
      rw [hsrc] at hf
      simp only at hf
      subst hf
      have h2 : mode = o.spec.descriptor.fill ∧ fmt = o.spec.descriptor.format ∧
          kk = slot.2.2.val := by
        unfold TensorCopy.source at hsrc
        split at hsrc
        · cases hsrc
        · cases hsrc
          exact ⟨rfl, rfl, rfl⟩
      obtain ⟨rfl, rfl, rfl⟩ := h2
      obtain ⟨-, -, hFormat, -, hFill⟩ := input_map p j
      have hfl : o.spec.descriptor.fill = .zero ∧ o.spec.descriptor.format = .bf16 := by
        rw [hs]
        exact ⟨hFill, hFormat⟩
      exact ⟨_, zero_byte' hfl.1 hfl.2 _⟩
  obtain ⟨b, hb⟩ := hwr
  rw [← input_wrote hp hX hIn ho hs hb]
  exact ⟨o, addr, b, ho, hIssue, hl, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
