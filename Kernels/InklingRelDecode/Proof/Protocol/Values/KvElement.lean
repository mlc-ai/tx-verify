-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvRead
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvByte
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvBlock
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Lemmas.Tcgen05.MmaBytePair
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The B elements of an MMA are numbers

The two bytes of element `(row, k)` of the B operand of a QK or PV MMA are adjacent bytes of one
ring slot, written by one copy of the use (`ring_copy_exists`, `ring_byte`) at the two slots of
one element of the cache (`copy_pair`, `copy_write_byte`), so they are the two bytes of a bf16
number. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The bf16 element of the cache an MMA reads as the B element at `(x, y)` of the box of half `hh`
of the K (`isV = 0`) or V tile of the slab `h` of block `n` of the CTA `c`. -/
noncomputable abbrev kvElem (Q : Params) (L : Launch) (c n isV h hh x y : Nat) : ℝ :=
  Q.kv (Q.page ((L.ctaidOf c).get .z) (2 * (Q.splits * n + (L.ctaidOf c).get .x) + h) *
      Q.pageRows + (L.ctaidOf c).get .y * Q.headRows + y)
    ((L.ctaidOf c).get .y * Q.headCols + (128 * isV + 64 * hh + x))

/-- **Every B element of a completed MMA is the cache element of the copy that wrote it**: the
copy of block `n` of its slot's use, the box byte at `(x, y)` of the element's location. -/
theorem kv_b_fact (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) {row kk : Nat} (hrow : row < 128)
    (hk : kk < 16) :
    ∃ c, ∃ σ : Fin 3, ∃ n isV h hh x y l0, c < L.grid ∧ g = KV.leader L X c 7 ∧
      s.byteLoc .b (2 * (row * 16 + kk)) = some l0 ∧ l0.cta = c ∧ Iface.InSlot L σ.val l0.addr ∧
      n % 3 = σ.val ∧ n / 3 = SingleTmaRing.readUse X ((KV.decl Q L X c).slot σ) (g, k) ∧
      isV ≤ 1 ∧ h ≤ 1 ∧ hh ≤ 1 ∧ x < 64 ∧ y < 64 ∧
      (∃ bar, TensorCopy.writeLoc (Lib.kvCopySpec Q c
        ((L.ctaidOf c).get .y * Q.headCols + 128 * isV + 64 * hh)
        (Q.page ((L.ctaidOf c).get .z) (2 * (Q.splits * n + (L.ctaidOf c).get .x) + h) *
          Q.pageRows + (L.ctaidOf c).get .y * Q.headRows)
        (L.sharedBase + 32768 * σ.val + 16384 * hh + 98304 * isV + 8192 * h) bar) x y 0 =
        some l0) ∧
      Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row kk =
        .ok (kvElem Q L c n isV h hh x y) := by
  obtain ⟨-, -, -, -, hEa, hEb, -, -, -, hloc⟩ := Mma.Export.issue_shape hp hX hf base he
  obtain ⟨-, -, -, b, hd⟩ := Mma.Export.columns hp hX hf base he
  have hw : s.descriptor.kind.width = 2 ∧ s.descriptor.kind = .f16 .bf16 .f32 ∧
      TcMma.Operand.bytes .b s.descriptor = 4096 := by
    rcases hd with ⟨j, -, -, -, hd⟩ | ⟨j, -, -, -, hd⟩ <;> rw [hd] <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hw2, -, hbytes⟩ := hw
  have hl0 : ∃ l0, s.byteLoc .b (2 * (row * 16 + kk)) = some l0 := by
    rcases hloc .b (2 * (row * 16 + kk)) (by omega) with h | ⟨h, -⟩
    · exact h
    · cases h
  obtain ⟨l0, hl0⟩ := hl0
  have hl1 : s.byteLoc .b (2 * (row * 16 + kk) + 1) = some ⟨l0.space, l0.cta, l0.addr + 1⟩ := by
    rw [TcMma.OperandSpec.byteLoc_pair s .b _ hw2 hEa hEb, hl0]
    rfl
  have even := TcMma.OperandSpec.byteLoc_even s .b _ hw2 hEa hEb hl0
  obtain ⟨c, σ, hcg, hg, hbyte, hpoll⟩ := read_ctx hp hX hf rows words he
  obtain ⟨hc0, hs0⟩ := hbyte _ _ hl0
  obtain ⟨hc1, hs1⟩ := hbyte _ _ hl1
  subst hg
  obtain ⟨gl, kl, pcl, a, sp, o, x, y, z, -, -, -, -, -, -, -, hcp, ho, hos, hn, hwl,
    hu', hmb, -, -, -, -, -, -, -⟩ :=
    ring_copy_exists hp hX hf rows init words hu form hcg
    (TcMma.OperandSpec.byteLoc_shared hl0) hc0 hs0 hpoll
  have hgl : gl / L.block = c :=
    KV.use_cta (r := .ready) (s := σ) rows (Frame.lt_of_get hX hcp) hcp hmb
  obtain ⟨n, isV, h, hh, hn3, hcu, hV, hH, hhh, hsl, hspec⟩ :=
    copy_block hp hX hf rows init hcp (by rw [hgl]; exact hmb)
  rw [hgl] at hspec hsl hcu
  obtain ⟨-, hy, hz⟩ := Lib.coordinate_bounds hp (Frame.lt_of_get hX hcp)
  rw [hgl] at hy hz
  have al := hp.sharedAlignment
  have hwl' := hwl
  rw [hspec] at hwl'
  obtain ⟨rfl, hw1⟩ := copy_pair Q c _ _ _ sp.mbar (by omega) hwl' even
  have bnd : x < 64 ∧ y < 64 := by
    have := TensorCopy.writeLoc_bounds hwl'
    simp [Lib.kvCopySpec, mapKv, TensorTile.count, TensorTile.step, TensorTile.rows,
      TensorTile.rowsOf] at this
    exact ⟨this.1, this.2.1⟩
  have hi : X.TensorIssue (gl, kl) a o.spec := ⟨pcl, by rw [hos]; exact hcp⟩
  have byte : ∀ z', z' < 2 → TensorCopy.writeByte o x y z' = some ((Value.float .bf16
      (kvElem Q L c n isV h hh x y)).byteAt z') := fun z' hz' =>
    copy_write_byte hp hX nub hz hsl hy hV hhh ho hi (hos ▸ hspec) hn bnd.1 bnd.2 hz'
  have hw1' : TensorCopy.writeLoc sp x y 1 = some ⟨l0.space, l0.cta, l0.addr + 1⟩ := by
    rw [hspec]
    exact hw1
  have b0 := ring_byte hp hX hf rows init words hu he hops hl0 hc0 hs0 hcp ho hos hwl
    (byte 0 (by omega)) hu'
  have b1 := ring_byte hp hX hf rows init words hu he hops hl1 hc1 hs1 hcp ho hos hw1'
    (byte 1 (by omega)) hu'
  refine ⟨c, σ, n, isV, h, hh, x, y, l0, hcg, rfl, hl0, hc0, hs0, hn3, hcu.symm.trans hu', hV, hH,
    hhh, bnd.1, bnd.2, ⟨sp.mbar, hwl'⟩, TcMma.element_of_bytes (Or.inr rfl) (fun z' hz' => ?_)⟩
  interval_cases z'
  · simpa using b0
  · exact b1

/-- **Every B element of a completed MMA is a number.** -/
theorem kv_element (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) {row kk : Nat} (hrow : row < 128)
    (hk : kk < 16) :
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row kk = .ok y := by
  obtain ⟨_, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    kv_b_fact hp hX hf rows init words hu nub form base he hops hrow hk
  exact ⟨_, h⟩

/-- **The B elements field of `Elements`**: every completed MMA's B elements are numbers. -/
theorem elements_b (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {i d s acc mask ops row k} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hrow : row < 128) (hk : k < 16) :
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok y := by
  obtain ⟨g, k'⟩ := i
  obtain ⟨pc, he⟩ := hi
  exact kv_element hp hX hf rows init words hu nub form base he hops hrow hk

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
