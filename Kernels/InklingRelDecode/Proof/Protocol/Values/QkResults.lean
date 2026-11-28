-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.Results
public import Kernels.InklingRelDecode.Proof.Iface.KvCopyForm
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryTile
import Kernels.InklingRelDecode.Proof.Protocol.Values.StoreElement
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns

@[expose] public section

/-! # The results of the QK MMAs are numbers

The QK MMAs read the query tile and the K tile, and accumulate onto an earlier QK MMA's result:
the rescale store and the probability store are never the source of their accumulator (the cells
they write are the O columns, and the probability store is excluded by the order of the rounds).
So the induction of `results` over the QK MMAs alone needs neither the probability words nor the
rescale words. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- The issues of the QK MMAs. -/
def QkIssue (X : Execution) (i : EvId) : Prop :=
  ∃ pc d s acc mask, X.get i = some ⟨pc, .tc (.mma d s acc mask)⟩ ∧ ∃ j : Fin 8, pc = Lib.qkIssue j

private theorem qk_ne_pv : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by decide +kernel

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A QK MMA's accumulator is never read from a store.** -/
theorem qk_nostore (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) {i src : EvId} {cell : Cell} (hd : QkIssue X i)
    (hrd : X.MmaReadCell i cell) (hs : ReadSource L X .acc src i cell)
    (hst : StoreCell L X src cell) : False := by
  obtain ⟨a, vals, sh, j, ⟨pc, hst⟩, hlen, hc⟩ := hst
  have hmc := mma_read_write hp hX hf base hrd
  obtain ⟨pc1, d1, s1, acc1, mask1, he1, -, lo, hi1, -, -, kind⟩ :=
    mma_write_cell hp hX hf base hmc
  obtain ⟨pc', d', s', a', m', he', j', hpc'⟩ := hd
  have hpc : pc' = pc1 := (Event.mk.inj (Option.some.inj (he'.symm.trans he1))).1
  rcases kind with ⟨jq, -, hd1, -⟩ | ⟨jp, hpcj, -⟩
  swap
  · exact qk_ne_pv _ _ (hpc'.symm.trans (hpc.trans hpcj))
  obtain ⟨-, -, h1 | h2⟩ := st_write_cell hp hX hf base (x := src) (cell := cell)
    ⟨a, vals, sh, j, ⟨pc, hst⟩, hlen, hc⟩
  · obtain ⟨a', vals', ba, w, j', g1, ha, hba, hj', hc'⟩ := h1
    exact pst_not_acc_source hp hX hf hu hG safe base rows init hrd hs g1
      ⟨ba, w, j', hba, ha, hj', hc'⟩
  · obtain ⟨a', vals', w, j', g2, ha, hj', hc'⟩ := h2
    have := (o_cols (L := L) (g := src.1) (w := w) hj').1
    rw [← ha, ← hc'] at this
    have hc2 := hc
    rw [hc'] at hc2
    omega

/-- **The elements of the QK MMAs** are numbers, and their accumulator is never a store word. -/
theorem qk_elements (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X) :
    Elements (QkIssue X) L X := by
  refine
    { b := fun _ hi _ hops hrow hk => elements_b hp hX hf rows init words hu nub form base hi hops
        hrow hk
      q := fun _ hi hat _ hops hrow hk => elements_q hp hX hf (query_tile hp hX hf words) base hi
        hat hops hrow hk
      p := fun hd hi hat _ _ _ _ => ?_
      store := fun {i src cell old} hd hrd hs hv => ?_ }
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨pc', d', s', a', m', he', j, hpc'⟩ := hd
    have hpc : pc' = pc := (Event.mk.inj (Option.some.inj (he'.symm.trans he))).1
    obtain ⟨-, lo, hi', bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
    · obtain ⟨j, -, -, none, -⟩ := qk
      rw [none] at hat
      cases hat
    · obtain ⟨j', hpcj, -⟩ := pv
      exact absurd (hpc'.symm.trans (hpc.trans hpcj)) (qk_ne_pv _ _)
  · exfalso
    obtain ⟨a, vals, sh, j, hT, hj, hc⟩ := hv
    exact qk_nostore hp hX hf hu safe base rows init hG hd hrd hs
      ⟨a, vals, sh, j, hT, (List.getElem?_eq_some_iff.mp hj).1, hc⟩

/-- The cells of a QK MMA's accumulator are written by QK MMAs only. -/
theorem qk_closed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) :
    ∀ i j cell, QkIssue X i → X.MmaReadCell i cell → X.MmaCell j cell →
      WriteBefore L X j i → QkIssue X j := by
  intro i j cell hd hrd hmc _
  have hmc0 := mma_read_write hp hX hf base hrd
  obtain ⟨pc1, d1, s1, acc1, mask1, he1, -, lo, hi1, -, -, kind⟩ :=
    mma_write_cell hp hX hf base hmc0
  obtain ⟨pc', d', s', a', m', he', j', hpc'⟩ := hd
  have hpc : pc' = pc1 := (Event.mk.inj (Option.some.inj (he'.symm.trans he1))).1
  obtain ⟨pc2, d2, s2, acc2, mask2, he2, -, lo2, hi2, -, -, kind2⟩ :=
    mma_write_cell hp hX hf base hmc
  rcases kind with ⟨jq, -, hd1, -⟩ | ⟨jp, hpcj, -⟩
  swap
  · exact absurd (hpc'.symm.trans (hpc.trans hpcj)) (qk_ne_pv _ _)
  rcases kind2 with ⟨jq2, hq2, hd2, -⟩ | ⟨jp2, -, hd2, -⟩
  · exact ⟨pc2, d2, s2, acc2, mask2, he2, jq2, hq2⟩
  · omega


/-- **Every cell a completed QK MMA writes has a single-precision value.** -/
theorem qk_results (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X) :
    ∀ k g d s acc mask row col cell, QkIssue X (g, k) → X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true →
      ∃ r : ℝ, Result L Assumptions.all X (g, k) cell (.float .f32 r) :=
  results hp hX hf hu safe base rows init hG hws ht hmd
    (qk_elements hp hX hf hu safe base rows init hG words nub form) (qk_closed hp hX hf base)

/-- **Every value a QK MMA leaves in a cell is a single-precision number.** -/
theorem qk_float (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    {i : EvId} {cell : Cell} {v : Value} (h : Result L Assumptions.all X i cell v)
    (hq : QkIssue X i) (hd : X.async.mmaDone i = true) : ∃ r : ℝ, v = .float .f32 r :=
  result_float hp hX hf base hG (qk_elements hp hX hf hu safe base rows init hG words nub form)
    (qk_closed hp hX hf base) h hq hd

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
