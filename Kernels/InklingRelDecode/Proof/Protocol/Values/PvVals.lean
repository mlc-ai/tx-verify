-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvElems
public import Kernels.InklingRelDecode.Proof.Protocol.Values.StoreElement
public import Kernels.InklingRelDecode.Proof.Protocol.Values.ResultReal
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Lib.QkCell
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The elements and the stored words of the PV MMAs as reals

`pv_elements` is the typing record of the PV MMAs (their elements and the rescale words are
numbers), `pv_vals` the value record: the A element is the probability `pw`, the B element the cache
element, and the real of a rescale word `sv` is the one its store word is. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The real of the word store `src` leaves in `cell`. -/
noncomputable def svOf (L : Launch) (X : Execution) (src : EvId) (cell : Cell) : ℝ :=
  Classical.epsilon fun r => ∃ old, StoreValue L X src cell old ∧ valFloat .f32 old = .ok r

/-- **A store leaves one word in a cell.** -/
theorem storeValue_unique (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {src : EvId} {cell : Cell} {o1 o2 : Value}
    (h1 : StoreValue L X src cell o1) (h2 : StoreValue L X src cell o2) : o1 = o2 := by
  obtain ⟨a1, v1, sh1, j1, ⟨pc1, g1⟩, e1, c1⟩ := h1
  obtain ⟨a2, v2, sh2, j2, ⟨pc2, g2⟩, e2, c2⟩ := h2
  have e := Option.some.inj (g1.symm.trans g2)
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at e
  obtain ⟨-, rfl, rfl, rfl⟩ := e
  have hs1 := st_write_cell hp hX hf base (x := src) (cell := cell)
    ⟨a1, v1, sh1, j1, ⟨pc1, g1⟩, (List.getElem?_eq_some_iff.mp e1).1, c1⟩
  have hs2 := st_write_cell hp hX hf base (x := src) (cell := cell)
    ⟨a1, v1, sh1, j2, ⟨pc1, g1⟩, (List.getElem?_eq_some_iff.mp e2).1, c2⟩
  have hj : j1 = j2 := by
    obtain ⟨-, -, k1 | k1⟩ := hs1
    · obtain ⟨a', v', ba, w, j', gg, ha, hba, hj', hc'⟩ := k1
      rw [g1] at gg
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at gg
      obtain ⟨-, rfl, rfl, rfl⟩ := gg
      subst ha
      have col := congrArg Cell.column (c1.symm.trans c2)
      rw [cell_split L src.1 ba 32 w j1 (by omega), cell_split L src.1 ba 32 w j2 (by omega)]
        at col
      simp only at col
      omega
    · obtain ⟨a', v', w, j', gg, ha, hj', hc'⟩ := k1
      rw [g1] at gg
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at gg
      obtain ⟨-, rfl, rfl, rfl⟩ := gg
      subst ha
      have col := congrArg Cell.column (c1.symm.trans c2)
      rw [cell_split L src.1 256 64 w j1 (by omega), cell_split L src.1 256 64 w j2 (by omega)]
        at col
      simp only at col
      omega
  subst hj
  rw [e1] at e2
  exact Option.some.inj e2

theorem svOf_eq (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {src : EvId} {cell : Cell} {old : Value} {r : ℝ}
    (hv : StoreValue L X src cell old) (hr : valFloat .f32 old = .ok r) :
    svOf L X src cell = r := by
  have hex : ∃ r', ∃ old', StoreValue L X src cell old' ∧ valFloat .f32 old' = .ok r' :=
    ⟨r, old, hv, hr⟩
  obtain ⟨old', hv', hr'⟩ := Classical.epsilon_spec hex
  obtain rfl := storeValue_unique hp hX hf base hv' hv
  exact (Except.ok.inj (hr'.symm.trans hr))

private theorem pv_a_some (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {i : EvId} {d s acc mask}
    (hd : PvIssue X i) (hi : X.MmaIssue i d s acc mask) : ∃ a, s.aTmem = some a := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hd
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  subst hj
  obtain ⟨b, -, -, hA⟩ := Mma.Export.pv_acc hp hX hf base he ⟨j, rfl⟩
  exact ⟨_, hA j rfl⟩

/-- **The typing record of the PV MMAs**: their elements are numbers, and so are the words of the
rescale stores they read. -/
theorem pv_elements (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    (W : Iface.PWords X)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) : Elements (PvIssue X) L X :=
  { b := fun hd hi _ ho hrow hk =>
      ⟨_, pv_b_ideal hp hX hf rows init words hu nub form base hd hi ho hrow hk⟩
    q := fun hd hi hat _ _ _ _ => by
      obtain ⟨a, ha⟩ := pv_a_some hp hX hf base hd hi
      rw [ha] at hat
      cases hat
    p := fun _ hi hat _ ho hrow hk =>
      p_element hp hX hf hu safe base rows init hG hws ht hmd W hi hat ho hrow hk
    store := fun {i src cell old} _ hrd hs hv =>
      store_element hp hX hf hu hG safe base rows init hrd hs hv hR }

/-- The row of a PV issue is valid when the row of the cell it writes is. -/
theorem pv_link (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) {i : EvId} {d s acc mask row col cell}
    (hq : PvIssue X i) (hi : X.MmaIssue i d s acc mask)
    (hw : writeCell s d mask row col = some cell)
    (hv : Lib.QRowValid Q L cell.cta (laneRow cell.lane)) :
    Lib.QRowValid Q L (i.1 / L.block) row := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hq
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  subst hj
  obtain ⟨rfl, hD⟩ := pv_cols hp hX hf base he
  obtain ⟨hmask, lo, -⟩ := Mma.Export.columns hp hX hf base he
  obtain ⟨hr, -, hcell⟩ := Lib.pv_cell hD hmask hw
  have e0 : laneRow (32 * (row / 16) + row % 16) = row := by unfold laneRow; omega
  rw [hcell] at hv
  dsimp only at hv
  rw [lo, e0] at hv
  exact hv

/-- **The value record of the PV MMAs**: the A element is the probability `pw`, the B element the
cache element, the real of a stored word `svOf`. -/
theorem pv_vals (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X)
    (W : Iface.PWords X) {pw : Nat → Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) :
    ElementVals (PvIssue X) L X (pvA L X pw) (pvB Q L X) (svOf L X)
      (fun i row => Lib.QRowValid Q L (i.1 / L.block) row) :=
  { b := fun hd hi _ ho hrow hk =>
      pv_b_ideal hp hX hf rows init words hu nub form base hd hi ho hrow hk
    a := fun hd hv hi _ ho hrow hk =>
      pv_a_ideal hp hX hf hu safe base rows init hG hws ht hmd W P hd hi ho hrow hk hv
    store := fun {i src cell old} _ hrd hs hv => by
      obtain ⟨r, hr⟩ := store_element hp hX hf hu hG safe base rows init hrd hs hv hR
      rw [hr, svOf_eq hp hX hf base hv hr] }

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
