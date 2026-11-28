-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Tcgen05.TmemRace
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

/-! # Tensor Memory writes are ordered, given the two cross-role orders

By column class, two writes of one cell are, in one CTA:

* two QK MMAs, or two PV MMAs: one MMA lane (the elected lane of warp 7), one accumulator,
  pipelined in program order (`Before.of_mma_po`);
* two probability stores, or two rescale stores: one data thread (`split_thread`), pipelined in
  program order (`StoreDoneBefore.of_po`);
* a QK MMA and a probability store of one score buffer (`QkStoreOrder`), and a PV MMA and a
  rescale store (`PvStoreOrder`): the cross-role orders;
* the other pairs share no cell: the score buffers (columns `[0, 256)`, the probabilities in the
  first 64 of each) and the accumulator (`[256, 384)`) are disjoint. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The QK/probability-store order**: a QK MMA and a probability store (pc 1009) of one CTA with
the MMA's destination buffer are ordered, the MMA done before the store or the store done before
the MMA. -/
def QkStoreOrder (L : Launch) (X : Execution) : Prop :=
  ∀ (x y : EvId) (pc d a : Nat) (s : OperandSpec) (acc : Bool) (mask : List Nat)
    (vals : List Value) (sh : TcShape),
    X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩ → (∃ j : Fin 8, pc = Lib.qkIssue j) →
    X.get y = some ⟨1009, .tc (.st a vals sh)⟩ → x.1 / L.block = y.1 / L.block →
    d = a % 2 ^ 21 → DoneBefore L X x y ∨ StoreDoneBefore L X y x

/-- **The PV/rescale order**: a PV MMA and a rescale store (pc 2328) of one CTA are ordered. -/
def PvStoreOrder (L : Launch) (X : Execution) : Prop :=
  ∀ (x y : EvId) (pc d a : Nat) (s : OperandSpec) (acc : Bool) (mask : List Nat)
    (vals : List Value) (sh : TcShape),
    X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩ → (∃ j : Fin 8, pc = Lib.pvIssue j) →
    X.get y = some ⟨2328, .tc (.st a vals sh)⟩ → x.1 / L.block = y.1 / L.block →
    DoneBefore L X x y ∨ StoreDoneBefore L X y x

/-- **An MMA event of the kernel is its CTA's elected lane of warp 7.** -/
public theorem mma_leader (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {x : EvId} {pc d s acc mask}
    (hx : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) :
    Protocol.KV.leader L X (x.1 / L.block) 7 = x.1 ∧ x.1 % L.block / 32 = 7 := by
  obtain ⟨g,k⟩ := x
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨wx,⟨ex,mx,wnx⟩,-⟩ := Mma.Export.read_slot hp hX hf words hx
  have lx := Protocol.KV.leader_eq hX (Frame.lt_of_get hX hx)
    ⟨ex,(List.take_sublist k _).subset mx,wnx⟩
  rw [wx] at lx
  exact ⟨lx,wx⟩

/-- Two MMA events of the kernel in one CTA are of one thread: the CTA's elected lane. -/
public theorem mma_thread (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {x y : EvId} {pc pc' d d' s s' acc acc' mask mask'}
    (hx : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩)
    (hy : X.get y = some ⟨pc', .tc (.mma d' s' acc' mask')⟩)
    (cta : x.1 / L.block = y.1 / L.block) : x.1 = y.1 := by
  obtain ⟨lx,-⟩ := mma_leader hp hX hf hx
  obtain ⟨ly,-⟩ := mma_leader hp hX hf hy
  rw [cta] at lx
  exact lx.symm.trans ly

variable (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
  (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
    a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
    bs = (PTX.Proof.b32 0).toBytes.map some)
include hp hX hf base

/-- **Two MMAs writing one cell are of one thread and one accumulator.** -/
theorem mm_one {x y : EvId} {cell : Cell} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaCell x cell) (hy : X.MmaCell y cell)
    (ix : X.MmaIssue x d s acc mask) (iy : X.MmaIssue y d' s' acc' mask') :
    x.1 < L.threads ∧ x.1 = y.1 ∧ SameAccumulator d s d' s' := by
  obtain ⟨pc,dx,sx,ax,mx,gx,cx,l1,h1,lx,hx',kx⟩ := mma_write_cell hp hX hf base hx
  obtain ⟨pc',dy,sy,ay,my,gy,cy,l2,h2,ly,hy',ky⟩ := mma_write_cell hp hX hf base hy
  obtain ⟨q,ix⟩ := ix
  obtain ⟨q',iy⟩ := iy
  rw [gx] at ix
  rw [gy] at iy
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at ix iy
  obtain ⟨-,rfl,rfl,-,-⟩ := ix
  obtain ⟨-,rfl,rfl,-,-⟩ := iy
  have cta : x.1 / L.block = y.1 / L.block := cx.symm.trans cy
  refine ⟨Frame.lt_of_get hX gx,mma_thread hp hX hf gx gy cta,?_⟩
  have dd : dx = dy := by
    rcases kx with ⟨-,-,k1,-⟩ | ⟨-,-,k1,-⟩ <;> rcases ky with ⟨-,-,k2,-⟩ | ⟨-,-,k2,-⟩ <;> omega
  subst dd
  have desc : sx.descriptor = sy.descriptor := by
    rcases kx with ⟨-,-,k1,e1⟩ | ⟨-,-,k1,e1⟩ <;> rcases ky with ⟨-,-,k2,e2⟩ | ⟨-,-,k2,e2⟩
    · exact e1.trans e2.symm
    · omega
    · omega
    · exact e1.trans e2.symm
  exact ⟨rfl,by rw [desc],by rw [desc],by rw [lx,ly,cta],by rw [hx',hy',cta]⟩

omit hp hX hf base in
/-- The columns of a probability store cell: the first 64 columns of its buffer. -/
theorem p_cols {g ba w j : Nat} (hba : ba = 0 ∨ ba = 128) (hj : j < 32) :
    ba ≤ (tcDataCell L g (.s16x32bx2 32) (ba + w * 2 ^ 21) j).column ∧
      (tcDataCell L g (.s16x32bx2 32) (ba + w * 2 ^ 21) j).column < ba + 64 ∧
      (tcDataCell L g (.s16x32bx2 32) (ba + w * 2 ^ 21) j).cta = g / L.block := by
  rw [cell_split L g ba 32 w j (by omega)]
  refine ⟨?_,?_,rfl⟩ <;> dsimp only <;> split_ifs <;> omega

omit hp hX hf base in
/-- The columns of a rescale store cell: the first 128 columns of the accumulator. -/
theorem o_cols {g w j : Nat} (hj : j < 64) :
    256 ≤ (tcDataCell L g (.s16x32bx2 64) (256 + w * 2 ^ 21) j).column ∧
      (tcDataCell L g (.s16x32bx2 64) (256 + w * 2 ^ 21) j).column < 384 ∧
      (tcDataCell L g (.s16x32bx2 64) (256 + w * 2 ^ 21) j).cta = g / L.block := by
  rw [cell_split L g 256 64 w j (by omega)]
  refine ⟨?_,?_,rfl⟩ <;> dsimp only <;> split_ifs <;> omega

/-- **Two stores writing one cell are of one thread.** -/
theorem ss_one {x y : EvId} {cell : Cell} (hx : StoreCell L X x cell) (hy : StoreCell L X y cell) :
    x.1 < L.threads ∧ x.1 = y.1 := by
  obtain ⟨lx,tx,kx⟩ := st_write_cell hp hX hf base hx
  obtain ⟨ly,ty,ky⟩ := st_write_cell hp hX hf base hy
  refine ⟨tx,?_⟩
  rcases kx with ⟨a,v,ba,w,j,-,rfl,hb,hj,hc⟩ | ⟨a,v,w,j,-,rfl,hj,hc⟩ <;>
    rcases ky with ⟨a',v',ba',w',j',-,rfl,hb',hj',hc'⟩ | ⟨a',v',w',j',-,rfl,hj',hc'⟩
  · obtain ⟨c1,c2,c3⟩ := p_cols (L := L) (g := x.1) (w := w) hb hj
    obtain ⟨d1,d2,d3⟩ := p_cols (L := L) (g := y.1) (w := w') hb' hj'
    rw [← hc] at c1 c2 c3
    rw [← hc'] at d1 d2 d3
    have : ba = ba' := by omega
    subst this
    exact split_thread (by omega) hj hj' lx ly (c3.symm.trans d3) (hc.symm.trans hc')
  · obtain ⟨c1,c2,c3⟩ := p_cols (L := L) (g := x.1) (w := w) hb hj
    obtain ⟨d1,d2,d3⟩ := o_cols (L := L) (g := y.1) (w := w') hj'
    rw [← hc] at c1 c2 c3
    rw [← hc'] at d1 d2 d3
    omega
  · obtain ⟨c1,c2,c3⟩ := o_cols (L := L) (g := x.1) (w := w) hj
    obtain ⟨d1,d2,d3⟩ := p_cols (L := L) (g := y.1) (w := w') hb' hj'
    rw [← hc] at c1 c2 c3
    rw [← hc'] at d1 d2 d3
    omega
  · exact split_thread (by omega) hj hj' lx ly
      ((o_cols (L := L) (g := x.1) (w := w) hj).2.2.symm.trans
        (hc ▸ hc' ▸ (o_cols (L := L) (g := y.1) (w := w') hj').2.2 ▸ rfl)) (hc.symm.trans hc')

/-- **An MMA and a store writing one cell are ordered**, given the two cross-role orders. -/
theorem ms_order (qk : QkStoreOrder L X) (pv : PvStoreOrder L X) {x y : EvId} {cell : Cell}
    (hx : X.MmaCell x cell) (hy : StoreCell L X y cell) :
    Before L X x y ∨ StoreDoneBefore L X y x := by
  obtain ⟨pc,d,s,acc,mask,gx,cx,l1,h1,-,-,kx⟩ := mma_write_cell hp hX hf base hx
  obtain ⟨-,-,ky⟩ := st_write_cell hp hX hf base hy
  rcases ky with ⟨a,v,ba,w,j,gy,rfl,hb,hj,hc⟩ | ⟨a,v,w,j,gy,rfl,hj,hc⟩
  · obtain ⟨c1,c2,c3⟩ := p_cols (L := L) (g := y.1) (w := w) hb hj
    rw [← hc] at c1 c2 c3
    rcases kx with ⟨j',hpc,hd,-⟩ | ⟨-,-,hd,-⟩
    · have hmod : (ba + w * 2 ^ 21) % 2 ^ 21 = ba := by omega
      rcases qk x y pc d _ s acc mask v _ gx ⟨j',hpc⟩ gy (cx.symm.trans c3)
        (by omega) with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · omega
  · obtain ⟨c1,c2,c3⟩ := o_cols (L := L) (g := y.1) (w := w) hj
    rw [← hc] at c1 c2 c3
    rcases kx with ⟨-,-,hd,-⟩ | ⟨j',hpc,hd,-⟩
    · omega
    · rcases pv x y pc d _ s acc mask v _ gx ⟨j',hpc⟩ gy (cx.symm.trans c3) with h | h
      · exact .inl (.inl h)
      · exact .inr h

/-- **No two Tensor Memory writes are unordered**, given the two cross-role orders. -/
theorem writes_safe (qk : QkStoreOrder L X) (pv : PvStoreOrder L X) :
    ¬ WritesUnsafe L X :=
  writesSafe_of (Lib.no_cp hX) (no_shift hX)
    (fun hx hy => mm_of_po (fun {_ _ _ _ _ _ _ _ _ _ _} hx' hy' ix iy =>
      mm_one hp hX hf base hx' hy' ix iy) hx hy)
    (fun hx hy => ms_order hp hX hf base qk pv hx hy)
    (fun hx hy => ss_of_po (fun hx' hy' => ss_one hp hX hf base hx' hy') hx hy)

end PTX.Kernels.InklingRelDecode.Proof.Tmem
