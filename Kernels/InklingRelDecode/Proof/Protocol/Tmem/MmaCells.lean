-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Regs
import Lemmas.Tcgen05.TcMmaZeroMask
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot

/-! # The cells of the MMAs

A QK issue's result cells are the 128 columns of its score buffer, a PV issue's the 128 columns of
the accumulator at column 256, and the A cells of a PV issue the 8 columns of its slice of the
probabilities: every one in the issuing CTA, below column 512. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem writeCell_resultCell {s : OperandSpec} {base row col : Nat} {mask : List Nat}
    {cell : Cell} (h : writeCell s base mask row col = some cell) :
    resultCell s base row col = some cell := by
  unfold writeCell at h
  dsimp only at h
  split at h
  · cases h
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i c hc
      dsimp only at h
      split at h
      · cases h
      · dsimp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [hc, h]
        · cases h

private theorem resultCell_cols {s : OperandSpec} {base row col : Nat} {cell : Cell}
    (hm : s.descriptor.m = 64) (hg : s.descriptor.group = .one) (hw : s.descriptor.ws = false)
    (hn : s.descriptor.n = 128) (h : resultCell s base row col = some cell) :
    cell.column = base % 2 ^ 16 + col ∧ col < 128 ∧ base % 2 ^ 16 + 128 ≤ 512 ∧
      (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
  unfold resultCell at h
  dsimp only at h
  have hh : halfDatapath s.descriptor = true := by
    simp [halfDatapath, hm, hg, hw]
  have hr : resultColumns s.descriptor = 128 := by
    simp [resultColumns, hh, hn]
  split at h
  · rename_i hc
    obtain ⟨-, -, -, hcol, hcols⟩ := hc
    rw [hr] at hcols
    have key : cell.column = base % 2 ^ 16 + col ∧
        (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
      split at h <;> (injection h with h; subst h; refine ⟨rfl, ?_⟩; dsimp only; split <;> simp)
    exact ⟨key.1, by omega, by omega, key.2⟩
  · cases h

private theorem aCell_cols {s : OperandSpec} {index : Nat} {cell : Cell} {b : Nat} {a : Nat}
    (hk : s.descriptor.kind.k * s.descriptor.kind.width = 32) (hs : s.aTmem = some a)
    (h : aCell s index = some (cell, b)) :
    a % 2 ^ 16 ≤ cell.column ∧ cell.column < a % 2 ^ 16 + 8 ∧ a % 2 ^ 16 + 8 ≤ 512 ∧
      (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
  unfold aCell at h
  dsimp only at h
  rw [hs] at h
  simp only [Option.bind_some, hk] at h
  split at h
  · rename_i hc
    obtain ⟨-, -, hlt, -⟩ := hc
    have key : a % 2 ^ 16 ≤ cell.column ∧ cell.column < a % 2 ^ 16 + 8 ∧
        (cell.cta = s.lowCta ∨ cell.cta = s.highCta) := by
      injection h with h
      injection h with h
      subst h
      dsimp only
      refine ⟨by omega, by omega, ?_⟩
      split <;> simp
    exact ⟨key.1, key.2.1, by omega, key.2.2⟩
  · cases h

private theorem aCell_none {s : OperandSpec} {index : Nat} (hs : s.aTmem = none) :
    aCell s index = none := by
  unfold aCell
  simp [hs]

private theorem qk_shape : Lib.qkDesc.m = 64 ∧ Lib.qkDesc.n = 128 ∧ Lib.qkDesc.ws = false ∧
    Lib.qkDesc.group = .one := ⟨rfl,rfl,rfl,rfl⟩

private theorem pv_shape : Lib.pvDesc.m = 64 ∧ Lib.pvDesc.n = 128 ∧ Lib.pvDesc.ws = false ∧
    Lib.pvDesc.group = .one ∧ Lib.pvDesc.kind.k * Lib.pvDesc.kind.width = 32 :=
  ⟨rfl,rfl,rfl,rfl,by decide⟩

/-- **The cells of an MMA issue are in its CTA, below column 512**: a result cell written, an
accumulator cell read, an A cell read. -/
public theorem mma_cells {x : EvId} {cell : Cell} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (h : X.MmaAccess x cell) :
    cell.cta = x.1/L.block ∧ cell.column < 512 := by
  obtain ⟨g,k⟩ := x
  have issue : ∀ {d s acc mask}, X.MmaIssue (g,k) d s acc mask →
      s.lowCta = g/L.block ∧ s.highCta = g/L.block ∧
      ((s.descriptor.m = 64 ∧ s.descriptor.n = 128 ∧ s.descriptor.ws = false ∧
        s.descriptor.group = .one) ∧ (∀ a, s.aTmem = some a →
          s.descriptor.kind.k * s.descriptor.kind.width = 32)) := by
    intro d s acc mask ⟨pc,he⟩
    obtain ⟨-,lo,hi,b,qk|pv⟩ := Mma.Export.columns hp hX hf base he
    · obtain ⟨j,-,-,none,desc⟩ := qk
      rw [desc]
      exact ⟨lo,hi,qk_shape,fun a h => by rw [none] at h; cases h⟩
    · obtain ⟨j,-,-,-,desc⟩ := pv
      rw [desc]
      obtain ⟨hm,hn,hw,hg,hk⟩ := pv_shape
      exact ⟨lo,hi,⟨hm,hn,hw,hg⟩,fun _ _ => hk⟩
  rcases h with ⟨d,s,acc,mask,row,col,hi,hw⟩ | ⟨d,s,mask,row,col,hi,hr⟩ |
    ⟨d,s,acc,mask,index,b,hi,ha⟩
  · obtain ⟨lo,hg,⟨hm,hn,hws,hgr⟩,-⟩ := issue hi
    obtain ⟨hc,hl,hb,cta⟩ := resultCell_cols hm hgr hws hn (writeCell_resultCell hw)
    exact ⟨by rcases cta with c|c <;> simp [c,lo,hg],by omega⟩
  · obtain ⟨lo,hg,⟨hm,hn,hws,hgr⟩,-⟩ := issue hi
    obtain ⟨hc,hl,hb,cta⟩ := resultCell_cols hm hgr hws hn hr
    exact ⟨by rcases cta with c|c <;> simp [c,lo,hg],by omega⟩
  · obtain ⟨lo,hg,-,hk⟩ := issue hi
    cases hs : s.aTmem with
    | none => rw [aCell_none hs] at ha; cases ha
    | some a =>
      obtain ⟨h1,h2,h3,cta⟩ := aCell_cols (hk a hs) hs ha
      exact ⟨by rcases cta with c|c <;> simp [c,lo,hg],by omega⟩

/-- **A result cell of an MMA issue**: the issue writes the 128 columns at its destination, in its
CTA; a QK issue's destination is a score buffer, a PV issue's the accumulator at column 256. -/
public theorem mma_write_cell {x : EvId} {cell : Cell} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (h : X.MmaCell x cell) :
    ∃ pc d s acc mask, X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩ ∧
      cell.cta = x.1/L.block ∧ d ≤ cell.column ∧ cell.column < d + 128 ∧
      s.lowCta = x.1/L.block ∧ s.highCta = x.1/L.block ∧
      ((∃ j : Fin 8, pc = Lib.qkIssue j ∧ (d = 0 ∨ d = 128) ∧ s.descriptor = Lib.qkDesc) ∨
        ∃ j : Fin 8, pc = Lib.pvIssue j ∧ d = 256 ∧ s.descriptor = Lib.pvDesc) := by
  obtain ⟨g,k⟩ := x
  obtain ⟨d,s,acc,mask,row,col,⟨pc,he⟩,hw⟩ := h
  obtain ⟨-,lo,hi,b,qk|pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j,hpc,hd,-,desc⟩ := qk
    obtain ⟨hm,hn,hws,hgr⟩ := qk_shape
    rw [← desc] at hm hn hws hgr
    obtain ⟨hc,hl,hb,cta⟩ := resultCell_cols hm hgr hws hn (writeCell_resultCell hw)
    have hb2 : b % 2 < 2 := Nat.mod_lt _ (by omega)
    refine ⟨pc,d,s,acc,mask,he,?_,by omega,by omega,lo,hi,.inl ⟨j,hpc,by omega,desc⟩⟩
    rcases cta with c|c <;> simp [c,lo,hi]
  · obtain ⟨j,hpc,hd,-,desc⟩ := pv
    obtain ⟨hm,hn,hws,hgr,-⟩ := pv_shape
    rw [← desc] at hm hn hws hgr
    obtain ⟨hc,hl,hb,cta⟩ := resultCell_cols hm hgr hws hn (writeCell_resultCell hw)
    refine ⟨pc,d,s,acc,mask,he,?_,by omega,by omega,lo,hi,.inr ⟨j,hpc,hd,desc⟩⟩
    rcases cta with c|c <;> simp [c,lo,hi]

/-- **An accumulator read of an MMA issue is a write of the same cell**: every MMA of the kernel
has zero output masks, one CTA in its group and `M = 64`. -/
public theorem mma_read_write {x : EvId} {cell : Cell} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (h : X.MmaReadCell x cell) : X.MmaCell x cell := by
  obtain ⟨g,k⟩ := x
  obtain ⟨d,s,mask,row,col,⟨pc,he⟩,hr⟩ := h
  obtain ⟨hmask,-,-,b,qk|pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j,-,-,-,desc⟩ := qk
    obtain ⟨hm,-,-,hgr⟩ := qk_shape
    rw [← desc] at hm hgr
    subst hmask
    exact ⟨d,s,true,[0,0,0,0],row,col,⟨pc,he⟩,writeCell_zeroMask hgr hm hr⟩
  · obtain ⟨j,-,-,-,desc⟩ := pv
    obtain ⟨hm,-,-,hgr,-⟩ := pv_shape
    rw [← desc] at hm hgr
    subst hmask
    exact ⟨d,s,true,[0,0,0,0],row,col,⟨pc,he⟩,writeCell_zeroMask hgr hm hr⟩

/-- **An A cell of an MMA issue** is in its CTA, in the eight columns at its A address. -/
public theorem mma_a_range {x : EvId} {cell : Cell} {pc d s acc mask a} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (he : X.get x = some ⟨pc,.tc (.mma d s acc mask)⟩) (hs : s.aTmem = some a)
    (h : X.MmaACell x cell) : cell.cta = x.1/L.block ∧ a ≤ cell.column ∧ cell.column < a + 8 := by
  obtain ⟨g,k⟩ := x
  obtain ⟨d',s',acc',mask',index,b,⟨pc',he'⟩,hc⟩ := h
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  obtain ⟨-,-,rfl,-,-,-⟩ := he'
  obtain ⟨-,lo,hi,b',qk|pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j,-,-,none,-⟩ := qk
    rw [none] at hs
    cases hs
  · obtain ⟨j,-,-,hat,desc⟩ := pv
    have ha : a = 128*((b'-1)%2)+8*j.val := by rw [hat] at hs; exact (Option.some.inj hs).symm
    have kk : s.descriptor.kind.k * s.descriptor.kind.width = 32 := by
      rw [desc]
      obtain ⟨-,-,-,-,hk⟩ := pv_shape
      exact hk
    obtain ⟨h1,h2,-,cta⟩ := aCell_cols kk hs hc
    have hmod : a % 2^16 = a := by omega
    refine ⟨by rcases cta with c|c <;> simp [c,lo,hi],by omega,by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
