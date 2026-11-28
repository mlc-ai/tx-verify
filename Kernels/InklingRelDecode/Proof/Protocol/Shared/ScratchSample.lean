-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchEpoch
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX

/-- At this barrier ordinal the four data warps are publishing a scratch word. -/
def PublishesAt (L : Launch) (X : Execution) (c n : Nat) : Prop :=
  ∀ h i p cnt, h/L.block=c → h%L.block<128 → X.IsBarrier (h,i) 0 cnt p →
    barOrdinal X h i=n → p=2251

/-- The source of a single byte of a scratch sample, with the publishing
event and ordinal of that very issuer. Different bytes can have different issuers. -/
structure ScratchByte (L : Launch) (X : Execution) (g k b : Nat) (a : Acc)
    (bs : List (Option Byte)) (n h u : Nat) (dst : Acc) (ys : List Byte) : Prop where
  cta : h/L.block=g/L.block
  low : h%L.block<128
  store : X.get (h,u)=some ⟨2250,.wr dst ys⟩
  rf : X.rf (.thread (g,k)) b=some (.thread (h,u))
  sync : X.IsBarrier (h,u+1) 0 (some 128) 2251
  epoch : barOrdinal X h (u+1)=n
  addr : dst.loc=a.loc
  size : dst.size=4
  value : bs[b]?=some ys[b]?

theorem scratch_sample {Q L m X g k a bs n b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.get (g,k)=some ⟨2252,.rd a bs⟩)
    (ord : barOrdinal X g k=n+1) (pub : PublishesAt L X (g/L.block) n) (byte : b<a.size) :
    ∃ h u dst ys, ScratchByte L X g k b a bs n h u dst ys := by
  have lg := Softmax.Export.data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
  let c := g/L.block
  let w := g%L.block%4
  let peer := c*L.block+32*w
  have small : w<4 := Nat.mod_lt _ (by decide)
  have ct : peer/L.block=c := by dsimp [peer]; rw [hp.block]; omega
  have low : peer%L.block<128 := by dsimp [peer]; rw [hp.block]; omega
  have warp : peer%L.block/32=w := by dsimp [peer]; rw [hp.block]; omega
  have atGen {t} (ct : t/L.block=c) (low : t%L.block<128) (i p cnt)
      (bar : X.IsBarrier (t,i) 0 cnt p) (same : barOrdinal X t i+1=barOrdinal X g k) : p=2251 :=
    pub t i p cnt ct low bar (by omega)
  obtain ⟨_,_,_,h,u,dst,ys,_,rf,get,cta,idx,val,_,_⟩ :=
    published_scratch_byte hp hX read byte lg low ct warp (atGen ct low)
      (fun j p he => (scratch_exit_ordinal hp hX read he lg low ct.symm).le)
  have lh := Softmax.Export.data_site hp hX get (by simp) (by dsimp; decide) (by dsimp; decide)
  obtain ⟨bar,count⟩ := scratch_epoch_source hp hX read get rf byte lg lh cta (atGen cta lh)
  obtain ⟨whereRead,_⟩ := Softmax.Export.scratch_read hp hX read
  obtain ⟨whereWrite,size⟩ := Softmax.Export.scratch_store hp hX get
  exact ⟨h,u,dst,ys,cta,lh,get,rf,bar,by omega,by rw [whereRead,whereWrite,cta,idx],size,val⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
