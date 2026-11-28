-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
import Lemmas.Protocol.MbarRowSource
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.TensorIssue

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control MbarRow

inductive Use (L : Launch) (g : Nat) (s : Site) (ev : Event) (l : Loc) : Prop where
  | init (j) (site : s = .init j) (addr : l = loc L g (initOffset j))
      (kd : ev.kind = .mbInit l 1)
  | arr (b) (site : s = .arr b) (addr : l = loc L g (Iface.kvReady b))
      (kd : PTX.MbarRow.Arrive ev l 65536)
  | copy (b j) (site : s = .ptc b j) (addr : l = loc L g (Iface.kvReady b))
      (kd : PTX.MbarRow.Issue ev l 8192)

private def isUse : Site → Bool
  | .init _ | .arr _ | .ptc _ _ => true
  | _ => false

private theorem only_uses (s : Site) :
    prologueSites.any (fun row => row.pc == s.pc) → isUse s := by
  cases s <;> repeat' first | exact id | decide | (rename_i j; revert j)

theorem use_of_fires {Q L m X g k l d w t e ins o} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some e)
    (hm : Frame.MbarOf e l) (ht : (code Q L g w).AtD d t) (pc : e.pc = d.site.pc)
    (hi : e.pc<574) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : Use L g d.site e l := by
  have lo := d.site.pc_range
  obtain ⟨r,mem,pos,_⟩ := PTX.MbarRow.region_source prologue_sites hX he hm (by omega) hi
  have key := only_uses d.site (List.any_eq_true.mpr ⟨r,mem,beq_iff_eq.mpr (pos.trans pc)⟩)
  cases hs : d.site <;> rw [hs] at key <;> try contradiction
  case init j =>
    have kd := init_shape hp ht j hs hc hf
    have addr : l = loc L g (initOffset j) := by
      obtain ⟨_,k⟩ := e; cases kd; exact hm
    exact .init j rfl addr (addr ▸ kd)
  case arr b =>
    have kd := arrive_shape hp ht b hs hc hf
    have addr : l = loc L g (Iface.kvReady b) := by
      obtain ⟨_,k⟩ := e; change k=_ at kd; cases kd; exact hm
    exact .arr b rfl addr (addr ▸ kd)
  case ptc b j =>
    have type : ∃ a sp, e.kind = .tensorIssue a sp := by
      obtain ⟨guard,dst,coords,fetch⟩ := copy_instr b j
      rw [hs] at hc
      obtain rfl := Option.some.inj (hc.symm.trans fetch)
      cases o with
      | none => exact False.elim (fires_none_notObject hf (PTX.MbarRow.objectKind hm))
      | some _ =>
        obtain ⟨a,sp,eq,_,_⟩ := fires_cpTensor_issue hf
        exact ⟨a,sp,congrArg Event.kind eq⟩
    obtain ⟨a,sp,eq⟩ := type
    obtain ⟨_,_,kd,bar,bytes⟩ := copy_shape hp ht b j hs hc hf eq
    have addr : l = loc L g (Iface.kvReady b) := by
      obtain ⟨_,k⟩ := e; cases kd; exact (Eq.symm hm).trans bar
    exact .copy b j rfl addr ⟨_,_,kd,bar.trans addr.symm,bytes⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue
