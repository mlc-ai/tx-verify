-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Common.OccursSite
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.History
import Lemmas.Flow.NotBulk
import Lemmas.Kernel.Safety.TableU

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.MbarRow MbarRow

private def inRegion (p : Nat) :=
  decide (27 < p ∧ p < 574 ∨ 574 < p ∧ p < 2331 ∨ 2565 ≤ p ∧ p < 2853 ∨
    2344 < p ∧ p < 2557 ∧ p ≠ 2422)

private theorem regions : kernel.code.zipIdx.all (fun x => !objectOp x.1.op || inRegion x.2) =
    true := by decide +kernel

private theorem mma_range (s : Mma.Site) : 2422 ≤ s.pc ∧ s.pc < 2557 ∨ s.pc = 2337 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem loader_range (s : Loader.Site) : 2344 ≤ s.pc ∧ s.pc < 2422 ∨ s.pc = 2337 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- Every mbarrier event that occurs (in the trace, or the lane's next) is in the pc region and
warp set of its producer role. -/
public theorem place_occ {Q L m X g k e l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (he : Occurs L X g k e)
    (hm : Frame.MbarOf e l) :
    StartupAt L g e.pc ∨ PrologueAt L g e.pc ∨ SoftmaxAt L g e.pc ∨ EpilogueAt L g e.pc ∨
    DispatchAt L g e.pc ∨ LoaderAt L g e.pc ∨ MmaAt L g e.pc := by
  have hg := he.lt hX
  have obj := objectKind hm
  have hu : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at obj; exact obj.elim
  obtain ⟨s,hs,pc,t,ins,o,_,inv,hc,fire⟩ := he.site hp hX hf hu
  have nu := he.noUb hX
  have hop : objectOp ins.op = true := by
    cases h : objectOp ins.op
    · exact False.elim (notObject_of_op h fire obj)
    · rfl
  have code : kernel.code[e.pc]? = some ins := pc ▸ hc
  have reg := List.all_eq_true.mp regions (ins,e.pc)
    (List.mem_zipIdx_iff_getElem?.mpr code)
  simp only [hop,Bool.not_true,Bool.false_or,inRegion,decide_eq_true_eq] at reg
  have atPc := pc ▸ state_role s
  rcases reg with h | h | h | h
  · obtain ⟨w,d,n,rfl⟩ := atPc.prologue h.1 h.2
    have lo : g%L.block < 128 := (reached_table hf hg nu hs).2.1
    exact .inr (.inl ⟨by omega,h.1.le,h.2⟩)
  · obtain ⟨w,ent,d,n,rfl⟩ := atPc.softmax h.1 h.2
    have lo := data_lane hp hX hf hg nu hs
    exact .inr (.inr (.inl ⟨by omega,.inl ⟨h.1.le,h.2⟩⟩))
  · obtain ⟨w,ent,d,n,rfl⟩ := atPc.epilogue h.1 h.2 inv
    have lo := data_lane hp hX hf hg nu hs
    exact .inr (.inr (.inr (.inl ⟨by omega,.inl h⟩)))
  · obtain ⟨w,x,r,d,n,rfl⟩ := atPc.worker h.1 h.2.1 h.2.2
    have hi := (reached_table hf hg nu hs).2
    right; right; right; right; right
    cases r with
    | loader =>
      have warp : g%L.block/32 = 6 := hi.1
      change e.pc = d.site.pc at pc
      have lim := loader_range d.site
      exact .inl ⟨warp,by omega,by omega⟩
    | mma =>
      have warp : g%L.block/32 = 7 := hi.1
      change e.pc = d.site.pc at pc
      have lim := mma_range d.site
      exact .inr ⟨warp,by omega,by omega⟩

/-- Every mbarrier event is in the pc region and warp set of its producer role. -/
public theorem mbar_place {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Place Q L X :=
  fun _ he hm => place_occ hp hX hf (.inl he) hm

end PTX.Kernels.InklingRelDecode.Proof.Export
