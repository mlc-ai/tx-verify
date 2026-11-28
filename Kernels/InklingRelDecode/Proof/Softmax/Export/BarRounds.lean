-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Table
import Kernels.InklingRelDecode.Proof.Softmax.Cnt
import Kernels.InklingRelDecode.Proof.Softmax.BarrierCount

@[expose] public section

/-! # The round of a mandatory rendezvous

A mandatory rendezvous of the softmax loop (pc 2241, 2251, 999, 1012) of round `i` follows `i + 1`
successful polls of `s_ready` and `i` of `o_done`, and has `4 i + p - 2` mandatory rendezvous
before it, `p` its position `0 .. 3` in the round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The position of a mandatory rendezvous in its round. -/
def barPos (pc : Nat) : Nat :=
  if pc = 2241 then 0 else if pc = 2251 then 1 else if pc = 999 then 2 else 3

private theorem bar_site (s : Softmax.Site)
    (h : s.pc = 2241 ∨ s.pc = 2251 ∨ s.pc = 999 ∨ s.pc = 1012) :
    s.afterS = true ∧ s.afterO = true ∧ ∀ i, Softmax.syncPosition s i = barPos s.pc := by
  cases s <;> first
    | exact ⟨rfl,rfl,fun _ => rfl⟩
    | (exfalso; revert h; decide +kernel)
    | (rename_i j; exfalso; revert h; revert j; decide +kernel)

/-- **The round of a mandatory rendezvous.** -/
public theorem bar_round_facts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {pc c} (get : X.get (g,k) = some ⟨pc,.bar 0 c .sync⟩)
    (hpc : pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012) :
    ∃ i, pollRound 1257 ((X.tr g).take k) = i+1 ∧ pollRound 2239 ((X.tr g).take k) = i ∧
      Softmax.Export.mandatory ((X.tr g).take k) + 2 = 4*i + barPos pc := by
  have clean : ∀ f, (Event.mk pc (.bar 0 c .sync)).kind ≠ .ub f := fun _ => nofun
  have lo : 574 < pc := by omega
  have hi : pc < 2331 := by omega
  obtain ⟨w,ent,d,n,hs,pce⟩ := at_site hp hX get clean lo hi
  have hg := lt_of_get hX get
  have nu := noUbBefore_of_get hX get
  have ref := (reached_table hf hg nu hs).2
  change Softmax.Ref _ d (softCounts n) at ref
  have cnt (key : Cls) : n key = ((X.tr g).take k).countP (cls key) := fcount hs key
  have sc := congrArg Softmax.Cnt.s ref.ledger
  have oc := congrArg Softmax.Cnt.o ref.ledger
  change n (.poll 1257) = d.i + d.site.afterS.toNat at sc
  change n (.poll 2239) = (if d.site.afterO then d.i else d.i-1) at oc
  have pcd : d.site.pc = 2241 ∨ d.site.pc = 2251 ∨ d.site.pc = 999 ∨ d.site.pc = 1012 := by
    rw [← pce]; exact hpc
  obtain ⟨aS,aO,pos⟩ := bar_site d.site pcd
  have fixed := soft_fixed_total hp hX (List.getElem?_eq_some_iff.mp get).1.le hs nu
  simp only [cnt] at fixed
  have posi : Softmax.syncPosition d.site d.i = barPos pc := by
    rw [pos]
    exact congrArg barPos pce.symm
  rw [aS,cnt] at sc
  rw [aO,cnt] at oc
  refine ⟨d.i,?_,?_,?_⟩
  · change pollRound 1257 _ = _ at sc
    simpa using sc
  · simp only [ite_true] at oc
    exact oc
  · simp only [Softmax.fixedCount, posi] at fixed
    exact fixed

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
