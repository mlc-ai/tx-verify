-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.CopyIndex
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.NotTensor
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
import Kernels.InklingRelDecode.Proof.Loader.CopyPend
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Loader.Export.Count
import Kernels.InklingRelDecode.Proof.Loader.Export.Election
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Kernels.InklingRelDecode.Proof.Lib.TensorSites

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k pc : Nat}

/-- The copies a loader thread issued before a copy site: eight per earlier iteration and the
copies of this iteration at earlier sites. -/
private theorem total (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {a sp} (he : X.get (g,k)=some ⟨pc,.tensorIssue a sp⟩)
    (site : pc ∈ Iface.copyPcs) :
    0<pollRound 2374 ((X.tr g).take k) ∧ ((X.tr g).take k).countP Loader.tensorEv =
      8*(pollRound 2374 ((X.tr g).take k)-1) + Iface.copyIndex pc := by
  have nu : ∀ f, (⟨pc,.tensorIssue a sp⟩ : Event).kind ≠ .ub f := by simp
  have range : 2344<pc ∧ pc<2422 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,x,r,d,n,hs,hd⟩ := loader_state hp hX hf he nu range.1 range.2
  have hg := Frame.lt_of_get hX he
  have warp := copy_warp hp hX hf he site
  have nuB := Frame.noUbBefore_of_get hX he
  have bal := loader_balance hp hX hf hg warp nuB hs
  have cop := loader_copies hp hX hf hg warp nuB hs
  have wins : ElectLead L g ((X.tr g).take k) := by
    intro e he' mask inst ld kd
    obtain ⟨e',mem,mask',inst',kd'⟩ := elected hp hX hf he nu site
    have full := Lib.electLead_of_elected hX (g := g) ⟨e',List.mem_of_mem_take mem,mask',inst',kd'⟩
    exact full e (List.mem_of_mem_take he') mask inst ld kd
  obtain ⟨p,u,hsite⟩ := Loader.site_of_copyPc d.site (hd ▸ site)
  have cnt (c : Cls) : n c = ((X.tr g).take k).countP (cls c) := fcount hs c
  have same : n (.winner (laneOf L g)) = n .elect := by
    rw [cnt, cnt]
    apply List.countP_congr
    intro e he'
    obtain ⟨q,kd⟩ := e
    cases kd <;> simp only [cls]
    simp [wins _ he' _ _ _ rfl]
  have idx : Iface.copyIndex pc = 2*p.val + (if u then 1 else 0) := by
    have : pc = (Loader.Site.copy p u).pc := hsite ▸ hd
    subst this
    fin_cases p <;> cases u <;> rfl
  obtain ⟨ho,hq,_⟩ := Loader.copy_place p u
  rw [hsite] at bal cop
  rw [ho] at bal
  rw [hq] at cop
  have h1 : n .copy = ((X.tr g).take k).countP Loader.tensorEv := cnt .copy
  have h2 : n (.poll 2374) = pollRound 2374 ((X.tr g).take k) := cnt _
  have hp3 := p.isLt
  cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] at cop idx <;> omega

/-- A copy of a loader thread is at a loader site, ready-barrier slot `(pre + round - 1) % 3`. -/
private theorem facts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {a sp} (he : X.get (g,k)=some ⟨pc,.tensorIssue a sp⟩)
    (warp : g%L.block/32=6) :
    pc ∈ Iface.copyPcs ∧ 0<pollRound 2374 ((X.tr g).take k) ∧
      ((X.tr g).take k).countP Loader.tensorEv =
        8*(pollRound 2374 ((X.tr g).take k)-1) + Iface.copyIndex pc ∧
      ∃ s : Fin 3, sp.mbar = Iface.kvReadyLoc L (g/L.block) s ∧
        s.val = (Iface.preloadCount Q L (g/L.block) + pollRound 2374 ((X.tr g).take k) - 1)%3 := by
  have site : pc ∈ Iface.copyPcs := by
    rcases Lib.tensor_issue_site hX he with pre|wk
    · exfalso
      have range : 27<pc ∧ pc<574 := by
        simp only [Lib.preloadPcs, List.mem_cons, List.not_mem_nil, or_false] at pre
        omega
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hw,_⟩ := prologue_event hp hX hf he (by simp)
        range.1 range.2
      omega
    · exact wk
  obtain ⟨pos,tot⟩ := total hp hX hf he site
  refine ⟨site,pos,tot,?_⟩
  obtain ⟨_,hc⟩ := packet_credit hp hX hf warp he (e := ⟨pc,.tensorIssue a sp⟩)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at site ⊢; omega)
    (.inr ⟨a,sp,rfl⟩)
  rcases hc with ⟨_,kd⟩|⟨sp',kd,bar,_⟩
  · simp at kd
  · obtain ⟨-,rfl⟩ := Kind.tensorIssue.inj kd
    exact ⟨_,bar,rfl⟩

/-- Copies to one slot among the first `T` copies, eight per iteration. -/
private def toSlot (pre : Nat) (σ : Fin 3) (T : Nat) : Nat :=
  8 * Iface.ringVisits pre (T/8) σ + if (pre+T/8)%3 = σ.val then T%8 else 0

private theorem toSlot_succ (pre T : Nat) (σ : Fin 3) :
    toSlot pre σ (T+1) = toSlot pre σ T + if (pre+T/8)%3 = σ.val then 1 else 0 := by
  unfold toSlot Iface.ringVisits
  have := σ.isLt
  split_ifs <;> omega

private theorem ready_eq (c : Nat) {s s' : Fin 3} :
    Iface.kvReadyLoc L c s = Iface.kvReadyLoc L c s' ↔ s.val = s'.val := by
  simp only [Iface.kvReadyLoc, Iface.kvReady, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
  omega

private theorem prefix_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (warp : g%L.block/32=6) (σ : Fin 3) (lim : k < (X.tr g).length) :
    ∀ j ≤ k, ((X.tr g).take j).countP (issuesTo (Iface.kvReadyLoc L (g/L.block) σ)) =
      toSlot (Iface.preloadCount Q L (g/L.block)) σ (((X.tr g).take j).countP Loader.tensorEv) := by
  intro j
  induction j with
  | zero => intro _; simp [toSlot, Iface.ringVisits]
  | succ j ih =>
    intro hj
    have lt : j < (X.tr g).length := by omega
    have prev := ih (by omega)
    rw [List.take_succ_eq_append_getElem lt, List.countP_append, List.countP_append, prev]
    rcases hev : (X.tr g)[j] with ⟨q,kd⟩
    cases kd with
    | tensorIssue a' sp' =>
      have get : X.get (g,j) = some ⟨q,.tensorIssue a' sp'⟩ := by
        rw [← hev]; exact List.getElem?_eq_getElem lt
      obtain ⟨site,pos,tot,s,bar,hs⟩ := facts hp hX hf get warp
      simp only [issuesTo, Loader.tensorEv, List.countP_singleton, bar, decide_eq_true_eq,
        ready_eq, ite_true]
      rw [toSlot_succ]
      have idx := Iface.copyIndex_lt site
      split_ifs <;> omega
    | _ => simp [issuesTo, Loader.tensorEv]

/-- **The loader's copy count**: the issues of a copy site to its ready barrier before it are
eight per earlier iteration that used the slot, plus the earlier sites of its own iteration. -/
public theorem copy_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {a sp} (he : X.get (g,k)=some ⟨pc,.tensorIssue a sp⟩)
    (warp : g%L.block/32=6) {σ : Fin 3} (bar : sp.mbar = Iface.kvReadyLoc L (g/L.block) σ) :
    pc ∈ Iface.copyPcs ∧ 0<pollRound 2374 ((X.tr g).take k) ∧
      ((X.tr g).take k).countP (issuesTo sp.mbar) =
        8*Iface.ringVisits (Iface.preloadCount Q L (g/L.block))
          (pollRound 2374 ((X.tr g).take k)-1) σ + Iface.copyIndex pc ∧
      σ.val = (Iface.preloadCount Q L (g/L.block) + pollRound 2374 ((X.tr g).take k) - 1)%3 := by
  obtain ⟨site,pos,tot,s,bar',hs⟩ := facts hp hX hf he warp
  have eq := (ready_eq (L := L) (g/L.block)).mp (bar'.symm.trans bar)
  refine ⟨site,pos,?_,by omega⟩
  rw [bar,prefix_count hp hX hf warp σ (List.getElem?_eq_some_iff.mp he).1 k le_rfl]
  have idx := Iface.copyIndex_lt site
  unfold toSlot
  rw [tot]
  have : (8*(pollRound 2374 ((X.tr g).take k)-1)+Iface.copyIndex pc)/8 =
      pollRound 2374 ((X.tr g).take k)-1 := by omega
  rw [this]
  split_ifs <;> omega

/-- **A copy site's block is below the block count**: the loader's block at its `r`-th poll is
the preloaded count plus `r - 1`. -/
public theorem copy_block (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {a sp} (he : X.get (g,k)=some ⟨pc,.tensorIssue a sp⟩)
    (site : pc ∈ Iface.copyPcs) :
    Iface.preloadCount Q L (g/L.block)+pollRound 2374 ((X.tr g).take k)-1 <
      Lib.blocksOf Q L (g/L.block) := by
  have nu : ∀ f, (⟨pc,.tensorIssue a sp⟩ : Event).kind ≠ .ub f := by simp
  have range : 2344<pc ∧ pc<2422 := by
    simp only [Iface.copyPcs, List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,x,r,d,n,hs,hd⟩ := loader_state hp hX hf he nu range.1 range.2
  have hg := Frame.lt_of_get hX he
  obtain ⟨_,ref,ord,_⟩ := (reached_table hf hg (Frame.noUbBefore_of_get hX he) hs).2
  obtain ⟨p,u,hsite⟩ := Loader.site_of_copyPc d.site (hd ▸ site)
  obtain ⟨j,lo,hi,hc,-⟩ := Loader.ref_loop ref (by rw [hsite]; rfl)
  have size := Lib.blocksOf_lt hp hg
  have cnt : n (.poll 2374) = pollRound 2374 ((X.tr g).take k) := fcount hs _
  have polls : Loader.polls (Iface.preloadCount Q L (g/L.block)) (iterCount Q L (g/L.block)) d =
      (Loader.bits d.counter).toNat - Iface.preloadCount Q L (g/L.block) + 1 := by
    unfold Loader.polls; rw [hsite]
  rw [hc, Loader.bits_b32 (by change j < Lib.blocksOf Q L (g/L.block) at hi; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by change j < Lib.blocksOf Q L (g/L.block) at hi; omega)]
    at polls
  change j < Lib.blocksOf Q L (g/L.block) at hi
  omega

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
