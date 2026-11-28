-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.PreElect
import Kernels.InklingRelDecode.Proof.Loader.Export.Producer
import Kernels.InklingRelDecode.Proof.Mma.Export.Time
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
public import Kernels.InklingRelDecode.Proof.Lib.ProducerLag

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing MbarRow

private theorem ready_round {Q L m X g c s} (hp : Pre Q L m) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (hw : Waiting L m X .ready c s g) :
    let r := pollRound 2462 (X.tr g)
    s.val=r%3 ∧ okPolls (Ring.ready.obj L c s) (X.tr g)=r/3 ∧
      r<Lib.blocksOf Q L c ∧ threadTime (schedule Q L) X g=Lib.Slots.readyWait r := by
  obtain ⟨rfl,q,sc,hn⟩ := hw
  have ⟨bound,clock⟩ := Mma.Export.wait_time hp hf hn (Or.inl rfl)
  have hg := hn.lt
  obtain ⟨Y,hY,pref,he⟩ := hn
  obtain ⟨_,_,_,warp,_,sEq,_⟩ := wait_info (r := .ready) (rows Y hY) hg he
  have ord := poll_count (r := .ready) (rows Y hY) hg warp s (X.tr g).length
  change s=slot3 (pollRound 2462 ((Y.tr g).take _)) at sEq
  change okPolls _ ((Y.tr g).take _)=visits 0 (pollRound 2462 ((Y.tr g).take _)) s at ord
  rw [pref] at ord sEq
  have pos := congrArg Fin.val sEq
  refine ⟨pos,ord.trans ?_,bound,clock⟩
  unfold visits
  change s.val=_ % 3 at pos
  omega

private theorem block_bounds {pre r : Nat} {s : Fin 3} (lim : pre≤3) (slot : s.val=r%3)
    (j : Nat) (bound : j<r/3+1-(if s.val<pre then 1 else 0)) :
    let u := s.val+3*(j+(if s.val<pre then 1 else 0))
    pre≤u ∧ u≤r ∧ u%3=s.val := by
  dsimp only
  by_cases h : s.val<pre <;> simp only [h,ite_true,ite_false] at bound ⊢ <;> omega

/-- The recurrent arrival lane has issued every block due on this slot if it
exited or its clock has caught up with the waiting MMA lane. -/
theorem loader_arrive_due {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hw : Waiting L m X .ready c s g) :
    let l := Ring.ready.obj L c s
    Due Q L X g (arrivalLane L c 1) (arrivesOn l)
      (dueArr (preload Q L c s) (okPolls l (X.tr g)+1) 1) := by
  obtain ⟨slot,ord,bound,clock⟩ := ready_round hp hf rows hw
  obtain ⟨rfl,_,_,hn⟩ := hw
  let c := g/L.block
  let y := arrivalLane L c 1
  let r := pollRound 2462 (X.tr g)
  let pre := Iface.preloadCount Q L c
  let δ := if s.val<pre then 1 else 0
  have hg := hn.lt
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have geo : y<L.threads ∧ y/L.block=c ∧ y%L.block/32=6 ∧ laneOf L y=0 := by
    simp only [y,arrivalLane,show (1:Fin 2)≠0 by decide,ite_false,Launch.threads,laneOf,
      hp.block]; omega
  obtain ⟨hy,cta,warp,lane⟩ := geo
  change Due Q L X g y _ _
  rw [ord]
  have count (done : (∃ k pc, X.get (y,k)=some ⟨pc,.exit⟩) ∨
      threadTime (schedule Q L) X g≤threadTime (schedule Q L) X y) :
      r/3+1-δ ≤ (X.tr y).countP (arrivesOn (Ring.ready.obj L c s)) := by
    apply Lib.count_of_occurrences (fun k _ => (pollRound 2374 ((X.tr y).take k)+pre-1)/3-δ)
    intro i
    let u := s.val+3*(i.val+δ)
    obtain ⟨lo,hi,us⟩ := block_bounds (pre := pre) (Nat.min_le_left ..) slot i.val i.isLt
    have same : (⟨u%3,by omega⟩ : Fin 3)=s := Fin.ext us
    have observed : Loader.Export.Issued Q L X y 2378 u (fun e =>
        e.kind=.arrive (Iface.kvReadyLoc L (y/L.block) ⟨u%3,by omega⟩) 65536 1 true .cta) := by
      by_contra missing
      obtain ⟨early,live⟩ := Loader.Export.arrival_short hp hX hf words hu hy warp lane
        (cta ▸ lo) (cta ▸ lt_of_le_of_lt hi bound) missing
      rcases done with ⟨k,pc,ex⟩|late
      · exact live k pc ex
      · rw [clock] at late
        change 1000+400*r+100+1≤_ at late
        change _≤1000+400*u+2 at early
        change u≤r at hi
        omega
    obtain ⟨k,e,get,_,kind,num⟩ := observed
    refine ⟨k,e,get,?_,?_⟩
    · rw [cta,same] at kind
      cases e with | mk pc kd =>
        cases kind; simp [arrivesOn,sourceArrive,Ring.obj,Ring.offset,Iface.kvReadyLoc]
    · rw [num,cta]
      change (u-pre+1+pre-1)/3-δ=i.val
      change pre≤u at lo
      dsimp [u] at lo ⊢
      omega
  exact ⟨fun k pc ex => count (.inl ⟨k,pc,ex⟩),fun late => count (.inr late)⟩

private def copyPc (p : Fin 4) (b : Bool) : Nat :=
  [2389,2394,2404,2410][p.val]! + if b then 2 else 0

private def copyIndex (pc : Nat) :=
  [2389,2391,2394,2396,2404,2406,2410,2412].idxOf pc

private theorem copy_index (p : Fin 4) (b : Bool) :
    copyIndex (copyPc p b)=2*p.val+b.toNat := by revert p b; decide

/-- Each selected block contributes eight distinct tensor issues to the ready object. -/
theorem loader_copy_due {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hw : Waiting L m X .ready c s g) :
    let l := Ring.ready.obj L c s
    Due Q L X g (copyLane L X c 2) (issuesTo l)
      (dueCp (preload Q L c s) (okPolls l (X.tr g)+1) 2) := by
  obtain ⟨slot,ord,bound,clock⟩ := ready_round hp hf rows hw
  obtain ⟨rfl,_,_,hn⟩ := hw
  let c := g/L.block
  let y := copyLane L X c 2
  let r := pollRound 2462 (X.tr g)
  let pre := Iface.preloadCount Q L c
  let δ := if s.val<pre then 1 else 0
  have hg := hn.lt
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cta,warp⟩ := leader_warp (X := X) hp hc (by decide : 6<8)
  change y/L.block=c at cta
  change Due Q L X g y _ _
  rw [ord]
  have count (done : (∃ k pc, X.get (y,k)=some ⟨pc,.exit⟩) ∨
      threadTime (schedule Q L) X g≤threadTime (schedule Q L) X y) :
      8*(r/3+1-δ) ≤ (X.tr y).countP (issuesTo (Ring.ready.obj L c s)) := by
    apply Lib.count_of_occurrences (fun k e =>
      8*((pollRound 2374 ((X.tr y).take k)+pre-1)/3-δ)+copyIndex e.pc)
    intro i
    let u := s.val+3*(i.val/8+δ)
    let p : Fin 4 := ⟨i.val%8/2,by omega⟩
    let b := decide (i.val%2=1)
    have ix := i.isLt
    obtain ⟨lo,hi,us⟩ := block_bounds (pre := pre) (Nat.min_le_left ..) slot (i.val/8) (by omega)
    have same : (⟨u%3,by omega⟩ : Fin 3)=s := Fin.ext us
    have observed : Loader.Export.Issued Q L X y (copyPc p b) u (fun e =>
        ∃ sp, e.kind=.tensorIssue Q.kvMap sp ∧ sp.mbar=Iface.kvReadyLoc L (y/L.block)
          ⟨u%3,by omega⟩ ∧ TensorTransfer.bytes sp.descriptor=8192) := by
      by_contra missing
      obtain ⟨early,live⟩ := Loader.Export.copy_short (g := y) hp hX hf words hu hy warp
        (Warp.leader_wins hp hX hc (by decide : 6<8)) (by rw [cta]; exact lo)
        (by rw [cta]; exact lt_of_le_of_lt hi bound) p b missing
      rcases done with ⟨k,pc,ex⟩|late
      · exact live k pc ex
      · rw [clock] at late
        have earlier := (Lib.Slots.kv_ready u p b).2
        change u≤r at hi
        change 1000+400*r+100+1≤_ at late
        change _<1000+400*u+100+1 at earlier
        omega
    obtain ⟨k,e,get,pc,⟨sp,kd,bar,_⟩,num⟩ := observed
    refine ⟨k,e,get,?_,?_⟩
    · rw [cta,same] at bar
      simp [issuesTo,kd,bar,Iface.kvReadyLoc,Ring.obj,Ring.offset]
    · rw [num,cta,pc,copy_index]
      change 8*((u-pre+1+pre-1)/3-δ)+(2*(i.val%8/2)+b.toNat)=i.val
      change pre≤u at lo
      dsimp [u,b] at lo ⊢
      by_cases h : i.val%2=1 <;> simp [h,Bool.toNat] <;> omega
  exact ⟨fun k pc ex => count (.inl ⟨k,pc,ex⟩),fun late => count (.inr late)⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
