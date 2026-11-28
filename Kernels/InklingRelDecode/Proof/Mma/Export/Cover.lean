-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Common.Roles
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Common.MmaHistory
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.CoverHist
import Kernels.InklingRelDecode.Proof.Mma.FinCount
import Kernels.InklingRelDecode.Proof.Mma.QkBalance
import Kernels.InklingRelDecode.Proof.Mma.PvBalance
import Kernels.InklingRelDecode.Proof.Mma.Export.Broadcast
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Kernels.InklingRelDecode.Proof.Lib.KvCover
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Mma.OperandWords
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Proof PTX.Frame

private theorem pvCommit_site (s : Site) : 2546 = s.pc → s = .pvCommit1 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The lane's history at an MMA-region event**: the state the event is fired from, and what the
lane issued before it. -/
private theorem hist_at {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,k) = some e) (warp : g%L.block/32 = 7)
    (hlead : ElectLead L g (X.tr g)) (lo : 2422 < e.pc) (hi : e.pc < 2557) :
    ∃ w x round, ∃ (d : D), ∃ n, stateAt (thread Q L) X g k =
      some (some (workerState w x (.mma round) d n)) ∧ e.pc = d.site.pc ∧ Hist X g d k := by
  have nuk (f : Fault) : e.kind ≠ .ub f := by
    cases e with | mk p kd => rintro rfl; exact (hu.worker (by omega)).kind he _ rfl
  obtain ⟨w,x,round,d,n,hs,pcEq⟩ := mma_state hp hX hf he nuk lo hi
  have nu := noUbBefore_of_get hX he
  have seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7 := fun k pc md a b c recv ok get site =>
    broadcast_seven hp hX hf words warp get site
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hist := mma_history_at hp hX hf words (I := fun d n => Hist X g d (n .all))
    (fun n _ => hist_init) (fun k d n e d' get clean all pc inv q p fires h move => by
      have bump : Code.bump cls n e .all = n .all + 1 := by simp [Code.bump,cls]
      rw [bump,all]
      exact hist_step hlead seven get clean pc inv q p fires (all ▸ h) move)
    hk hs (prefix_ub_zero hs nu)
  have all : n .all = k := by
    have h := fcount hs .all
    have len : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    simp only [cls,List.countP_true,List.length_take] at h
    omega
  change Hist X g d (n .all) at hist
  rw [all] at hist
  exact ⟨w,x,round,d,n,hs,pcEq,hist⟩

/-- **The history before a score or an empty commit**: the state the commit is fired from. -/
private theorem commit_hist {Q L m X g jc pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨pc,.tc (.commit sp)⟩)
    (hpc : pc = 2499 ∨ pc = 2546 ∨ pc = 2548 ∨ pc = 2553) :
    ∃ w x round d n, stateAt (thread Q L) X g jc =
      some (some (workerState w x (.mma round) d n)) ∧ pc = d.site.pc ∧ Hist X g d jc := by
  have warp := commit_warp hp hX hf he
  have hlead : ElectLead L g (X.tr g) := by
    obtain ⟨ev,hev,ew⟩ := elected hp hX hf he (fun _ => nofun) (by simp; omega)
    exact Lib.electLead_of_elected hX ⟨ev,(List.take_sublist jc _).subset hev,ew⟩
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := hist_at hp hX hf words hu he warp hlead
    (by change 2422 < pc; omega) (by change pc < 2557; omega)
  exact ⟨w,x,round,d,n,hs,pcEq,hist⟩

/-- **The history before an empty commit**: with `i` its PV ordinal, the lane issued each QK
step of iteration `i - 1` and each PV step of iteration `i` before it. -/
private theorem commit_history {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2546,.tc (.commit sp)⟩) :
    1 ≤ pollRound 2510 ((X.tr g).take jc) ∧
      (∀ j, QKE X g (pollRound 2510 ((X.tr g).take jc)) j jc) ∧
      ∀ j, PVE X g (pollRound 2510 ((X.tr g).take jc)) j jc := by
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := commit_hist hp hX hf words hu he (.inr (.inl rfl))
  obtain ⟨s,i,v⟩ := d
  change 2546 = s.pc at pcEq
  obtain rfl := pvCommit_site s pcEq
  obtain ⟨hi,_,ref,hq,hp',-⟩ := reached_table hf hg nu hs
  have loop : Inv ⟨.pvCommit1,i,v⟩ := hi.1
  have pv : pollRound 2510 ((X.tr g).take jc) = i := by
    have := (fcount hs (.poll 2510)).symm.trans hp'
    exact this
  rw [pv]
  change 0 < i ∧ _ at loop
  refine ⟨loop.1,fun j => hist.prev (.inr rfl) loop.1 j,fun j => hist.done j (by simp [vd])⟩

private theorem qk_pce (j : Fin 8) : Lib.qkIssue j = qkPc j := by fin_cases j <;> rfl

private theorem pvCommit2_site (s : Site) : 2548 = s.pc → s = .pvCommit2 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem qkCommit_site (s : Site) : 2499 = s.pc → s = .qkCommit := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The history before a score commit**: the lane issued each QK step of its block before it. -/
public theorem score_history {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2499,.tc (.commit sp)⟩) :
    ∀ j : Fin 8, ∃ kR < jc, ∃ dst s acc mask,
      X.get (g,kR) = some ⟨Lib.qkIssue j,.tc (.mma dst s acc mask)⟩ ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take jc) := by
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := commit_hist hp hX hf words hu he (.inl rfl)
  obtain ⟨s,i,v⟩ := d
  change 2499 = s.pc at pcEq
  obtain rfl := qkCommit_site s pcEq
  obtain ⟨hi,_,ref,hq,hp',-⟩ := reached_table hf hg nu hs
  have qr : pollRound 2462 ((X.tr g).take jc) = i+1 := (fcount hs (.poll 2462)).symm.trans hq
  intro j
  obtain ⟨kR,lt,d',s',a',m',get,q,-⟩ := hist.cur j (by simp [kd]) (.inl rfl)
  exact ⟨kR,lt,d',s',a',m',by rw [qk_pce j]; exact get,by rw [q,qr]⟩

private theorem qk_site (j : Fin 8) : ∀ s : Site, qkPc j = s.pc → s = .qk j := by
  fin_cases j <;> intro s <;> cases s <;>
    repeat' first | decide +kernel | (rename_i j'; revert j')

private theorem pv_site (j : Fin 8) : ∀ s : Site, pvPc j = s.pc → s = .pv j := by
  fin_cases j <;> intro s <;> cases s <;>
    repeat' first | decide +kernel | (rename_i j'; revert j')

private theorem qk_spec {Q L m X g kR j dst sp acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,kR) = some ⟨qkPc j,.tc (.mma dst sp acc mask)⟩) :
    ∃ i, pollRound 2462 ((X.tr g).take kR) = i+1 ∧ sp.descriptor = Lib.qkDesc ∧
      sp.b = ⟨kWord L i j*16,0,1024,0,false,false,.b128⟩ ∧ sp.lowCta = g/L.block := by
  have warp := (read_slot hp hX hf words he).1
  have range : 2422 < qkPc j ∧ qkPc j < 2557 := by fin_cases j <;> decide
  obtain ⟨w,x,d,t,ins,o,ht,loop,pcEq,hc,ff,hq,hp'⟩ := mma_event hp hX hf warp he
    (fun _ => nofun) range.1 range.2
  obtain ⟨s,i,v⟩ := d
  obtain rfl := qk_site j s pcEq
  obtain ⟨desc,atmem,a,b,ctas,grp,lo,hi⟩ := q_operands hp j ht hc ff
  obtain ⟨own,_⟩ := owner hp (Frame.lt_of_get hX he) grp lo hi
  change pollRound 2462 _ = i+1 at hq
  exact ⟨i,hq,desc,b,own⟩

private theorem pv_spec {Q L m X g kR j dst sp acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,kR) = some ⟨pvPc j,.tc (.mma dst sp acc mask)⟩) :
    ∃ i, pollRound 2510 ((X.tr g).take kR) = i ∧ sp.descriptor = Lib.pvDesc ∧
      sp.b = ⟨vWord L i j*16,16384,1024,0,false,false,.b128⟩ ∧ sp.lowCta = g/L.block := by
  have warp := (read_slot hp hX hf words he).1
  have range : 2422 < pvPc j ∧ pvPc j < 2557 := by fin_cases j <;> decide
  obtain ⟨w,x,d,t,ins,o,ht,loop,pcEq,hc,ff,hq,hp'⟩ := mma_event hp hX hf warp he
    (fun _ => nofun) range.1 range.2
  obtain ⟨s,i,v⟩ := d
  obtain rfl := pv_site j s pcEq
  obtain ⟨desc,atmem,-,b,ctas,grp,lo,hi⟩ := v_operands hp j ht hc ff
  obtain ⟨own,_⟩ := owner hp (Frame.lt_of_get hX he) grp lo hi
  change pollRound 2510 _ = i at hp'
  exact ⟨i,hp',desc,b,own⟩

/-- **The MMA lane read every byte of both tiles of a slot before the slot's empty commit.**
For the empty commit at position `jc` of PV ordinal `P`, each byte of the K tile and of the V
tile of slot `(P - 1) % 3` is a B operand byte of an MMA the lane issued before the commit, whose
PV ordinal is at least `P - 2`. -/
public theorem commit_covers {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2546,.tc (.commit sp)⟩) :
    ∀ base, (base = L.sharedBase+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3) ∨
        base = L.sharedBase+98304+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3)) →
      ∀ a, a<32768 → ∃ kR < jc, ∃ pc dst s acc mask idx,
        X.get (g,kR) = some ⟨pc,.tc (.mma dst s acc mask)⟩ ∧
        s.byteLoc .b idx = some ⟨.shared,g/L.block,base+a⟩ ∧
        pollRound 2510 ((X.tr g).take jc) ≤ pollRound 2510 ((X.tr g).take kR)+2 := by
  obtain ⟨pos,qk,pv⟩ := commit_history hp hX hf words hu he
  have align := hp.sharedAlignment
  intro base hb a ha
  rcases hb with rfl|rfl
  · obtain ⟨j,idx,cov⟩ := Lib.k_cover
      (B := L.sharedBase+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3)) (a := a) (by omega) ha
    obtain ⟨kR,lt,dst,sp',acc,mask,get,q,p⟩ := qk j
    obtain ⟨i,hi,desc,b,low⟩ := qk_spec hp hX hf words get
    refine ⟨kR,lt,_,dst,sp',acc,mask,idx,get,?_,by omega⟩
    have jb := j.isLt
    have iv : i = pollRound 2510 ((X.tr g).take jc)-1 := by omega
    have eq : kWord L i j*16 = L.sharedBase+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3)
        + 16384*(j.val/4) + 32*(j.val%4) := by
      subst iv
      dsimp [kWord,kLo]
      omega
    have := cov sp' desc (by rw [b,eq])
    rw [this,low]
  · obtain ⟨j,idx,cov⟩ := Lib.v_cover
      (B := L.sharedBase+98304+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3)) (a := a)
      (by omega) ha
    obtain ⟨kR,lt,dst,sp',acc,mask,get,p⟩ := pv j
    obtain ⟨i,hi,desc,b,low⟩ := pv_spec hp hX hf words get
    refine ⟨kR,lt,_,dst,sp',acc,mask,idx,get,?_,by omega⟩
    have jb := j.isLt
    have iv : i = pollRound 2510 ((X.tr g).take jc) := by omega
    have eq : vWord L i j*16 = L.sharedBase+98304+32768*((pollRound 2510 ((X.tr g).take jc)-1)%3)
        + 2048*j.val := by
      subst iv
      dsimp [vWord,vLo]
      omega
    have := cov sp' desc (by rw [b,eq])
    rw [this,low]

private theorem pv_pce (j : Fin 8) : Lib.pvIssue j = pvPc j := by fin_cases j <;> rfl

/-- **The steps a PV issue follows in its lane**: with `b` its PV ordinal, the lane issued each QK
step of block `b - 1` and each earlier PV step of block `b` before it. -/
public theorem pv_prior {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.pvIssue j) :
    1 ≤ pollRound 2510 ((X.tr g).take k) ∧
      (∀ j' : Fin 8, ∃ kR < k, ∃ d' s' a' m',
        X.get (g,kR) = some ⟨Lib.qkIssue j',.tc (.mma d' s' a' m')⟩ ∧
        pollRound 2462 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take k)) ∧
      (∀ j' : Fin 8, j'.val < j.val → ∃ kR < k, ∃ d' s' a' m',
        X.get (g,kR) = some ⟨Lib.pvIssue j',.tc (.mma d' s' a' m')⟩ ∧
        pollRound 2510 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take k)) ∧
      (2 ≤ pollRound 2510 ((X.tr g).take k) → ∃ kR < k, ∃ d' s' a' m',
        X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma d' s' a' m')⟩ ∧
        pollRound 2510 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take k) - 1) := by
  have range : 2422 < pvPc j ∧ pvPc j < 2557 := by fin_cases j <;> decide
  have pce := pv_pce j
  have warp := (read_slot hp hX hf words he).1
  have hlead : ElectLead L g (X.tr g) := by
    obtain ⟨ev,hev,ew⟩ := elected_issue hp hX hf he (by
      subst hj
      fin_cases j <;> decide)
    exact Lib.electLead_of_elected hX ⟨ev,(List.take_sublist k _).subset hev,ew⟩
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := hist_at hp hX hf words hu he warp hlead
    (by subst hj; change 2422 < Lib.pvIssue j; rw [pce]; exact range.1)
    (by subst hj; change Lib.pvIssue j < 2557; rw [pce]; exact range.2)
  obtain ⟨st,i,v⟩ := d
  obtain rfl := pv_site j st ((pce.symm.trans hj.symm).trans pcEq)
  obtain ⟨hi,_,ref,hq,hp',-⟩ := reached_table hf hg nu hs
  have loop : Inv ⟨.pv j,i,v⟩ := hi.1
  have pv : pollRound 2510 ((X.tr g).take k) = i := (fcount hs (.poll 2510)).symm.trans hp'
  change 0 < i ∧ _ at loop
  rw [pv]
  refine ⟨loop.1,fun j' => ?_,fun j' hj' => ?_,fun h2 => ?_⟩
  · obtain ⟨kR,lt,d',s',a',m',get,q,-⟩ := hist.prev (.inr rfl) loop.1 j'
    exact ⟨kR,lt,d',s',a',m',by rw [qk_pce j']; exact get,q⟩
  · obtain ⟨kR,lt,d',s',a',m',get,q⟩ := hist.done j' (by simpa [vd] using hj')
    exact ⟨kR,lt,d',s',a',m',by rw [pv_pce j']; exact get,q⟩
  · obtain ⟨kR,lt,d',s',a',m',get,q⟩ := hist.last (.inr rfl) h2
    exact ⟨kR,lt,d',s',a',m',by rw [pv_pce 7]; exact get,q⟩

/-- **The steps a QK issue follows in its lane**: the lane issued each earlier QK step of its
block before it. -/
private theorem qk_prior' {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.qkIssue j) :
    (∀ j' : Fin 8, j'.val < j.val → ∃ kR < k, ∃ d' s' a' m',
      X.get (g,kR) = some ⟨Lib.qkIssue j',.tc (.mma d' s' a' m')⟩ ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take k)) ∧
    (3 ≤ pollRound 2462 ((X.tr g).take k) → ∃ kR < k, ∃ d' s' a' m',
      X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma d' s' a' m')⟩ ∧
      pollRound 2510 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take k) - 2) := by
  have range : 2422 < qkPc j ∧ qkPc j < 2557 := by fin_cases j <;> decide
  have pce := qk_pce j
  have warp := (read_slot hp hX hf words he).1
  have hlead : ElectLead L g (X.tr g) := by
    obtain ⟨ev,hev,ew⟩ := elected_issue hp hX hf he (by
      subst hj
      fin_cases j <;> decide)
    exact Lib.electLead_of_elected hX ⟨ev,(List.take_sublist k _).subset hev,ew⟩
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := hist_at hp hX hf words hu he warp hlead
    (by subst hj; change 2422 < Lib.qkIssue j; rw [pce]; exact range.1)
    (by subst hj; change Lib.qkIssue j < 2557; rw [pce]; exact range.2)
  obtain ⟨st,i,v⟩ := d
  obtain rfl := qk_site j st ((pce.symm.trans hj.symm).trans pcEq)
  obtain ⟨hi,_,ref,hq,hp',-⟩ := reached_table hf hg nu hs
  have qr : pollRound 2462 ((X.tr g).take k) = i+1 := (fcount hs (.poll 2462)).symm.trans hq
  refine ⟨fun j' hj' => ?_,fun h3 => ?_⟩
  · obtain ⟨kR,lt,d',s',a',m',get,q,-⟩ := hist.cur j' (by simpa [kd] using hj') (.inl rfl)
    exact ⟨kR,lt,d',s',a',m',by rw [qk_pce j']; exact get,by rw [q,qr]⟩
  · rw [qr] at h3
    obtain ⟨kR,lt,d',s',a',m',get,q⟩ := hist.last (.inl rfl) (by change 2 ≤ i; omega)
    refine ⟨kR,lt,d',s',a',m',by rw [pv_pce 7]; exact get,?_⟩
    rw [q,qr]
    change i - 1 = i + 1 - 2
    omega

/-- **The steps a QK issue follows in its lane**: the lane issued each earlier QK step of its
block before it. -/
public theorem qk_prior {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.qkIssue j) :
    ∀ j' : Fin 8, j'.val < j.val → ∃ kR < k, ∃ d' s' a' m',
      X.get (g,kR) = some ⟨Lib.qkIssue j',.tc (.mma d' s' a' m')⟩ ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take k) :=
  (qk_prior' hp hX hf words hu he hj).1

/-- **The last PV step before a QK issue**: from the third ready poll on, the lane issued the last
step of the PV of the block before the previous one. -/
public theorem qk_last {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.qkIssue j) :
    3 ≤ pollRound 2462 ((X.tr g).take k) → ∃ kR < k, ∃ d' s' a' m',
      X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma d' s' a' m')⟩ ∧
      pollRound 2510 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take k) - 2 :=
  (qk_prior' hp hX hf words hu he hj).2

/-- **The QK issues of a step are counted by the rounds**: before the issue of step `j` the lane
issued it once per earlier ready poll of the QK loop. -/
public theorem qk_count {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.qkIssue j) :
    ((X.tr g).take k).countP (fun e => e.pc == pc) + 1 = pollRound 2462 ((X.tr g).take k) := by
  change ((X.tr g).take k).countP (cls (.atPc pc)) + 1 = _
  have range : 2422 < qkPc j ∧ qkPc j < 2557 := by fin_cases j <;> decide
  have pce := qk_pce j
  have warp := (read_slot hp hX hf words he).1
  have lead : ElectLead L g (X.tr g) := by
    obtain ⟨ev,hev,ew⟩ := elected_issue hp hX hf he (by
      subst hj
      fin_cases j <;> decide)
    exact Lib.electLead_of_elected hX ⟨ev,(List.take_sublist k _).subset hev,ew⟩
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  have pcs : pc = qkPc j := hj.trans pce
  have nuk (f : Fault) : (⟨pc,.tc (.mma dst s acc mask)⟩ : Event).kind ≠ .ub f := nofun
  obtain ⟨w,x,round,d,n,hs,pcEq⟩ := mma_state hp hX hf he nuk (by show 2422 < pc; omega)
    (by show pc < 2557; omega)
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have cnt := mma_history_at hp hX hf words (I := QkCnt) (fun n z => qkCnt_start z)
    (fun k d n e d' get _ _ pc' inv _ _ _ h move => qkCnt_step lead
      (fun k pc md a b c recv ok get site => broadcast_seven hp hX hf words warp get site)
      get pc' inv h move) hk hs (prefix_ub_zero hs nu)
  obtain ⟨st,i,v⟩ := d
  obtain rfl := qk_site j st (pcs.symm.trans pcEq)
  obtain ⟨-,-,-,hq,-⟩ := reached_table hf hg nu hs
  have rounds : pollRound 2462 ((X.tr g).take k) = i + 1 := (fcount hs (.poll 2462)).symm.trans hq
  have atpc : n (.atPc (qkPc j)) = ((X.tr g).take k).countP (cls (.atPc (qkPc j))) :=
    fcount hs (.atPc (qkPc j))
  have c1 := cnt.2 j
  simp only [qpend, polls, le_refl, ↓reduceIte] at c1
  rw [pcs]
  omega

/-- **A step of the QK loop is issued once per round**: two issues of one step in a lane are in
different rounds. -/
public theorem qk_once {Q L m X g k1 k2 pc d1 s1 a1 m1 d2 s2 a2 m2} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (h1 : X.get (g,k1) = some ⟨pc,.tc (.mma d1 s1 a1 m1)⟩)
    (h2 : X.get (g,k2) = some ⟨pc,.tc (.mma d2 s2 a2 m2)⟩) {j : Fin 8}
    (hj : pc = Lib.qkIssue j) (lt : k1 < k2) :
    pollRound 2462 ((X.tr g).take k1) < pollRound 2462 ((X.tr g).take k2) := by
  have c1 := qk_count hp hX hf words h1 hj
  have c2 := qk_count hp hX hf words h2 hj
  have get1 : (X.tr g)[k1]? = some ⟨pc,.tc (.mma d1 s1 a1 m1)⟩ := h1
  have step : ((X.tr g).take (k1+1)).countP ((fun e => e.pc == pc)) =
      ((X.tr g).take k1).countP ((fun e => e.pc == pc)) + 1 := by
    rw [List.take_add_one, get1]
    simp [List.countP_append]
  have mono : ((X.tr g).take (k1+1)).countP ((fun e => e.pc == pc)) ≤
      ((X.tr g).take k2).countP ((fun e => e.pc == pc)) := by
    have := (List.take_sublist (k1+1) ((X.tr g).take k2)).countP_le (p := (fun e => e.pc == pc))
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  omega

/-- **The PV issues of a step are counted by the polls**: before the issue of step `j` the lane
issued it once per earlier ready poll of the PV loop. -/
public theorem pv_count {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    {j : Fin 8} (hj : pc = Lib.pvIssue j) :
    ((X.tr g).take k).countP (fun e => e.pc == pc) + 1 = pollRound 2510 ((X.tr g).take k) := by
  change ((X.tr g).take k).countP (cls (.atPc pc)) + 1 = _
  have range : 2422 < pvPc j ∧ pvPc j < 2557 := by fin_cases j <;> decide
  have pcs : pc = pvPc j := hj.trans (pv_pce j)
  have warp := (read_slot hp hX hf words he).1
  have lead : ElectLead L g (X.tr g) := by
    obtain ⟨ev,hev,ew⟩ := elected_issue hp hX hf he (by
      subst hj
      fin_cases j <;> decide)
    exact Lib.electLead_of_elected hX ⟨ev,(List.take_sublist k _).subset hev,ew⟩
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  have nuk (f : Fault) : (⟨pc,.tc (.mma dst s acc mask)⟩ : Event).kind ≠ .ub f := nofun
  obtain ⟨w,x,round,d,n,hs,pcEq⟩ := mma_state hp hX hf he nuk (by show 2422 < pc; omega)
    (by show pc < 2557; omega)
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have cnt := mma_history_at hp hX hf words (I := PvCnt) (fun n z => pvCnt_start z)
    (fun k d n e d' get _ _ pc' inv _ _ _ h move => pvCnt_step lead
      (fun k pc md a b c recv ok get site => broadcast_seven hp hX hf words warp get site)
      get pc' inv h move) hk hs (prefix_ub_zero hs nu)
  obtain ⟨st,i,v⟩ := d
  obtain rfl := pv_site j st (pcs.symm.trans pcEq)
  obtain ⟨-,-,-,-,hp',-⟩ := reached_table hf hg nu hs
  have rounds : pollRound 2510 ((X.tr g).take k) = i := (fcount hs (.poll 2510)).symm.trans hp'
  have atpc : n (.atPc (pvPc j)) = ((X.tr g).take k).countP (cls (.atPc (pvPc j))) :=
    fcount hs (.atPc (pvPc j))
  have c1 := cnt.2 j
  simp only [ppend, polls, le_refl, ↓reduceIte] at c1
  rw [pcs]
  omega

/-- **A step of the PV loop is issued once per poll**: two issues of one step in a lane are
after different polls. -/
public theorem pv_once {Q L m X g k1 k2 pc d1 s1 a1 m1 d2 s2 a2 m2} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (h1 : X.get (g,k1) = some ⟨pc,.tc (.mma d1 s1 a1 m1)⟩)
    (h2 : X.get (g,k2) = some ⟨pc,.tc (.mma d2 s2 a2 m2)⟩) {j : Fin 8}
    (hj : pc = Lib.pvIssue j) (lt : k1 < k2) :
    pollRound 2510 ((X.tr g).take k1) < pollRound 2510 ((X.tr g).take k2) := by
  have c1 := pv_count hp hX hf words h1 hj
  have c2 := pv_count hp hX hf words h2 hj
  have get1 : (X.tr g)[k1]? = some ⟨pc,.tc (.mma d1 s1 a1 m1)⟩ := h1
  have step : ((X.tr g).take (k1+1)).countP ((fun e => e.pc == pc)) =
      ((X.tr g).take k1).countP ((fun e => e.pc == pc)) + 1 := by
    rw [List.take_add_one, get1]
    simp [List.countP_append]
  have mono := (List.take_sublist (k1+1) ((X.tr g).take k2)).countP_le (p := (fun e => e.pc == pc))
  rw [List.take_take, Nat.min_eq_left (by omega)] at mono
  omega

/-- **The history before a done commit**: the lane issued the last PV step of its block before
it. -/
public theorem done_history {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2548,.tc (.commit sp)⟩) :
    ∃ kR < jc, ∃ dst s acc mask,
      X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma dst s acc mask)⟩ ∧
      pollRound 2510 ((X.tr g).take kR) = pollRound 2510 ((X.tr g).take jc) := by
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := commit_hist hp hX hf words hu he (.inr (.inr (.inl rfl)))
  obtain ⟨s,i,v⟩ := d
  change 2548 = s.pc at pcEq
  obtain rfl := pvCommit2_site s pcEq
  obtain ⟨hi,_,ref,hq,hp',-⟩ := reached_table hf hg nu hs
  have pv : pollRound 2510 ((X.tr g).take jc) = i := (fcount hs (.poll 2510)).symm.trans hp'
  obtain ⟨kR,lt,d',s',a',m',get,q⟩ := hist.commit2 rfl
  exact ⟨kR,lt,d',s',a',m',by rw [pv_pce 7]; exact get,by rw [q,pv]⟩

private theorem finCommit_site (s : Site) : 2553 = s.pc → s = .finCommit := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The history before the final commit**: a lane whose CTA has blocks issued the last PV step of
its last block before it, the PV step of the ordinal of the last block. -/
public theorem final_history_ord {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2553,.tc (.commit sp)⟩)
    (nz : Lib.blocksOf Q L (g/L.block) ≠ 0) :
    ∃ kR < jc, ∃ dst s acc mask,
      X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma dst s acc mask)⟩ ∧
      pollRound 2510 ((X.tr g).take kR) = Lib.blocksOf Q L (g/L.block) := by
  have hg := Frame.lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨w,x,round,d,n,hs,pcEq,hist⟩ := commit_hist hp hX hf words hu he (.inr (.inr (.inr rfl)))
  have fc := mma_fin_count hp hX hf words (List.getElem?_eq_some_iff.mp he).1.le hs
    (prefix_ub_zero hs nu)
  obtain ⟨s,i,v⟩ := d
  change 2553 = s.pc at pcEq
  obtain rfl := finCommit_site s pcEq
  obtain ⟨hi,_,ref,-,-⟩ := reached_table hf hg nu hs
  have limit : low v = Lib.blocksOf Q L (g/L.block) := ref_count ref rfl
  have adm : Lib.blocksOf Q L (g/L.block) ≤ 2147483646 := Lib.iter_admitted hp hg
  obtain ⟨pv,lim0⟩ := hist.fin rfl
  have lim1 : i = 0 → low v = 0 ∨ 2147483646 < low v := lim0
  have pv1 : 1 ≤ i → PVE X g (i-1) 7 jc := pv
  have i1 : 1 ≤ i := by
    by_contra! z
    have := lim1 (by omega)
    omega
  obtain ⟨kR,lt,d',s',a',m',get,q⟩ := pv1 i1
  have hi : i = low v + 1 := ((fc : finS .finCommit = true → _) rfl).resolve_right (Nat.ne_of_gt i1)
  refine ⟨kR,lt,d',s',a',m',by rw [pv_pce 7]; exact get,?_⟩
  change pollRound 2510 (List.take kR (X.tr g)) = i - 1 at q
  omega
/-- **The history before the final commit**: the last PV step of the last block. -/
public theorem final_history {Q L m X g jc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (he : X.get (g,jc) = some ⟨2553,.tc (.commit sp)⟩)
    (nz : Lib.blocksOf Q L (g/L.block) ≠ 0) :
    ∃ kR < jc, ∃ dst s acc mask,
      X.get (g,kR) = some ⟨Lib.pvIssue 7,.tc (.mma dst s acc mask)⟩ := by
  obtain ⟨kR,lt,d,s,a,m',get,-⟩ := final_history_ord hp hX hf words hu he nz
  exact ⟨kR,lt,d,s,a,m',get⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
