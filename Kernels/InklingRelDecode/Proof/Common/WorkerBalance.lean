-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerLedger
public import Kernels.InklingRelDecode.Proof.Loader.ElectBalance
public import Kernels.InklingRelDecode.Proof.Loader.CopyPend
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.OpPcsFast
import Kernels.InklingRelDecode.Proof.Loader.CopyShape
import Lemmas.Flow.TensorIssue
public import Kernels.InklingRelDecode.Proof.Mma.ShuffleBalance
public import Kernels.InklingRelDecode.Proof.Common.WarpColl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

private theorem observed {L g p e} (h : SourceAt L g p e) : Lib.CollectiveAt p e := by
  obtain ⟨_,_,_,hc,fire,_⟩ := h
  exact Lib.collective_at hc fire

def Balance (warp lane bonus loader mma cp cl ex sk : Nat) (n : Cls → Nat) : Prop :=
  (warp=6 → n .elect + loader = 4*n (.poll 2374)) ∧
  (warp=7 → n .shfl + mma = bonus + n (.poll 2462) + n (.poll 2510)) ∧
  (warp=6 → n .copy + cp = 2*n (.winner lane)) ∧
  (warp=6 → n .coll + cl = bonus + 9*n (.poll 2374)) ∧
  (warp=7 → n .coll + cl + n .skip = bonus + 4*(n (.poll 2462) + n (.poll 2510)) +
    n (.atPc 2550) + n (.atPc 2551) + ex ∧ sk ≤ n .skip) ∧
  (warp≠6 → warp≠7 → n .coll + cl = bonus)

private theorem bump_cls (n : Cls → Nat) (e : Event) (c : Cls) :
    Code.bump cls n e c = n c + (cls c e).toNat := by
  change _ + (if cls c e then 1 else 0) = _; cases cls c e <;> rfl

private theorem bump_coll (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .coll = n .coll + (Sched.isWarpColl e).toNat := bump_cls n e .coll

private theorem bump_skip (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .skip = n .skip + (Mma.skipEv e).toNat := bump_cls n e .skip

private theorem bump_pc (n : Cls → Nat) (e : Event) (p : Nat) :
    Code.bump cls n e (.atPc p) = n (.atPc p) + (e.pc == p).toNat := bump_cls n e (.atPc p)

private theorem skip_off {e : Event} (h1 : e.pc ≠ 2464) (h2 : e.pc ≠ 2512) :
    Mma.skipEv e = false := by
  simp [Mma.skipEv, h1, h2]

private theorem pc_off {e : Event} {p : Nat} (h : e.pc ≠ p) : (e.pc == p).toNat = 0 := by
  simp [h]

/-- A fired event at a pc is a collective exactly when the pc's instruction is a warp one. -/
private theorem source_coll {L g pc e} (src : SourceAt L g pc e) :
    Sched.isWarpColl e = isWarpAt pc := by
  obtain ⟨_, _, _, hc, fire, nu⟩ := src
  exact fired_coll hc fire nu

private theorem bump_elect (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .elect = n .elect + (isElectEv e).toNat := by
  change _ + (if isElectEv e then 1 else 0) = _; cases isElectEv e <;> rfl

private theorem bump_shfl (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .shfl = n .shfl + (Execution.isShfl e).toNat := by
  change _ + (if Execution.isShfl e then 1 else 0) = _; cases Execution.isShfl e <;> rfl

private theorem bump_poll (n : Cls → Nat) (e : Event) (p : Nat) :
    Code.bump cls n e (.poll p) = n (.poll p) + (okPollAt p e).toNat := by
  change _ + (if okPollAt p e then 1 else 0) = _; cases okPollAt p e <;> rfl

private theorem off {p : Nat} {e : Event} (h : e.pc ≠ p) : okPollAt p e=false := by
  obtain ⟨q,k⟩ := e
  change q≠p at h
  cases k <;> try rfl
  rename_i b _ _
  cases b <;> simp_all [okPollAt]

private theorem bump_copy (n : Cls → Nat) (e : Event) :
    Code.bump cls n e .copy = n .copy + (Loader.tensorEv e).toNat := by
  change _ + (if Loader.tensorEv e then 1 else 0) = _; cases Loader.tensorEv e <;> rfl

private theorem bump_winner (n : Cls → Nat) (e : Event) (l : Nat) :
    Code.bump cls n e (.winner l) = n (.winner l) + (Loader.winnerEv l e).toNat := by
  change _ + (if Loader.winnerEv l e then 1 else 0) = _; cases Loader.winnerEv l e <;> rfl

/-- The twelve preload sites and the eight loader sites are the only tensor copies. -/
private def tensorPcs : List Nat := [211,217,226,231,253,259,268,273,295,301,310,315,
  2389,2391,2394,2396,2404,2406,2410,2412]

private theorem all_tensor : OpPcsFast kernel.code tensorOp tensorPcs = true := by
  decide +kernel

private theorem tensor_off {L g pc e} (src : SourceAt L g pc e) (h : pc ∉ tensorPcs) :
    Loader.tensorEv e = false := by
  obtain ⟨t,ins,o,hc,fire,_⟩ := src
  cases hq : Loader.tensorEv e
  · rfl
  · obtain ⟨q,k⟩ := e
    cases k with
    | tensorIssue a sp => ?_
    | _ => simp [Loader.tensorEv] at hq
    have op : tensorOp ins.op = true := by
      cases test : tensorOp ins.op
      · exact (fires_notTensor (eventTmpl_notTensor test) fire a sp rfl).elim
      · rfl
    exact (h (OpPcsFast.mem all_tensor hc op)).elim

private theorem copy_on {L g p u e} (src : SourceAt L g (Loader.Site.copy p u).pc e) :
    Loader.tensorEv e = true := by
  obtain ⟨t,ins,o,hc,fire,nu⟩ := src
  obtain ⟨guard,dst,coords,code⟩ := Loader.copy_instr p u
  obtain rfl := Option.some.inj (hc.symm.trans code)
  cases o with
  | some v =>
    obtain ⟨addr,sp,ev,_,_⟩ := fires_cpTensor_issue fire
    rw [ev]; rfl
  | none =>
    rcases fires_none_ends fire with ⟨f,h⟩|exit
    · exact (nu f h).elim
    · have ret := Lib.ret_pc' code fire exit
      have no : ∀ p b, (Loader.Site.copy p b).pc ∉ Lib.retPcs := by decide
      exact (no p u ret).elim

private theorem loader_off (s : Loader.Site) (h : s.isCopy = false) : s.pc ∉ tensorPcs := by
  cases s with
  | copy p u => simp [Loader.Site.isCopy] at h
  | _ => first | decide +kernel | (rename_i p; revert p; decide +kernel)

/-- The startup's collective is made once the site is the entry of a role. -/
def startPhase : Startup.Site → Nat
  | .enter _ => 1
  | _ => 0

/-- The startup makes no poll, no final collective and no broadcast of the loop. -/
private def Quiet (n : Cls → Nat) : Prop :=
  n (.atPc 2550) + n (.atPc 2551) + n (.poll 2374) + n (.poll 2462) + n (.poll 2510) + n .skip = 0

private theorem first {L g d dn e n}
    (prev : Balance (g%L.block/32) (laneOf L g) (startPhase d.site) 0 0 0 0 0 0 n ∧ Quiet n)
    (src : SourceAt L g d.site.pc e) (hn : Startup.succ L g d e=some (some dn)) :
    Balance (g%L.block/32) (laneOf L g) (startPhase dn.site) 0 0 0 0 0 0 (Code.bump cls n e) ∧
      Quiet (Code.bump cls n e) := by
  have atPc := observed src
  have pc := atPc.pc_eq
  obtain ⟨s,t,x,w⟩ := d
  have quiet (s : Startup.Site) : s.pc≠2374 ∧ s.pc≠2462 ∧ s.pc≠2510 ∧
      Lib.canElect s.pc=false ∧ s.pc ∉ tensorPcs ∧ s.pc≠2464 ∧ s.pc≠2512 ∧ s.pc≠2550 ∧
      s.pc≠2551 ∧ isWarpAt s.pc = decide (s=.shfl) := by
    cases s <;> first | decide +kernel | (rename_i b; cases b <;> decide +kernel)
  obtain ⟨h1,h2,h3,he,h4,h5,h6,h7,h8,wa⟩ := quiet s
  have noVote := atPc.election he
  have bonus : startPhase dn.site = startPhase s + (Execution.isShfl e).toNat := by
    by_cases hs : s=.shfl
    · subst s
      obtain ⟨p,k⟩ := e
      cases k with
      | shfl _ _ _ _ v _ =>
        simp only [Startup.succ] at hn
        split at hn <;> cases hn
        rfl
      | _ => cases hn
    have ns : Lib.canShuffle s.pc=false := by
      cases s <;> first | contradiction | decide +kernel
    rw [atPc.shuffle ns]
    cases s <;> simp only [Startup.succ] at hn
    all_goals repeat' split at hn
    all_goals try contradiction
    all_goals cases hn; rfl
  have coll : Sched.isWarpColl e = Execution.isShfl e := by
    rw [source_coll src, wa]
    by_cases hs : s=.shfl
    · subst s
      obtain ⟨p,k⟩ := e
      cases k with
      | shfl _ _ _ _ _ _ => rfl
      | _ => cases hn
    · have ns : Lib.canShuffle s.pc=false := by
        cases s <;> first | contradiction | decide +kernel
      rw [atPc.shuffle ns]
      simp [hs]
  dsimp only at prev ⊢
  obtain ⟨⟨a,b,c,a2,b2,c2⟩,q⟩ := prev
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
  · intro hw
    rw [bump_elect,noVote,bump_poll,off (pc ▸ h1)]
    exact a hw
  · intro hw
    have z := b hw
    rw [bump_shfl,bump_poll,bump_poll,off (pc ▸ h2),off (pc ▸ h3)]
    change n .shfl+0=startPhase s+n (.poll 2462)+n (.poll 2510) at z
    simp only [Bool.toNat_false,Nat.add_zero]; omega
  · intro hw
    have z := c hw
    rw [bump_copy,bump_winner,tensor_off src (pc ▸ h4),Loader.winner_off _ _ noVote]
    simpa using z
  · intro hw
    have z := a2 hw
    rw [bump_coll,bump_poll,off (pc ▸ h1),coll]
    simp only [Bool.toNat_false,Nat.add_zero]; omega
  · intro hw
    have z := b2 hw
    rw [bump_coll,bump_skip,bump_poll,bump_poll,bump_pc,bump_pc,off (pc ▸ h2),off (pc ▸ h3),
      skip_off (pc ▸ h5) (pc ▸ h6),pc_off (pc ▸ h7),pc_off (pc ▸ h8),coll]
    simp only [Bool.toNat_false,Nat.add_zero]; omega
  · intro h6 h7
    have z := c2 h6 h7
    rw [bump_coll,coll]
    omega
  · unfold Quiet at q ⊢
    rw [bump_pc,bump_pc,bump_poll,bump_poll,bump_poll,bump_skip,pc_off (pc ▸ h7),pc_off (pc ▸ h8),
      off (pc ▸ h1),off (pc ▸ h2),off (pc ▸ h3),skip_off (pc ▸ h5) (pc ▸ h6)]
    simp only [Bool.toNat_false,Nat.add_zero]; omega

theorem mma_poll_receipt (s : Mma.Site) (e : Event) (h : e.pc=s.pc) :
    Mma.receipt s e = ((okPollAt 2462 e).toNat,(okPollAt 2510 e).toNat) := by
  have only (s : Mma.Site) : (s.pc=2462 ↔ s=.kvWait) ∧ (s.pc=2510 ↔ s=.pWait) := by
    cases s <;> first | decide | (rename_i j; revert j; decide +kernel)
  by_cases q : s=.kvWait
  · subst s; obtain ⟨_,k⟩ := e; cases h; cases k <;> try rfl
    rename_i b _ _; cases b <;> rfl
  by_cases p : s=.pWait
  · subst s; obtain ⟨_,k⟩ := e; cases h; cases k <;> try rfl
    rename_i b _ _; cases b <;> rfl
  rw [off (h ▸ fun eq => q ((only s).1.mp eq)),off (h ▸ fun eq => p ((only s).2.mp eq))]
  cases s <;> first | contradiction | rfl

private theorem dispatch_step {warp n L g d e} (h : Balance warp (laneOf L g) 1 0 0 0 0 0 0 n)
    (src : SourceAt L g (Dispatch.Site.pc d) e) :
    Balance warp (laneOf L g) 1 0 0 0 0 0 0 (Code.bump cls n e) := by
  have atPc := observed src
  have facts (s : Dispatch.Site) : Lib.canElect s.pc=false ∧ Lib.canShuffle s.pc=false ∧
      s.pc≠2374 ∧ s.pc≠2462 ∧ s.pc≠2510 ∧ s.pc ∉ tensorPcs ∧ isWarpAt s.pc = false ∧
      s.pc≠2464 ∧ s.pc≠2512 ∧ s.pc≠2550 ∧ s.pc≠2551 := by cases s <;> decide +kernel
  obtain ⟨a,b,c,f,j,t,w,k1,k2,k3,k4⟩ := facts d
  have pc := atPc.pc_eq
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := h
  have coll : Sched.isWarpColl e = false := (source_coll src).trans w
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro hw
    rw [bump_elect,bump_poll,atPc.election a,off (pc ▸ c)]
    exact ha hw
  · intro hw
    rw [bump_shfl,bump_poll,bump_poll,atPc.shuffle b,off (pc ▸ f),off (pc ▸ j)]
    exact hb hw
  · intro hw
    rw [bump_copy,bump_winner,tensor_off src (pc ▸ t),Loader.winner_off _ _ (atPc.election a)]
    simpa using hc hw
  · intro hw
    rw [bump_coll,bump_poll,coll,off (pc ▸ c)]
    simpa using hd hw
  · intro hw
    rw [bump_coll,bump_skip,bump_poll,bump_poll,bump_pc,bump_pc,coll,skip_off (pc ▸ k1) (pc ▸ k2),
      off (pc ▸ f),off (pc ▸ j),pc_off (pc ▸ k3),pc_off (pc ▸ k4)]
    simpa using he hw
  · intro h6 h7
    rw [bump_coll,coll]
    simpa using hf h6 h7

theorem loader_coll (s : Loader.Site) : isWarpAt s.pc = s.coll := by
  cases s <;> first | decide +kernel | (rename_i p; revert p; decide +kernel) |
    (rename_i p b; revert p b; decide +kernel)

theorem mma_coll (s : Mma.Site) : isWarpAt s.pc = s.coll := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

private def ledgerAt {Q L g w x} :
    (workerCode Q L g w x).D → (Cls → Nat) → Prop
  | .inl _,n => Balance (g%L.block/32) (laneOf L g) 1 0 0 0 0 0 0 n
  | .inr ⟨.loader _,s⟩,n => Balance (g%L.block/32) (laneOf L g) 1 (Loader.owed s.site) 0
    s.site.pend (Loader.remain s.site) 0 0 n
  | .inr ⟨.mma _,s⟩,n => Balance (g%L.block/32) (laneOf L g) 1 0 (Mma.owed s.site) 0
    (Mma.remain s.site) s.site.waiting s.site.skipped n

private theorem entered {Q L g w x d n}
    (h : Balance (g%L.block/32) (laneOf L g) 1 0 0 0 0 0 0 n) :
    @ledgerAt Q L g w x (Code.enter _ _ workerEntry d) n := by
  unfold Code.enter
  split
  · rename_i i _
    cases i <;> exact h
  · exact h

private theorem returned {Q L g w x i s n} (h : @ledgerAt Q L g w x (.inr ⟨i,s⟩) n) :
    @ledgerAt Q L g w x (Code.backEnter _ _ workerEntry (workerBack Q L g w x) i s) n := by
  cases i with
  | loader =>
    unfold Code.backEnter workerBack
    by_cases hs : s.site=.dispatch
    · simp only [hs,↓reduceIte]
      apply entered
      change Balance _ _ 1 (Loader.owed s.site) 0 s.site.pend (Loader.remain s.site) 0 0 n at h
      rwa [hs] at h
    · simpa only [hs,↓reduceIte] using h
  | mma =>
    unfold Code.backEnter workerBack
    by_cases hs : s.site=.dispatch
    · simp only [hs,↓reduceIte]
      apply entered
      change Balance _ _ 1 0 (Mma.owed s.site) 0 (Mma.remain s.site) s.site.waiting s.site.skipped n
        at h
      rwa [hs] at h
    · simpa only [hs,↓reduceIte] using h

private theorem step {Q L g w x d n e dn} (h : @ledgerAt Q L g w x d n)
    (hi : workerInv Q L g w x d n) (src : SourceAt L g ((workerCode Q L g w x).pc d) e)
    (hn : (workerCode Q L g w x).next d e=some (some dn)) :
    ledgerAt dn (Code.bump cls n e) := by
  rcases d with d|⟨i,s⟩
  · change (Dispatch.next L g d e).map _ = _ at hn
    obtain ⟨o,_,hc⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨_,_,rfl⟩ := Option.map_eq_some_iff.mp hc
    exact entered (dispatch_step h src)
  · change (((workerFrag Q L g w x i).next s e).map _) = _ at hn
    obtain ⟨o,hfired,hc⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨s',rfl,rfl⟩ := Option.map_eq_some_iff.mp hc
    apply returned
    cases i with
    | loader =>
      obtain ⟨hw,_⟩ := hi
      obtain ⟨prev,_,cprev,lprev,_⟩ := h
      have bal := Loader.owed_next (observed src) hfired
      have coll := Loader.remain_next (observed src) ((source_coll src).trans (loader_coll s.site))
        hfired
      have pend := Loader.pend_next (L := L) (g := g) hfired
        (fun no => (observed src).election (Loader.canElect_off _ fun p h => no ⟨p,h⟩))
        (fun yes => by
          obtain ⟨p,u,hs⟩ : ∃ p u, s.site = .copy p u := by
            cases hs : s.site <;> first | exact ⟨_,_,rfl⟩ | (rw [hs] at yes; cases yes)
          have src' : SourceAt L g s.site.pc e := src
          rw [hs] at src'
          exact copy_on src')
        (fun no => tensor_off src (loader_off s.site no))
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · intro _
        rw [bump_elect,bump_poll]
        have z := prev hw
        omega
      · omega
      · intro _
        rw [bump_copy,bump_winner]
        have z := cprev hw
        omega
      · intro _
        rw [bump_coll,bump_poll]
        have z := lprev hw
        omega
      · intro h7; omega
      · intro h6; omega
    | mma =>
      obtain ⟨hw,_⟩ := hi
      obtain ⟨_,prev,_,_,mprev,_⟩ := h
      have bal := Mma.owed_next (observed src) hfired
      have coll := Mma.remain_next (observed src) ((source_coll src).trans (mma_coll s.site))
        hfired
      rw [mma_poll_receipt _ _ (observed src).pc_eq] at bal coll
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · omega
      · intro _
        rw [bump_shfl,bump_poll,bump_poll]
        have z := prev hw
        omega
      · intro h6; omega
      · intro h6; omega
      · intro _
        rw [bump_coll,bump_skip,bump_poll,bump_poll,bump_pc,bump_pc]
        have z := mprev hw
        omega
      · intro _ h7; omega

private def collectiveLedger (Q : Params) (L : Launch) : WorkerLedger Q L where
  startup g d n := Balance (g%L.block/32) (laneOf L g) (startPhase d.site) 0 0 0 0 0 0 n ∧ Quiet n
  worker _ _ _ := ledgerAt
  init g := by
    unfold Startup.init
    split <;> exact ⟨⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => ⟨rfl,le_rfl⟩,
      fun _ _ => rfl⟩,rfl⟩
  first _ _ _ _ _ := first
  entry _ d _ prev hs := by
    have prev := prev.1
    change Balance _ _ (startPhase d.site) _ _ _ _ _ _ _ at prev
    rw [hs] at prev
    exact prev
  step _ _ _ _ _ _ _ h hi src hn _ := step h hi src hn

theorem loader_balance {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=6) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.loader r) d n))) :
    n .elect + Loader.owed d.site = 4*n (.poll 2374) :=
  ((collectiveLedger Q L).at_worker hp hX hf hg nu hs).1 hw

theorem mma_balance {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=7) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.mma r) d n))) :
    n .shfl + Mma.owed d.site = 1+n (.poll 2462)+n (.poll 2510) := by
    obtain ⟨_,b2,_,_,_,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact b2 hw

/-- A loader thread has issued two copies for each election it won, less those still owed. -/
theorem loader_copies {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=6) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.loader r) d n))) :
    n .copy + d.site.pend = 2*n (.winner (laneOf L g)) := by
    obtain ⟨_,_,b3,_,_,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact b3 hw

/-- A loader thread has made a collective for each step of its successful polls, less those still
owed, and the startup's. -/
theorem loader_coll_count {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=6) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.loader r) d n))) :
    n .coll + Loader.remain d.site = 1 + 9*n (.poll 2374) := by
    obtain ⟨_,_,_,b4,_,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact b4 hw

/-- An MMA thread has made four collectives for each successful poll, the final two, and the
startup's, less those still owed; a broadcast of no 7 is counted. -/
theorem mma_coll_count {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=7) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.mma r) d n))) :
    n .coll + Mma.remain d.site + n .skip = 1 + 4*(n (.poll 2462) + n (.poll 2510)) +
      n (.atPc 2550) + n (.atPc 2551) + d.site.waiting := by
    obtain ⟨_,_,_,_,b5,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact (b5 hw).1

/-- An MMA thread at a site entered after a broadcast that received no 7 has counted one. -/
theorem mma_skipped {Q L m X g k w x r d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=7) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (workerState w x (.mma r) d n))) :
    d.site.skipped ≤ n .skip := by
  obtain ⟨_,_,_,_,b5,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
  exact (b5 hw).2

/-- A dispatch thread of the loader's warp has made a collective for each step of its polls. -/
theorem loader_dispatch_count {Q L m X g k w x d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=6) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) :
    n .coll = 1 + 9*n (.poll 2374) := by
    obtain ⟨_,_,_,b4,_,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact b4 hw

/-- A dispatch thread of the MMA's warp has made four collectives for each successful poll, the
final two and the startup's; a broadcast of no 7 is counted. -/
theorem mma_dispatch_count {Q L m X g k w x d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (hw : g%L.block/32=7) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) :
    n .coll + n .skip = 1 + 4*(n (.poll 2462) + n (.poll 2510)) + n (.atPc 2550) +
      n (.atPc 2551) := by
    obtain ⟨_,_,_,_,b5,_⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    have := (b5 hw).1
    omega

/-- A dispatch thread of another warp has made only the startup's collective. -/
theorem idle_coll_count {Q L m X g k w x d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (h6 : g%L.block/32≠6) (h7 : g%L.block/32≠7) (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.dispatch w x),.inl d⟩,n))) :
    n .coll = 1 := by
    obtain ⟨_,_,_,_,_,b6⟩ := ((collectiveLedger Q L).at_worker hp hX hf hg nu hs)
    exact b6 h6 h7

/-- The startup has made its one collective once it is at the entry of a role. -/
theorem startup_coll_count {Q L m X g k d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (nu : Frame.NoUbBefore X g k)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (.inl d,n))) :
    n .coll = startPhase d.site := by
  obtain ⟨⟨a,b,c,a2,b2,c2⟩,q⟩ := (collectiveLedger Q L).at_startup hp hX hf hg nu hs
  unfold Quiet at q
  by_cases h6 : g%L.block/32=6
  · have := a2 h6; omega
  by_cases h7 : g%L.block/32=7
  · have := b2 h7; omega
  have := c2 h6 h7; omega

end PTX.Kernels.InklingRelDecode.Proof
