-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainFirstRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDrainRelinquish
import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotCursor
import Kernels.TmlFa4Fwd.Flow.Code.Part042
import Kernels.TmlFa4Fwd.Flow.Code.Part043

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (drainRoots signedWord)

private theorem drainBallotArgs (l : Launch) (g : Nat)
    {base count part heads cta : Nat} (hPrefix : part ≤ count) (hCount : count < 2^31)
    (hHead : heads < 2^31) (hCta : cta < 2^31) (hEnd : base+count*heads < 2^31) :
    Seg kernel [] l g 4 2752
      [(7214,b32 count),(7139,b32 heads),(7216,b32 (base+count*heads)),
        (7213,b32 part),(1072,b32 cta)] 2756
      [(435,.pred (decide (base+part*heads ≤ cta)))] := by
  have hMul := Nat.mul_le_mul_right heads hPrefix
  have hBase : base < 2^31 := by omega
  have hProd : count*heads < 2^31 := by omega
  have hPre : part < 2^31 := by omega
  have hPrefixWork : base+part*heads < 2^31 := by omega
  intro t ht
  seg_fp ht using
    first
    | norm_cmp
    | (simp only [compare,Option.getD_some,← BitVec.ofNat_mul,
        truncBits_ofNat (show count < 2^32 by omega) (by decide),
        truncBits_ofNat (show heads < 2^32 by omega) (by decide),
        truncBits_ofNat (show part < 2^32 by omega) (by decide),
        truncBits_ofNat (show cta < 2^32 by omega) (by decide)]
       norm_cmp)

private theorem drainTerminalGate {l : Launch} {g first batch : Nat} {t : TState}
    {F : List (Nat × Value)} (hf : first < 2^31) (hb : batch < 2^31)
    (ht : At t 2750 F) (hFirst : t.regs 7215 = some (b32 first))
    (hBatch : t.regs 7149 = some (b32 batch))
    (hKeep : ((kernel.code.drop 2750).take 2).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if batch ≤ first then 2763 else 2752) F := by
  have hSeg : Seg kernel [] l g 1 2750 [(7215,b32 first),(7149,b32 batch)] 2751
      [(434,.pred (decide (batch ≤ first)))] := by
    intro s hs
    seg_fp hs using simp only [compare,Option.getD_some,
      truncBits_ofNat (show first < 2^32 by omega) (by decide),
      truncBits_ofNat (show batch < 2^32 by omega) (by decide),
      signedWord hf,signedWord hb,ge_iff_le,Int.ofNat_le]
  obtain ⟨v,hv,hV⟩ := hSeg.apply (ht.mono ⟨hFirst,hBatch,trivial⟩)
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2751 _ hV hV.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep ht (by decide) (by decide) hKeep
    (by decide +kernel) (run_comp hv hu)
  exact ⟨u,hPath,by simpa only [decide_eq_true_eq] using hU.mono hF⟩

private def drainIndexFrame (p : Params) (first lane : Nat) : List (Nat × Value) :=
  [(7213,b32 (prefixWindow (groupLaneTiles p first) 32 lane)),
    (7212,b32 (groupLaneTiles p first lane))]

private theorem drainBallotLocal {p : Params} {l : Launch} {m : Mem0} {g first : Nat}
    (hp : Pre p l m) (hg : g < l.threads) (hf : first < p.batch) {t : TState}
    (ht : At t 2750 (activeDrainSelectedFrame p l g first)) :
    let part := prefixWindow (groupLaneTiles p first) 32 (laneOf l g)
    let base := tilePrefix p first*p.heads
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2756 ((435,.pred (decide (base+part*p.heads ≤ g/l.block)))::
        drainIndexFrame p first (laneOf l g)) := by
  let xs := groupLaneTiles p first
  let lane := laneOf l g
  let base := tilePrefix p first*p.heads
  let cta := g/l.block
  let part := prefixWindow xs 32 lane
  let group := prefixWindow xs 32 31
  let limit := tilePrefix p (min p.batch (first+31))*p.heads
  have hb := hp.shape.2.1
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hGroup := hp.groupWindow_signed hf.le (show 31 < 32 by decide) 32
  change group < 2^31 at hGroup
  have hPart : part ≤ group := by
    rw [show group = ∑ i ∈ Finset.range 32, xs i from prefixWindow_warp _ (by decide)]
    exact prefixWindow_le_warp xs 32 hl
  have hSum : base+group*p.heads = limit := by
    have h := congrArg (·*p.heads) (groupTiles_eq p hf.le (by decide : 32 ≤ 32))
    have hCount : group = ∑ i ∈ Finset.range 32, xs i := prefixWindow_warp _ (by decide)
    rw [hCount]
    simpa only [show min 31 32 = 31 by decide,Nat.add_mul,base,limit,xs] using h
  have hFit := hp.prefixWork_signed (Nat.min_le_left p.batch (first+31))
  change limit < 2^31 at hFit
  have hCta : cta < 2^31 := (NamedBar.cta_lt hg).trans hp.grid.2.2
  obtain ⟨v,hPath,hV⟩ := drainTerminalGate (l := l) (g := g) (hf.trans hb) hb ht
    (holds_lookup ht.2.2.2.2 rfl) (holds_lookup ht.2.2.2.2 rfl) (by
      change ((kernel.code.drop 2750).take 2).all
        (fun i => [7212,7213,7214,7216,7215,7149,7139,1180,7506,1072].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel)
  rw [ite_eq_right (Nat.not_le_of_lt hf)] at hV
  have hSeg := drainBallotArgs l g hPart hGroup hp.heads_signed hCta (hSum.symm ▸ hFit)
  rw [hSum] at hSeg
  obtain ⟨u,hu,hU⟩ := hSeg.apply (hV.mono ⟨holds_lookup hV.2.2.2.2 rfl,
    holds_lookup hV.2.2.2.2 rfl,holds_lookup hV.2.2.2.2 rfl,holds_lookup hV.2.2.2.2 rfl,
    holds_lookup hV.2.2.2.2 rfl,trivial⟩)
  have hCursor : At v 2752 (drainIndexFrame p first lane) := hV.mono
    ⟨holds_lookup hV.2.2.2.2 rfl,holds_lookup hV.2.2.2.2 rfl,trivial⟩
  obtain ⟨hLocal,hKeep⟩ := activeDrainLocalKeep hCursor (by decide) (by decide)
    (by change ((kernel.code.drop 2752).take 4).all
          (fun i => [7213,7212].all fun r => !(writesRegs i.op).contains r) = true
        decide +kernel)
    (by decide +kernel) hu
  exact ⟨u,hPath.trans hLocal,hU.mono ⟨hU.2.2.2.2.1,hKeep⟩⟩

private theorem drainSelectedBallotEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles votes : Nat} (hg : g < l.threads)
    (hf : first < p.batch) (hLo : tilePrefix p first*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (min p.batch (first+31))*p.heads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2750
      (fun i => activeDrainSelectedFrame p l (warpLane l g i) first) shuffles votes ends) :
    ∃ n < 31, Nonempty (SchedulerWarpReached l X g 2756
      (fun i => (435,.pred (decide (i<n)))::drainIndexFrame p first i) shuffles votes ends) := by
  obtain ⟨b,⟨hFirst,hGroup,hBatch,hLower,hUpper⟩,_⟩ := groupContains_request p hLo hHi
  let n := b-first
  refine ⟨n,by dsimp [n]; omega,?_⟩
  apply cur.advanceLocal
  intro i hi
  have hs := Step.sameWarp_lane (show l.block%32 = 0 by rw [hp.block]) hg hi
  obtain ⟨u,hu,hU⟩ := drainBallotLocal hp hs.1.1.2.1 hf (cur.checkpoint i hi)
  have hOwner : warpLane l g i/l.block = g/l.block := hs.1.1.2.2.symm
  change (g-laneOf l g+i)/l.block = g/l.block at hOwner
  rw [hs.2,hOwner] at hU
  have hPrefix : (tilePrefix p first*p.heads +
      prefixWindow (groupLaneTiles p first) 32 i*p.heads ≤ g/l.block) ↔ i < n := by
    rw [← Nat.add_mul,prefixWindow_warp _ hi]
    exact (groupBallot_iff p hFirst hGroup hBatch hi hLower hUpper).trans (by dsimp [n]; omega)
  have hEq : decide _ = decide (i<n) := Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq] using hPrefix)
  rw [hEq] at hU
  exact ⟨u,hu,hU⟩

private theorem drainPopcount {l : Launch} {g n : Nat} {t : TState} {F : List (Nat × Value)}
    (hn : n < 31) (ht : At t 2757 ((2678,b32 (2^n-1))::F))
    (hKeep : ((kernel.code.drop 2757).take 3).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if n = 0 then 2762 else 2760) ((1200,b32 n)::F) := by
  have hp : 2^n < 2^32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hMask : 2^n-1 < 2^32 := by omega
  have hMask64 : 2^n-1 < 2^64 := by omega
  have hZero : 2^n-1 = 0 ↔ n = 0 := by
    cases n with
    | zero => decide
    | succ n =>
      have hOne := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
      omega
  have hc := ballotPrefixPopcount (by omega : n ≤ 32)
  have hs : Seg kernel [] l g 2 2757 [(2678,b32 (2^n-1))] 2759
      [(436,.pred (decide (n=0))),(1200,b32 n)] := by
    intro s hs
    seg_fp hs using
      simp only [b32,truncBits_ofNat hMask (by decide),toNat_ofNat_lt hMask64,hc,
        compare,Option.getD_some,show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 by decide,
        Int.ofNat_inj,hZero]
  obtain ⟨v,hv,hV⟩ := hs.apply (ht.mono ⟨ht.2.2.2.2.1,trivial⟩)
  have ht' := ht.mono ht.2.2.2.2.2
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2759 _ hV hV.2.2.2.2.1 (by simp)
  obtain ⟨hPath,hRegs⟩ := activeDrainLocalKeep ht' (by decide) (by decide) hKeep
    (by decide +kernel) (run_comp hv hu)
  have hFrame : Holds u.regs ((1200,b32 n)::F) := ⟨hU.2.2.2.2.2.1,hRegs⟩
  exact ⟨u,hPath,by simpa only [decide_eq_true_eq] using hU.mono hFrame⟩

private theorem drainIndexTemplate {l : Launch} {g src index dst n : Nat} {s : TState}
    {v : Value} (hr : s.regs src = some v) (hIndex : s.regs index = some (b32 n))
    (hBlock : l.block%32 = 0) (hn : n < 2^32) (hv : v.bytes = 4) :
    shflTmpl l g s .idx dst none (.reg src) (.reg index) (.imm 31) (.imm (-1)) =
      .shfl .idx v n 31 (fun word _ => next (setReg s dst word)) := by
  have hBits : readBits l g s 32 (.reg index) = .ok (BitVec.ofNat 64 n) := by
    simp only [readBits,readReg,hIndex,b32,bind,Except.bind,pure,Except.pure,
      truncBits_ofNat hn (by decide : 32 ≤ 64)]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hClamp : readBits l g s 32 (.imm 31) = .ok (BitVec.ofNat 64 31) := rfl
  simp [shflTmpl,readValue,readReg,hr,hBits,hBlock,hv,pure,Except.pure,hMask,hClamp,
    toNat_ofNat_lt (show n < 2^64 by omega)]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem drainFinalIndex {g first n shuffles votes : Nat} (hg : g < l.threads) (hn : n < 31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2762
      (fun i => (1200,b32 n)::drainIndexFrame p first i) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2763 (fun _ => []) (shuffles+1) votes ends) := by
  let word i := b32 (groupLaneTiles p first i)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨mid⟩ := cur.consumeShuffle (dst := 2681) hp hMax hg .idx word
    (fun _ => n) (fun _ => 31) (by
      intro lane _ pair hm
      simp [drainIndexFrame] at hm
      rcases hm with rfl | rfl | rfl <;> (dsimp only; decide)) (by
      intro i hi
      have h := cur.checkpoint i hi
      have hr : (cur.state i).regs 7212 = some (word i) := h.2.2.2.2.2.2.1
      have hnReg := h.2.2.2.2.1
      rw [out_eq_core (by rw [h.1]; decide) (by rw [h.1]; decide),
        out_event h.2.2.2.1 (h.1.symm ▸ Flow.code_2762) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g i) (cur.state i) .idx 2681 none
        (.reg 7212) (.reg 1200) (.imm 31) (.imm (-1))) = _
      rw [drainIndexTemplate hr hnReg hBlock (show n < 2^32 by omega) rfl])
  apply mid.advanceLocal
  intro i hi
  exact ⟨_,.refl,(mid.checkpoint i hi).mono trivial⟩

private theorem drainPreviousIndex {g first n shuffles votes : Nat} (hg : g < l.threads)
    (hn : n < 31) (hpos : 0 < n) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2760
      (fun i => (1200,b32 n)::drainIndexFrame p first i) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2762
      (fun i => (1200,b32 n)::drainIndexFrame p first i) (shuffles+1) votes ends) := by
  let F i := (1200,b32 n)::drainIndexFrame p first i
  have hPrepare : Nonempty (SchedulerWarpReached l X g 2761
      (fun i => (2679,b32 (n-1))::F i) shuffles votes ends) := by
    apply cur.advanceLocal
    intro i hi
    have hSeg : Seg kernel [] l (warpLane l g i) 1 2760 [(1200,b32 n)] 2761
        [(2679,b32 (n-1))] := by
      intro t ht
      seg_fp ht using norm_bits
    have h := cur.checkpoint i hi
    obtain ⟨u,hu,hU⟩ := hSeg.apply (h.mono ⟨h.2.2.2.2.1,trivial⟩)
    obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep h (by decide) (by decide)
      (by change ((kernel.code.drop 2760).take 1).all
            (fun ins => [1200,7213,7212].all fun r => !(writesRegs ins.op).contains r) = true
          decide +kernel) (by decide +kernel) hu
    exact ⟨u,hPath,hU.mono ⟨hU.2.2.2.2.1,hKeep⟩⟩
  obtain ⟨ready⟩ := hPrepare
  let word i := b32 (prefixWindow (groupLaneTiles p first) 32 i)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨mid⟩ := ready.consumeShuffle (dst := 2680) hp hMax hg .idx word
    (fun _ => n-1) (fun _ => 31) (by
      intro lane _ pair hm
      simp [F,drainIndexFrame] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> (dsimp only; decide)) (by
      intro i hi
      have h := ready.checkpoint i hi
      have hr : (ready.state i).regs 7213 = some (word i) := h.2.2.2.2.2.2.1
      have hnReg := h.2.2.2.2.1
      rw [out_eq_core (by rw [h.1]; decide) (by rw [h.1]; decide),
        out_event h.2.2.2.1 (h.1.symm ▸ Flow.code_2761) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g i) (ready.state i) .idx 2680 none
        (.reg 7213) (.reg 2679) (.imm 31) (.imm (-1))) = _
      rw [drainIndexTemplate hr hnReg hBlock (show n-1 < 2^32 by omega) rfl])
  apply mid.advanceLocal
  intro i hi
  have h := mid.checkpoint i hi
  exact ⟨_,.refl,h.mono h.2.2.2.2.2.2⟩

private theorem drainRelinquishAtWarp {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 2763 F shuffles votes ends) :
    MmaRelinquishPrefix l X g := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hself : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  apply relinquishOfDrainCursor hp hMax hg hw (F := F lane)
  refine ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
    ?_,?_,cur.checkpoint lane hl,?_,?_,?_⟩
  · simpa only [hself] using cur.bounded lane hl
  · simpa only [hself] using cur.released lane hl
  · simpa only [hself] using cur.recorded lane hl
  · simpa only [hself] using cur.continuation lane hl
  · simpa only [hself] using cur.localSteps lane hl

/-- The selected terminal group executes the real ballot and required index exchanges
before its MMA warp records the relinquish collective. -/
theorem activeDrainRelinquishOfSelected {g first shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hf : first < p.batch) (hLo : tilePrefix p first*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (min p.batch (first+31))*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2750
      (fun i => activeDrainSelectedFrame p l (warpLane l g i) first) shuffles votes ends) :
    MmaRelinquishPrefix l X g := by
  obtain ⟨n,hn,⟨b⟩⟩ := drainSelectedBallotEntry hp hg hf hLo hHi cur
  obtain ⟨mid⟩ := b.consumePrefixBallot (dst := 2678) hp hMax hg (by omega : n ≤ 32) (by
      intro i _ pair hm
      simp [drainIndexFrame] at hm
      rcases hm with rfl | rfl | rfl <;> (dsimp only; decide)) (by
      intro i hi
      have ht := b.checkpoint i hi
      have hReg := ht.2.2.2.2.1
      have hb : l.block%32 = 0 := by rw [hp.block]
      rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
        out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_2756) rfl rfl]
      change Out.ev (voteTmpl l (warpLane l g i) (b.state i) 2678 435 false (.imm (-1))) = _
      simp [voteTmpl,readPred,readReg,hReg,hb,bind,Except.bind,pure,Except.pure,b32]
      rfl)
  have hPop : Nonempty (SchedulerWarpReached l X g (if n=0 then 2762 else 2760)
      (fun i => (1200,b32 n)::drainIndexFrame p first i) shuffles (votes+1) ends) := by
    apply mid.advanceLocal
    intro i hi
    have h := mid.checkpoint i hi
    exact drainPopcount (g := warpLane l g i) hn (h.mono ⟨h.2.2.2.2.1,h.2.2.2.2.2.2⟩)
      (by change ((kernel.code.drop 2757).take 3).all
            (fun ins => [7213,7212].all fun r => !(writesRegs ins.op).contains r) = true
          decide +kernel)
  by_cases hz : n = 0
  · rw [ite_eq_left hz] at hPop
    obtain ⟨c⟩ := hPop
    obtain ⟨done⟩ := drainFinalIndex hp hMax hg hn c
    exact drainRelinquishAtWarp hp hMax hg hw done
  · rw [ite_eq_right hz] at hPop
    obtain ⟨c⟩ := hPop
    obtain ⟨prev⟩ := drainPreviousIndex hp hMax hg hn (Nat.pos_of_ne_zero hz) c
    obtain ⟨done⟩ := drainFinalIndex hp hMax hg hn prev
    exact drainRelinquishAtWarp hp hMax hg hw done

/-- An exhausted terminal search skips request selection and arrives at real relinquish. -/
theorem activeDrainRelinquishOfExhausted {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2750
      (fun _ => activeDrainExhaustedFrame p) shuffles votes ends) :
    MmaRelinquishPrefix l X g := by
  have hDone : Nonempty (SchedulerWarpReached l X g 2763 (fun _ => []) shuffles votes ends) := by
    apply cur.advanceLocal
    intro i hi
    have h := cur.checkpoint i hi
    obtain ⟨u,hu,hU⟩ := drainTerminalGate (g := warpLane l g i) hp.shape.2.1 hp.shape.2.1
      h h.2.2.2.2.1 h.2.2.2.2.2.1 (by
        change ((kernel.code.drop 2750).take 2).all
          (fun ins => [7215,7149].all fun r => !(writesRegs ins.op).contains r) = true
        decide +kernel)
    rw [ite_eq_left (Nat.le_refl p.batch)] at hU
    exact ⟨u,hu,hU.mono trivial⟩
  obtain ⟨done⟩ := hDone
  exact drainRelinquishAtWarp hp hMax hg hw done

end PTX.Kernels.TmlFa4Fwd.Mma
