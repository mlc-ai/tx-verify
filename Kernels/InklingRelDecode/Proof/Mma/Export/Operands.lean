-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Mma.Export.EmptyCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Lemmas.Flow.NthEv
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.OperandWords
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotBulk
import Lemmas.Cluster.Unit

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Proof PTX.Flow

private def positions := (List.finRange 8).map qkPc ++ (List.finRange 8).map pvPc

private theorem checked : OpPcsFast kernel.code tcMmaOp positions=true := by decide +kernel

private theorem site_form (s : Site) (hit : s.pc ∈ positions) :
    (∃ j,s=.qk j) ∨ ∃ j,s=.pv j := by
  cases s <;> first | exact .inl ⟨_,rfl⟩ | exact .inr ⟨_,rfl⟩ | exact absurd hit (by decide +kernel)

private def InTile (L : Launch) (op : TcMma.Operand) (l : Loc) : Prop :=
  l.space=.shared ∧ match op with
    | .a => L.sharedBase+196608≤l.addr ∧ l.addr<L.sharedBase+212992
    | .b => L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608

private theorem q_tile {Q L m i s} (hp : Pre Q L m) (j : Fin 8)
    (desc : s.descriptor=Lib.qkDesc) (atmem : s.aTmem=none)
    (a : s.a=⟨qWord L j*16,0,1024,0,false,false,.b128⟩)
    (b : s.b=⟨kWord L i j*16,0,1024,0,false,false,.b128⟩)
    {op idx l} (atByte : TcMma.OperandSpec.byteLoc s op idx=some l) :
    InTile L op l ∧ l.cta=s.lowCta ∧ (op=.b → Iface.InSlot L (i%3) l.addr) := by
  have align := hp.sharedAlignment
  have bound := j.isLt
  cases op with
  | a =>
    let base := L.sharedBase+196608+8192*(j.val/4)
    have start : qWord L j*16=base+32*(j.val%4) := by dsimp [qWord,qLo,base]; omega
    rw [start] at a
    obtain ⟨sp,cta,lo,hi⟩ := Lib.qk_a_foot desc (B := base) (by dsimp [base]; omega)
      (by omega) a atmem atByte
    exact ⟨⟨sp,by dsimp [base] at lo hi; exact ⟨by omega,by omega⟩⟩,cta,fun h => by cases h⟩
  | b =>
    let base := L.sharedBase+32768*(i%3)+16384*(j.val/4)
    have start : kWord L i j*16=base+32*(j.val%4) := by dsimp [kWord,kLo,base]; omega
    rw [start] at b
    obtain ⟨sp,cta,lo,hi⟩ := Lib.qk_b_foot desc (B := base) (by dsimp [base]; omega)
      (by omega) b atByte
    refine ⟨⟨sp,by dsimp [base] at lo hi; exact ⟨by omega,by omega⟩⟩,cta,fun _ => ?_⟩
    dsimp [base] at lo hi
    unfold Iface.InSlot
    omega

private theorem v_tile {Q L m i s} (hp : Pre Q L m) (j : Fin 8)
    (desc : s.descriptor=Lib.pvDesc) (atmem : ∃ a,s.aTmem=some a)
    (b : s.b=⟨vWord L i j*16,16384,1024,0,false,false,.b128⟩)
    {op idx l} (atByte : TcMma.OperandSpec.byteLoc s op idx=some l) :
    InTile L op l ∧ l.cta=s.lowCta ∧ (op=.b → Iface.InSlot L ((i-1)%3) l.addr) := by
  cases op with
  | a =>
    obtain ⟨a,eq⟩ := atmem
    rw [Lib.pv_a_none eq] at atByte
    cases atByte
  | b =>
    have align := hp.sharedAlignment
    let base := L.sharedBase+98304+32768*((i-1)%3)
    have start : vWord L i j*16=base+2048*j.val := by dsimp [vWord,vLo,base]; omega
    rw [start] at b
    obtain ⟨sp,cta,lo,hi⟩ := Lib.pv_b_foot desc (B := base) (by dsimp [base]; omega) j.isLt b atByte
    refine ⟨⟨sp,by dsimp [base] at lo hi; exact ⟨by omega,by omega⟩⟩,cta,fun _ => ?_⟩
    dsimp [base] at lo hi
    unfold Iface.InSlot
    omega

public theorem owner {Q L m g ctas lo hi} (hp : Pre Q L m) (hg : g<L.threads)
    (grp : L.ctaGroup (g/L.block) .one=some ctas) (first : ctas.head?=some lo)
    (last : ctas.getLast?=some hi) : lo=g/L.block ∧ hi=g/L.block := by
  have hs : ∀ k, (L.clusterPlaces k).shape=⟨1,1,1⟩ := by
    intro k
    rw [hp.clusterPlaces,hp.clusterNctaid]
    rfl
  have cta : g/L.block<L.grid := by
    rw [Launch.threads,hp.block] at hg
    rw [hp.block]
    omega
  have hc : g/L.block<L.nclusters := hp.nclusters ▸ cta
  rw [Launch.ctaGroup_one,Launch.rankOfCta_unit hs hc,Launch.peerCta_unit hs hc cta] at grp
  obtain rfl : ctas=[g/L.block] := by simpa using grp.symm
  simp only [List.head?_cons,List.getLast?_singleton,Option.some.injEq] at first last
  exact ⟨first.symm,last.symm⟩

/-- Each QK or PV issue decodes a single-CTA descriptor and sits among the MMA sites after the
second publication. Its operand bytes lie in the issuer's CTA: shared B operands in the KV
rings and any shared A operand in the query tile. -/
public theorem operands_all {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    (s.descriptor=Lib.qkDesc ∨ s.descriptor=Lib.pvDesc) ∧ (2462≤pc ∧ pc≤2553) ∧
    ∀ op idx l, s.byteLoc op idx=some l → l.space=.shared ∧ l.cta=g/L.block ∧
      (match op with
        | .a => L.sharedBase+196608≤l.addr ∧ l.addr<L.sharedBase+212992
        | .b => L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608) := by
  obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have hit := OpPcsFast.mem checked code (fires_tcMma_op fire rfl)
  have range : ∀ p ∈ positions, 2422<p ∧ p<2557 := by decide +kernel
  have narrow : ∀ p ∈ positions, 2462≤p ∧ p≤2553 := by decide +kernel
  obtain ⟨w,x,r,d,n,hs,pcEq⟩ := mma_state hp hX hf he (fun _ => nofun)
    (range _ hit).1 (range _ hit).2
  obtain ⟨t,ins,o,ht,_,hc,ff⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (fun _ => nofun)
  have hg := Frame.lt_of_get hX he
  change pc=d.site.pc at pcEq
  subst pc
  obtain ⟨site,i,v⟩ := d
  change site.pc ∈ positions at hit
  suffices core : (s.descriptor=Lib.qkDesc ∨ s.descriptor=Lib.pvDesc) ∧
      ∀ op idx l, s.byteLoc op idx=some l → l.space=.shared ∧ l.cta=g/L.block ∧
        (match op with
          | .a => L.sharedBase+196608≤l.addr ∧ l.addr<L.sharedBase+212992
          | .b => L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608) from
    ⟨core.1,narrow _ hit,core.2⟩
  rcases site_form site hit with ⟨j,rfl⟩|⟨j,rfl⟩
  · obtain ⟨desc,atmem,a,b,ctas,grp,lo,hi⟩ := q_operands hp j ht hc ff
    obtain ⟨own,_⟩ := owner hp hg grp lo hi
    refine ⟨.inl desc,fun _ _ _ hb => ?_⟩
    obtain ⟨⟨sp,tile⟩,cta,_⟩ := q_tile hp j desc atmem a b hb
    exact ⟨sp,cta.trans own,tile⟩
  · obtain ⟨desc,atmem,-,b,ctas,grp,lo,hi⟩ := v_operands hp j ht hc ff
    obtain ⟨own,_⟩ := owner hp hg grp lo hi
    refine ⟨.inr desc,fun _ _ _ hb => ?_⟩
    obtain ⟨⟨sp,tile⟩,cta,_⟩ := v_tile hp j desc atmem b hb
    exact ⟨sp,cta.trans own,tile⟩

/-- Each QK or PV issue decodes a single-CTA descriptor. Shared B operands
read the KV rings, and any shared A operand reads the query tile. -/
public theorem operands {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    (s.descriptor=Lib.qkDesc ∨ s.descriptor=Lib.pvDesc) ∧
    ∀ op idx l, s.byteLoc op idx=some l → l.space=.shared ∧
      (match op with
        | .a => L.sharedBase+196608≤l.addr ∧ l.addr<L.sharedBase+212992
        | .b => L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608) := by
  obtain ⟨desc,_,tile⟩ := operands_all hp hX hf he
  exact ⟨desc,fun op idx l hb => by
    obtain ⟨sp,_,rng⟩ := tile op idx l hb
    exact ⟨sp,rng⟩⟩

/-- **The slot an MMA reads**: the B operand bytes of a QK or PV issue lie in one ring slot
`σ` of the issuer's CTA, whose ready polls exceed its empty commits. A commit of ordinal at most
`T` precedes the issue, and a ready poll of slot `σ` is made at the issue's position `m ≥ T`:
with the commits' distinct ordinals this gives the issue's commits `+ 1 ≤` polls. -/
public theorem read_slot {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩) :
    g%L.block/32 = 7 ∧ Elected ((X.tr g).take k) (laneOf L g) ∧ ∃ σ : Fin 3,
      (∀ idx l, s.byteLoc .b idx = some l → l.cta=g/L.block ∧ Iface.InSlot L σ.val l.addr) ∧
      ∃ T n, T ≤ n ∧ n < pollRound 2462 ((X.tr g).take k) ∧ n%3 = σ.val ∧
        ∀ j, j<k → ∀ sp, X.get (g,j) = some ⟨2546,.tc (.commit sp)⟩ →
          pollRound 2510 ((X.tr g).take j) ≤ T := by
  obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have hit := OpPcsFast.mem checked code (fires_tcMma_op fire rfl)
  have range : ∀ p ∈ positions, 2422<p ∧ p<2557 := by decide +kernel
  have hpc : 2422 < pc ∧ pc < 2557 := range _ hit
  obtain ⟨w0,x0,r0,d0,n0,hs0,inv0⟩ := worker_event hp hX hf he (fun _ => nofun)
    (by change 2344 < pc; omega) (by change pc < 2557; omega)
    (by change pc ≠ 2422; omega)
  have warp : g%L.block/32 = 7 := by
    cases r0 with
    | mma => exact inv0.1
    | loader =>
      have wrong : g%L.block/32 = 6 := inv0.1
      have := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs0 (fun _ => nofun)
      change pc = d0.site.pc at this
      have h : ∀ s : Loader.Site, ¬ (2422 < s.pc ∧ s.pc < 2557) := by
        intro s
        cases s <;> first | decide | (rename_i p; fin_cases p <;> decide) |
          (rename_i p b; fin_cases p <;> cases b <;> decide)
      exact absurd (this ▸ range _ hit) (h _)
  refine ⟨warp,elected_issue hp hX hf he (by
      have all : ∀ p ∈ positions, p ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
          2530,2533,2535,2537,2539,2541,2543,2545] := by decide +kernel
      exact all _ hit),?_⟩
  obtain ⟨w,x,d,t,ins,o,ht,loop,pcEq,hc,ff,hq,hp'⟩ := mma_event hp hX hf warp he
    (fun _ => nofun) (by change 2422 < pc; exact (range _ hit).1)
    (by change pc < 2557; exact (range _ hit).2)
  have hg := Frame.lt_of_get hX he
  obtain ⟨site,i,v⟩ := d
  change pc = site.pc at pcEq
  subst pc
  change site.pc ∈ positions at hit
  have mono {T : Nat} (le : pollRound 2510 ((X.tr g).take k) ≤ T) (j : Nat) (hj : j<k) :
      pollRound 2510 ((X.tr g).take j) ≤ T :=
    (countP_take_mono (okPollAt 2510) (X.tr g) hj.le).trans le
  rcases site_form site hit with ⟨j,rfl⟩|⟨j,rfl⟩
  · obtain ⟨desc,atmem,a,b,ctas,grp,lo,hi⟩ := q_operands hp j ht hc ff
    obtain ⟨own,_⟩ := owner hp hg grp lo hi
    change pollRound 2462 _ = i+1 at hq
    change pollRound 2510 _ = i-1 at hp'
    refine ⟨⟨i%3,Nat.mod_lt _ (by omega)⟩,fun idx l hb => ?_,i-1,i,by omega,by omega,rfl,
      fun j' hj' _ _ => mono hp'.le j' hj'⟩
    obtain ⟨_,cta,slot⟩ := q_tile hp j desc atmem a b hb
    exact ⟨cta.trans own,slot rfl⟩
  · obtain ⟨desc,atmem,-,b,ctas,grp,lo,hi⟩ := v_operands hp j ht hc ff
    obtain ⟨own,_⟩ := owner hp hg grp lo hi
    change pollRound 2462 _ = min (i+1) (low v) at hq
    change pollRound 2510 _ = i at hp'
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    refine ⟨⟨(i-1)%3,Nat.mod_lt _ (by omega)⟩,fun idx l hb => ?_,i-1,i-1,le_rfl,by omega,rfl,
      fun j' hj' sp get => ?_⟩
    · obtain ⟨_,cta,slot⟩ := v_tile hp j desc atmem b hb
      exact ⟨cta.trans own,slot rfl⟩
    · have := Export.commit_ord_lt hp hX hf words warp get hj' he
        (by
          have all : ∀ j : Fin 8, pvPc j ∈ [2530,2533,2535,2537,2539,2541,2543,2545] := by
            decide +kernel
          exact all j)
      omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
