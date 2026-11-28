-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Mma.Export.ShuffleTotal
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.FollowStartup
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
import Kernels.InklingRelDecode.Flow.Code.Part038
import Kernels.InklingRelDecode.Flow.Code.Part039
import Lemmas.Flow.ShflOps

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Proof PTX.Flow PTX.Frame

private theorem region {Q L m X g k pc md a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (warp : g%L.block/32=7)
    (he : X.get (g,k)=some ⟨pc,.shfl md a b c recv ok⟩)
    (pos : 0<((X.tr g).take k).countP Execution.isShfl) : pc=2464 ∨ pc=2512 := by
  have static : kernel.code.zipIdx.all (fun (i,p) => !i.op.isShfl ||
      (p==17 || (27<p && p<574) || (574<p && p<2331) || (2565≤p && p<2853) ||
        p==2464 || p==2512)) := by decide +kernel
  have hg := lt_of_get hX he
  obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg) hX he
    (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  obtain ⟨_,ins,_,_,inv,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  have loc : pc=(thread Q L g).pc st := EventFrame.fires_source_pc fire
  have code := loc ▸ hc
  have sh := fires_shfl_op fire (by rfl)
  have allowed := List.all_eq_true.mp static (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr code)
  simp only [sh,Bool.not_true,Bool.false_or,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,
    decide_eq_true_eq] at allowed
  have fits := loc ▸ state_role st
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases allowed with ((((rfl|pro)|soft)|epi)|qk)|pv
  · obtain ⟨d,n,rfl⟩ := fits.startup (by decide)
    have atpc : 17=d.site.pc := loc
    have only (s : Startup.Site) : 17=s.pc → s=.shfl := by
      cases s <;> first | decide | (rename_i e; cases e <;> decide)
    have active : Startup.enterOf d=none := by simp [Startup.enterOf,only _ atpc]
    have zero := startup_ordinal hp hX len.le active hs
    omega
  · obtain ⟨_,_,_,rfl⟩ := fits.prologue pro.1 pro.2
    have low : g%L.block<128 := (reached_table hf hg (noUbBefore_of_get hX he) hs).2.1
    omega
  · obtain ⟨_,_,_,_,rfl⟩ := fits.softmax soft.1 soft.2
    have low := data_lane hp hX hf hg (noUbBefore_of_get hX he) hs; omega
  · obtain ⟨_,_,_,_,rfl⟩ := fits.epilogue epi.1 epi.2 inv
    have low := data_lane hp hX hf hg (noUbBefore_of_get hX he) hs; omega
  · exact .inl qk
  · exact .inr pv

private theorem sent {Q L m X g k pc md a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (warp : g%L.block/32=7)
    (he : X.get (g,k)=some ⟨pc,.shfl md a b c recv ok⟩) (sites : pc=2464 ∨ pc=2512) :
    a=b32 7 := by
  obtain ⟨w,x,d,t,ins,o,hat,_,pos,hc,fire,_,_⟩ := mma_event hp hX hf warp he (by simp)
    (by change 2422<pc; omega) (by change pc<2557; omega)
  have only (s : Site) : (s.pc=2464 → s=.qkShfl) ∧ (s.pc=2512 → s=.pvShfl) := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨s,i,v⟩ := d
  change pc=s.pc at pos
  have hb : L.block%32=0 := by rw [hp.block]
  obtain ⟨_,_,_,_,regs⟩ := hat
  have key (h : 464 ∈ Flow.live s.pc) : t.regs 464=some (b32 (g%L.block/32)) :=
    holds_mem regs (mem_factsFrom h)
  rcases sites with rfl|rfl
  · obtain rfl := (only s).1 pos.symm
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2464)
    have reg := key (by decide : 464 ∈ Flow.live 2464)
    rw [warp] at reg
    obtain ⟨_,_,eq⟩ := fires_shflTmpl (mode := .idx) (d := 546) (p := none)
      (a := .reg 464) (b := .imm 0) (c := .imm 31) (mask := .imm (-1))
      (g := g) (t := t) (av := b32 7) rfl
      (by simp [readValue,readReg,reg,pure,Except.pure]) rfl rfl rfl hb rfl fire
    exact (Kind.shfl.inj (congrArg Event.kind eq)).2.1
  · obtain rfl := (only s).2 pos.symm
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2512)
    have reg := key (by decide : 464 ∈ Flow.live 2512)
    rw [warp] at reg
    obtain ⟨_,_,eq⟩ := fires_shflTmpl (mode := .idx) (d := 563) (p := none)
      (a := .reg 464) (b := .imm 0) (c := .imm 31) (mask := .imm (-1))
      (g := g) (t := t) (av := b32 7) rfl
      (by simp [readValue,readReg,reg,pure,Except.pure]) rfl rfl rfl hb rfl fire
    exact (Kind.shfl.inj (congrArg Event.kind eq)).2.1

private theorem ordinal {Q L m X g k pc md a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (warp : g%L.block/32=7)
    (he : X.get (g,k)=some ⟨pc,.shfl md a b c recv ok⟩) (site : pc=2464 ∨ pc=2512) :
    let ord := ((X.tr g).take k).countP Execution.isShfl
    0<ord ∧ ord<1+2*Lib.blocksOf Q L (g/L.block) := by
  obtain ⟨w,x,r,d,n,hs,pcEq⟩ := mma_state hp hX hf he (by simp)
    (by change 2422<pc; omega) (by change pc<2557; omega)
  have hg := lt_of_get hX he
  have nu := noUbBefore_of_get hX he
  obtain ⟨inv,_,ref,q,p,-⟩ := reached_table hf hg nu hs
  have loop : Inv d := inv.1
  have bal := mma_balance hp hX hf hg warp nu hs
  have num : n .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
  have only (s : Site) : (s.pc=2464 → s=.qkShfl) ∧ (s.pc=2512 → s=.pvShfl) := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨s,i,v⟩ := d
  change pc=s.pc at pcEq
  rcases site with rfl|rfl
  · obtain rfl := (only _).1 pcEq.symm
    change i<low v ∧ _ at loop
    change n (.poll 2462)=i+1 at q
    change n (.poll 2510)=i-1 at p
    have lim : low v=Lib.blocksOf Q L (g/L.block) := ref_count ref rfl
    change n .shfl+1=1+n (.poll 2462)+n (.poll 2510) at bal
    dsimp only; omega
  · obtain rfl := (only _).2 pcEq.symm
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    change n (.poll 2462)=min (i+1) (low v) at q
    change n (.poll 2510)=i at p
    have lim : low v=Lib.blocksOf Q L (g/L.block) := ref_count ref rfl
    change n .shfl+1=1+n (.poll 2462)+n (.poll 2510) at bal
    dsimp only; omega

public theorem broadcast_seven {Q L m X g k pc md a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨pc,.shfl md a b c recv ok⟩)
    (site : pc=2464 ∨ pc=2512) : recv=b32 7 := by
  let n := ((X.tr g).take k).countP Execution.isShfl
  have ⟨pos,lt⟩ := ordinal hp hX hf warp he site
  have hb : L.block%32=0 := by rw [hp.block]
  have src := Step.shflSource_lt md (show laneOf L g<32 from Nat.mod_lt _ (by decide)) b c
  obtain ⟨_,hw,cta,_,_⟩ := lane_facts hb (lt_of_get hX he) warp src
  obtain ⟨_,hit|ex⟩ := hX.shfl _ _ n _ _ _ _ _ _ _ he ⟨⟨_,_,_,_,_,_,_,he⟩,rfl⟩
  · obtain ⟨j,p,b',c',r',o',rank,get⟩ := hit
    have pos' := rank.2
    apply sent hp hX hf hw get
    exact region hp hX hf hw get (pos' ▸ pos)
  · obtain ⟨j,p,get,late⟩ := ex
    have total := exited_shuffles hp hX hf words (NoUbLane.of_exit hX get) hw get
    rw [cta] at total
    dsimp [n] at late
    omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
