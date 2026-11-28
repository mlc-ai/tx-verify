-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
public import Kernels.InklingRelDecode.Proof.Lib.TcVec
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Softmax.Export.RoundBar
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import all Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.BaseWord
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.TcCount
import Kernels.InklingRelDecode.Proof.Epilogue.Tmem
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Lemmas.Flow.TcStAddr
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Flow.Code.Part020
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part036
import Kernels.InklingRelDecode.Flow.Code.Part040
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section

/-! # What a collective `tcgen05` event shows, as the lanes of a warp must agree on it

A data lane's collective event is a function of the position, the round `i`, and the word its
warp's broadcast delivered (`Lib.opStatic`): the broadcast is the shuffle of the round (of the
epilogue) the lane made at the round's ordinal (`Lib.ShflAt`). The Tensor Memory object's base is
recorded as zero (`Iface.BaseRead`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Frame PTX.Proof PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat}

private theorem word_b32 (n : Nat) : (Lib.word (b32 n)).toNat = n % 2^32 := by
  unfold Lib.word b32 truncBits Value.regBits
  have := Nat.mod_lt n (show 0 < 2^32 by norm_num)
  simp
  omega

private theorem soft_base (x b : Nat) (h : x + b < 2^32) :
    Softmax.Control.basePlus (Softmax.Control.basePlus (b32 0) x) b = b32 (x+b) := by
  have e1 : Softmax.Control.basePlus (b32 0) x = b32 x := by
    show Softmax.Control.u32 ((Lib.word (b32 0)).toNat + x) = b32 x
    rw [word_b32]
    simp only [Softmax.Control.u32,Nat.zero_mod,Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [e1]
  show Softmax.Control.u32 ((Lib.word (b32 x)).toNat + b) = b32 (x+b)
  rw [word_b32]
  simp only [Softmax.Control.u32]
  rw [Nat.mod_eq_of_lt (by omega : x < 2^32),Nat.mod_eq_of_lt h]

private theorem epi_base (b : Nat) (h : 256 + b < 2^32) :
    Lib.addBase (Lib.addBase (b32 0) 256) b = b32 (256+b) := by
  have e1 : Lib.addBase (b32 0) 256 = b32 256 := by
    simpa using Lib.addBase_bits 0 256
  rw [e1]
  have := Lib.addBase_bits 256 b
  rw [Nat.mod_eq_of_lt (by omega : 256 < 2^32)] at this
  rw [this,Nat.mod_eq_of_lt h]

private theorem offset_lt (w : Value) : Lib.bcastOffset w < 2^23 := by
  unfold Lib.bcastOffset
  omega

private theorem ld_static {A : List Assumption} {t : TState} {pc ta a : Nat} {o : Option TState}
    {ds : List Nat} {sh : TcShape} {kk : TcKind} (hr : t.regs ta = some (b32 a)) (ha : a < 2^32)
    (fire : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) ⟨pc,.tc kk⟩ o)
    (hd : isTcData ⟨pc,.tc kk⟩ = true) (hw : A.any (·.tcLdWait t.pc) = false) :
    tcStatic kk = .ld a [] sh := by
  obtain ⟨vals,hev⟩ := fires_tcLd_addr hr ha fire hd hw
  simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at hev
  subst hev
  rfl

private theorem st_static {A : List Assumption} {t : TState} {pc ta a : Nat} {o : Option TState}
    {ss : List Opnd} {sh : TcShape} {kk : TcKind} (hr : t.regs ta = some (b32 a)) (ha : a < 2^32)
    (fire : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) ⟨pc,.tc kk⟩ o)
    (hd : isTcData ⟨pc,.tc kk⟩ = true) (hnp : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcStWaitLd t.pc) = false) : tcStatic kk = .st a [] sh := by
  obtain ⟨vals,hev⟩ := fires_tcSt_addr hr ha fire hd hnp hw
  simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at hev
  subst hev
  rfl

private theorem soft_reg {t : TState} {ent : Softmax.Control.Entry} {g i : Nat}
    {v : Softmax.Control.Carry} {site : Softmax.Site} {r : Nat} (zero : ent.base = b32 0)
    (regs : Holds t.regs (factsFrom (Softmax.Control.ctlLive site.pc)
      (Softmax.Control.valueOf ent L g ⟨site,i,v⟩)))
    (live : r ∈ Softmax.Control.ctlLive site.pc) (hr : r = 1676 ∨ r = 1611) :
    t.regs r = some (b32 ((if r = 1676 then i%2*128 else 256) + Lib.bcastOffset v.base)) := by
  have reg := holds_mem regs (mem_factsFrom live)
  have lt : (Lib.word v.base).toNat % 4 * 2^21 < 2^23 := by omega
  rcases hr with rfl|rfl
  · have : Softmax.Control.valueOf ent L g ⟨site,i,v⟩ 1676 =
        Softmax.Control.basePlus (Softmax.Control.basePlus ent.base (i%2*128))
          ((Lib.word v.base).toNat % 4 * 2^21) := by
      simp [Softmax.Control.valueOf]
    rw [this,zero,soft_base _ _ (by omega)] at reg
    simpa [Lib.bcastOffset] using reg
  · have : Softmax.Control.valueOf ent L g ⟨site,i,v⟩ 1611 =
        Softmax.Control.basePlus (Softmax.Control.basePlus ent.base 256)
          ((Lib.word v.base).toNat % 4 * 2^21) := by
      simp [Softmax.Control.valueOf]
    rw [this,zero,soft_base _ _ (by omega)] at reg
    simpa [Lib.bcastOffset] using reg

private theorem site_of_pc (s : Softmax.Site) :
    (s.pc=1265 → s=.ldS) ∧ (s.pc=2260 → s=.ldO) ∧ (s.pc=2328 → s=.stO) ∧
      (s.pc=1009 → s=.tmemSt) := by
  cases s <;> first
    | (refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> first | rfl | (exfalso; revert h; decide +kernel))
    | (rename_i j; refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> exfalso <;> revert h <;> revert j <;>
        decide +kernel)

/-- The address a Softmax collective at an address position shows: the buffer offset of the round
and the broadcast word's offset. -/
private theorem soft_static {w n pc} {kk : TcKind} {ent : Softmax.Control.Entry}
    {d : Softmax.Control.D} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (base : Iface.BaseRead L X) (he : X.get (g,j) = some ⟨pc,.tc kk⟩)
    (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hs : stateAt (thread Q L) X g j = some (some (softState w ent d n)))
    (hk : j ≤ (X.tr g).length) (nub : NoUbBefore X g j) (hpc : pc = d.site.pc)
    (addr : pc = 1265 ∨ pc = 2260 ∨ pc = 2328 ∨ pc = 1009) :
    tcStatic kk = Lib.opStatic L (g/L.block) pc d.i d.held.base := by
  have zero : ent.base = b32 0 := recorded_zero hp hX base hk nub hs
  have nu := no_ub tc
  obtain ⟨t,ins,o,ht,-,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs nu
  obtain ⟨hpcT,-,-,-,regs⟩ := ht
  have hd : isTcData ⟨pc,.tc kk⟩ = true := by
    rw [Lib.tcdata_event hX he nu]
    simp only [Lib.dataPcs,List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq]
    omega
  obtain ⟨site,i,v⟩ := d
  obtain ⟨s1,s2,s3,s4⟩ := site_of_pc site
  rcases addr with rfl|rfl|rfl|rfl
  · obtain rfl := s1 hpc.symm
    change kernel.code[1265]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1265)
    have reg := soft_reg (r := 1676) zero regs (by decide +kernel) (.inl rfl)
    simp only [ite_true] at reg
    have lt : i%2*128 + Lib.bcastOffset v.base < 2^32 := by
      unfold Lib.bcastOffset; omega
    have hw : Assumptions.all.any (·.tcLdWait t.pc) = false := by
      have : t.pc = 1265 := hpcT
      rw [this]; decide +kernel
    rw [ld_static reg lt fire hd hw]
    simp [Lib.opStatic]
  · obtain rfl := s2 hpc.symm
    change kernel.code[2260]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2260)
    have reg := soft_reg (r := 1611) zero regs (by decide +kernel) (.inr rfl)
    simp only [show (1611 = 1676) = False from by decide,ite_false] at reg
    have lt : 256 + Lib.bcastOffset v.base < 2^32 := by
      unfold Lib.bcastOffset; omega
    have hw : Assumptions.all.any (·.tcLdWait t.pc) = false := by
      have : t.pc = 2260 := hpcT
      rw [this]; decide +kernel
    rw [ld_static reg lt fire hd hw]
    simp [Lib.opStatic]
  · obtain rfl := s3 hpc.symm
    change kernel.code[2328]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2328)
    have reg := soft_reg (r := 1611) zero regs (by decide +kernel) (.inr rfl)
    simp only [show (1611 = 1676) = False from by decide,ite_false] at reg
    have lt : 256 + Lib.bcastOffset v.base < 2^32 := by
      unfold Lib.bcastOffset; omega
    have hw : Assumptions.all.any (·.tcStWaitLd t.pc) = false := by
      have : t.pc = 2328 := hpcT
      rw [this]; decide +kernel
    rw [st_static reg lt fire hd (fun _ => nofun) hw]
    simp [Lib.opStatic]
  · obtain rfl := s4 hpc.symm
    change kernel.code[1009]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1009)
    have reg := soft_reg (r := 1676) zero regs (by decide +kernel) (.inl rfl)
    simp only [ite_true] at reg
    have lt : i%2*128 + Lib.bcastOffset v.base < 2^32 := by
      unfold Lib.bcastOffset; omega
    have hw : Assumptions.all.any (·.tcStWaitLd t.pc) = false := by
      have : t.pc = 1009 := hpcT
      rw [this]; decide +kernel
    rw [st_static reg lt fire hd (fun _ => nofun) hw]
    simp [Lib.opStatic]

private theorem wait_static {t : TState} {pc : Nat} {o : Option TState} {ins : Instr}
    {kk : TcKind} (hb : L.block % 32 = 0) (hc : kernel.code[pc]? = some ins)
    (fire : Fires pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc,.tc kk⟩ o)
    (w : pc = 1298 ∨ pc = 2261 ∨ pc = 2608 ∨ pc = 2329 ∨ pc = 1010) :
    tcStatic kk = if pc = 2329 ∨ pc = 1010 then .waitSt else .waitLd := by
  rcases w with rfl|rfl|rfl|rfl|rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1298)
    have := fires_tcWaitLd hb fire
    simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at this
    subst this; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2261)
    have := fires_tcWaitLd hb fire
    simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at this
    subst this; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2608)
    have := fires_tcWaitLd hb fire
    simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at this
    subst this; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2329)
    have := fires_tcWaitSt_kind hb fire
    simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at this
    subst this; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1010)
    have := fires_tcWaitSt_kind hb fire
    simp only [Event.mk.injEq,Kind.tc.injEq,true_and] at this
    subst this; rfl

private theorem epi_site_of_pc (s : Epilogue.Site) :
    (s.pc=2607 → s=.load) ∧ (s.pc=2608 → s=.waitLd) ∧ (s.pc=2851 → s=.dealloc) := by
  cases s <;> first
    | (refine ⟨?_,?_,?_⟩ <;> intro h <;> first | rfl | (exfalso; revert h; decide +kernel))
    | (rename_i j; refine ⟨?_,?_,?_⟩ <;> intro h <;> exfalso <;> revert h <;> revert j <;>
        decide +kernel)

/-- What an epilogue collective shows: the load's address, the wait, or the deallocation. -/
private theorem epi_static {w n pc} {kk : TcKind} {ent : Softmax.Control.Entry}
    {d : Epilogue.Control.D} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) (he : X.get (g,j) = some ⟨pc,.tc kk⟩)
    (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hs : stateAt (thread Q L) X g j = some (some (epiState w ent d n)))
    (hk : j ≤ (X.tr g).length) (nub : NoUbBefore X g j) (hpc : pc = d.site.pc)
    (epi : pc = 2607 ∨ pc = 2608 ∨ pc = 2851) :
    tcStatic kk = Lib.opStatic L (g/L.block) pc ent.limit d.received := by
  have zero : ent.base = b32 0 := recorded_zero hp hX base hk nub hs
  have nu := no_ub tc
  have hg := lt_of_get hX he
  obtain ⟨t,ins,o,ht,-,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs nu
  obtain ⟨hpcT,-,-,-,regs⟩ := ht
  obtain ⟨site,v⟩ := d
  obtain ⟨s1,s2,s3⟩ := epi_site_of_pc site
  rcases epi with rfl|rfl|rfl
  · obtain rfl := s1 hpc.symm
    change kernel.code[2607]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2607)
    have hd : isTcData ⟨2607,.tc kk⟩ = true := by
      rw [Lib.tcdata_event hX he nu]
      simp [Lib.dataPcs]
    have reg := holds_mem regs (mem_factsFrom
      (val := Epilogue.Control.valueOf (epiEntry ent (g%L.block)) L g v)
      (show 1827 ∈ Epilogue.Control.ctlLive 2607 by decide +kernel))
    change t.regs 1827 = some (Epilogue.Control.valueOf (epiEntry ent (g%L.block)) L g v 1827)
      at reg
    have val : Epilogue.Control.valueOf (epiEntry ent (g%L.block)) L g v 1827 =
        Lib.addBase (Lib.addBase ent.base 256) ((Lib.word v).toNat % 4 * 2^21) := by
      simp [Epilogue.Control.valueOf,epiEntry]
    have lt : (Lib.word v).toNat % 4 * 2^21 < 2^23 := by omega
    rw [val,zero,epi_base _ (by omega)] at reg
    have hw : Assumptions.all.any (·.tcLdWait t.pc) = false := by
      have : t.pc = 2607 := hpcT
      rw [this]; decide +kernel
    rw [ld_static reg (by omega) fire hd hw]
    simp [Lib.opStatic,Lib.bcastOffset]
  · obtain rfl := s2 hpc.symm
    change kernel.code[2608]? = some ins at hc
    have := wait_static (hb := by simp [hp.block]) hc fire (by simp)
    rw [this]
    simp [Lib.opStatic]
  · obtain rfl := s3 hpc.symm
    have res : isTmemOp ⟨2851,.tc kk⟩ = true := by
      have := Lib.tcColl_event hX he nu
      rw [tc] at this
      simpa [Lib.dataPcs] using this.symm
    obtain ⟨_,grp,dst,act,eq⟩ := tmemOp_resource res
    simp only [Event.mk.injEq,Kind.tc.injEq] at eq
    obtain ⟨-,rfl⟩ := eq
    change kernel.code[2851]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2851)
    obtain ⟨a,h1,h2,h3,-⟩ := Epilogue.dealloc_kind fire rfl
    subst h1 h2 h3
    have zero := dealloc_zero hp hX hf base hg he
    simp [tcStatic,Lib.opStatic,zero]

private theorem wait_at {s : (thread Q L g).D} {pc : Nat} {kk : TcKind}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,j) = some ⟨pc,.tc kk⟩) (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hs : stateAt (thread Q L) X g j = some (some s)) (hpc : pc = (thread Q L g).pc s)
    (w : pc = 1298 ∨ pc = 2261 ∨ pc = 2608 ∨ pc = 2329 ∨ pc = 1010) :
    tcStatic kk = if pc = 2329 ∨ pc = 1010 then .waitSt else .waitLd := by
  obtain ⟨t,ins,o,-,-,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX he hs (no_ub tc)
  rw [← hpc] at hc fire
  exact wait_static (by simp [hp.block]) hc fire w

/-- **What a collective `tcgen05` event shows.** The event's static part is a function of the
position, the round `i` and the word `w` of the broadcast; at an address position the broadcast is
the lane's shuffle of the round's ordinal. -/
public theorem tc_operand (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {pc : Nat} {kk : TcKind}
    (he : X.get (g,j) = some ⟨pc,.tc kk⟩) (tc : isTcColl ⟨pc,.tc kk⟩ = true) :
    ∃ i w, (∃ R e', Lib.dataPcs.map (fun P => ((X.tr g).take j).countP (fun x => x.pc == P)) =
        Lib.tcVec pc i R e') ∧
      (pc ∈ Lib.addrPcs → Lib.ShflAt X g (Lib.bcastPc pc)
        (1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase i) w) ∧
      tcStatic kk = Lib.opStatic L (g/L.block) pc i w := by
  obtain ⟨s,hs,inv,hi,hk,nub,wh⟩ := tc_where hp hX hf he tc
  have nu := no_ub tc
  rcases wh with ⟨st,n',eq,hpc,res⟩|⟨w,ent,d,n',eq,hpc,loop⟩|⟨w,ent,d,n',eq,hpc,where_⟩
  · cases eq
    have cnt (P : Nat) : ((X.tr g).take j).countP (fun x => x.pc == P) = n' (.atPc P) :=
      (fcount hs (.atPc P)).symm
    change Zero n' at inv
    refine ⟨0,b32 0,⟨0,0,?_⟩,fun h => ?_,?_⟩
    · rw [Lib.tcVec_off (hpc ▸ startup_tc_pc st.site)]
      rw [List.map_congr_left (g := fun _ => 0) (fun P hP => by
        rw [cnt P]; exact inv P (List.mem_cons_of_mem _ hP))]
      simp [Lib.dataPcs]
    · exfalso
      simp only [Lib.addrPcs,List.mem_cons,List.not_mem_nil,or_false] at h
      omega
    · have ev := start_ev hp hX he hs nu
      obtain ⟨site,t,x,w⟩ := st
      rcases res with rfl|rfl
      all_goals
        cases site <;> simp [Startup.Ev,Startup.Site.pc] at ev hpc
        all_goals first
          | (subst ev; simp [tcStatic,Lib.opStatic])
          | (rename_i r; cases r <;> simp [Startup.Entry.pc] at hpc)
  · cases eq
    obtain ⟨cntInv,vis⟩ := inv
    have cnt (P : Nat) : ((X.tr g).take j).countP (fun x => x.pc == P) = n' (.atPc P) :=
      (fcount hs (.atPc P)).symm
    refine ⟨d.i,d.held.base,⟨n' (.atPc 2326),0,?_⟩,fun h => ?_,?_⟩
    · rw [List.map_congr_left (g := Softmax.softCount d.site d.i (n' (.atPc 2326)))
        (fun P hP => by rw [cnt P]; exact cntInv P hP),hpc]
      exact soft_vec d.site _ _ (hpc ▸ loop)
    · obtain ⟨s1,s2,s3,s4⟩ := site_of_pc d.site
      simp only [Lib.addrPcs,List.mem_cons,List.not_mem_nil,or_false,Lib.loopTcPcs] at h loop
      have held : Softmax.held d.site = true := by
        rcases h with rfl|rfl|rfl|rfl|rfl
        · rw [s1 hpc.symm]; rfl
        · rw [s2 hpc.symm]; rfl
        · rw [s3 hpc.symm]; rfl
        · rw [s4 hpc.symm]; rfl
        · omega
      have := shfl_held hp hX hk hs nub held
      have b : Lib.bcastPc pc = 1261 := by
        simp only [Lib.bcastPc]
        split_ifs with e
        · omega
        · rfl
      rw [b]
      exact this
    · simp only [Lib.loopTcPcs,List.mem_cons,List.not_mem_nil,or_false] at loop
      by_cases a : pc = 1265 ∨ pc = 2260 ∨ pc = 2328 ∨ pc = 1009
      · rw [soft_static hp hX base he tc hs hk nub hpc a]
      · have w : pc = 1298 ∨ pc = 2261 ∨ pc = 2329 ∨ pc = 1010 := by omega
        rw [wait_at hp hX he tc hs hpc (by omega)]
        rcases w with rfl|rfl|rfl|rfl <;> simp [Lib.opStatic]
  · cases eq
    obtain ⟨cntInv,live⟩ := inv
    have cnt (P : Nat) : ((X.tr g).take j).countP (fun x => x.pc == P) = n' (.atPc P) :=
      (fcount hs (.atPc P)).symm
    refine ⟨ent.limit,d.received,
      ⟨n' (.atPc 2326),if (epiEntry ent (g%L.block)).skip then 0 else 1,?_⟩,fun h => ?_,?_⟩
    · rw [List.map_congr_left (g := fun P => Softmax.softCount .epilogue ent.limit
        (n' (.atPc 2326))
        P+Epilogue.epiCount (epiEntry ent (g%L.block)).skip d.site P)
        (fun P hP => by rw [cnt P]; exact cntInv P hP),hpc]
      exact epi_vec _ d.site _ _ (fun h => live (.inr (.inr h))) (hpc ▸ where_)
    · have p2607 : pc = 2607 := by
        simp only [Lib.addrPcs,List.mem_cons,List.not_mem_nil,or_false] at h
        omega
      subst p2607
      obtain ⟨s1,-,-⟩ := epi_site_of_pc d.site
      have site := s1 hpc.symm
      obtain ⟨-,load,-⟩ := shfl_epi hp hX hk hs nub
      have := load site
      simpa [Lib.bcastPc] using this
    · exact epi_static hp hX hf base he tc hs hk nub hpc where_

/-- **The round of a softmax tensor collective at an address position**: the loads of the score
and the accumulator (pc 1265, 2260) and the stores of the probabilities and the accumulator
(pc 1009, 2328) of round `i` follow `i + 1` successful polls of `s_ready`, `i` of `o_done` (`i - 1`
before the accumulator wait), and show the address of the round. -/
theorem soft_round (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {pc : Nat} {kk : TcKind}
    (he : X.get (g,j) = some ⟨pc,.tc kk⟩) (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hpc : pc = 1265 ∨ pc = 2260 ∨ pc = 1009 ∨ pc = 2328) :
    ∃ i w, pollRound 1257 ((X.tr g).take j) = i+1 ∧
      pollRound 2239 ((X.tr g).take j) = (if pc = 1265 then i-1 else i) ∧
      Softmax.Export.mandatory ((X.tr g).take j) + 2 = 4*i + Lib.softPos pc i ∧
      tcStatic kk = Lib.opStatic L (g/L.block) pc i w ∧ ((pc = 2260 ∨ pc = 2328) → 0 < i) := by
  obtain ⟨s,hs,inv,hi,hk,nub,wh⟩ := tc_where hp hX hf he tc
  rcases wh with ⟨st,n',eq,hp',h1115⟩|⟨w,ent,d,n',eq,hp',loop⟩|⟨w,ent,d,n',eq,hp',h26⟩
  · omega
  swap
  · omega
  · cases eq
    have hg := Frame.lt_of_get hX he
    have ref := (reached_table hf hg nub hs).2
    change Softmax.Ref _ d (softCounts n') at ref
    have cnt (key : Cls) : n' key = ((X.tr g).take j).countP (cls key) := fcount hs key
    have sc := congrArg Softmax.Cnt.s ref.ledger
    have oc := congrArg Softmax.Cnt.o ref.ledger
    change n' (.poll 1257) = d.i + d.site.afterS.toNat at sc
    change n' (.poll 2239) = (if d.site.afterO then d.i else d.i-1) at oc
    obtain ⟨s1,s2,s3,s4⟩ := site_of_pc d.site
    have site : d.site = .ldS ∨ d.site = .ldO ∨ d.site = .tmemSt ∨ d.site = .stO := by
      rcases hpc with h|h|h|h
      · exact .inl (s1 (hp'.symm.trans h))
      · exact .inr (.inl (s2 (hp'.symm.trans h)))
      · exact .inr (.inr (.inl (s4 (hp'.symm.trans h))))
      · exact .inr (.inr (.inr (s3 (hp'.symm.trans h))))
    have nz : ∀ x, x = d.site → d.site.afterS = true := fun x hx => by
      rcases site with h|h|h|h <;> rw [h] <;> rfl
    have aS := nz _ rfl
    rw [aS,cnt] at sc
    rw [cnt] at oc
    have fixed := soft_fixed_total hp hX hk hs nub
    simp only [cnt] at fixed
    have pos : Softmax.syncPosition d.site d.i = Lib.softPos pc d.i := by
      rcases hpc with h|h|h|h
      · rw [s1 (hp'.symm.trans h)]
        simp [h, Softmax.syncPosition, Lib.softPos]
      · rw [s2 (hp'.symm.trans h)]
        simp [h, Softmax.syncPosition, Lib.softPos]
      · rw [s4 (hp'.symm.trans h)]
        simp [h, Softmax.syncPosition, Lib.softPos]
      · rw [s3 (hp'.symm.trans h)]
        simp [h, Softmax.syncPosition, Lib.softPos]
    refine ⟨d.i,d.held.base,?_,?_,?_,?_,?_⟩
    · change pollRound 1257 _ = _ at sc
      simpa using sc
    · change pollRound 2239 _ = _ at oc
      rw [oc]
      rcases hpc with h|h|h|h
      · rw [s1 (hp'.symm.trans h)]; simp [h, Softmax.Site.afterO]
      · rw [s2 (hp'.symm.trans h)]; simp [h, Softmax.Site.afterO]
      · rw [s4 (hp'.symm.trans h)]; simp [h, Softmax.Site.afterO]
      · rw [s3 (hp'.symm.trans h)]; simp [h, Softmax.Site.afterO]
    · simp only [Softmax.fixedCount, pos] at fixed
      exact fixed
    · rw [soft_static hp hX base he tc hs hk nub hp' (by omega)]
    · intro h
      refine ref.late ?_
      rcases h with h|h
      · rw [s2 (hp'.symm.trans h)]; rfl
      · rw [s3 (hp'.symm.trans h)]; rfl

/-- **The round of a softmax store**: the probability store (pc 1009) and the rescale store
(pc 2328) of round `i` follow `i + 1` successful polls of `s_ready` and `i` of `o_done`, and show
the address of the round. -/
public theorem st_round (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {pc : Nat} {kk : TcKind}
    (he : X.get (g,j) = some ⟨pc,.tc kk⟩) (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hpc : pc = 1009 ∨ pc = 2328) :
    ∃ i w, pollRound 1257 ((X.tr g).take j) = i+1 ∧ pollRound 2239 ((X.tr g).take j) = i ∧
      Softmax.Export.mandatory ((X.tr g).take j) + 2 = 4*i + (if pc = 1009 then 3 else 2) ∧
      tcStatic kk = Lib.opStatic L (g/L.block) pc i w := by
  obtain ⟨i,w,a,b,c,d,-⟩ := soft_round hp hX hf base he tc (by omega)
  refine ⟨i,w,a,?_,?_,d⟩
  · rw [b]; rcases hpc with rfl|rfl <;> simp
  · rw [c]; rcases hpc with rfl|rfl <;> simp [Lib.softPos]

/-- **The round of a softmax load**: the score load (pc 1265) of round `i` has the round's
polls, `i - 1` of `o_done`, and sits at `4 i - 2` mandatory rendezvous (none in round zero); the
accumulator load (pc 2260) at `4 i`. -/
public theorem ld_round (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {pc : Nat} {kk : TcKind}
    (he : X.get (g,j) = some ⟨pc,.tc kk⟩) (tc : isTcColl ⟨pc,.tc kk⟩ = true)
    (hpc : pc = 1265 ∨ pc = 2260) :
    ∃ i w, pollRound 1257 ((X.tr g).take j) = i+1 ∧
      pollRound 2239 ((X.tr g).take j) = (if pc = 1265 then i-1 else i) ∧
      Softmax.Export.mandatory ((X.tr g).take j) + 2 =
        4*i + (if pc = 1265 then (if i = 0 then 2 else 0) else 2) ∧
      tcStatic kk = Lib.opStatic L (g/L.block) pc i w ∧ (pc = 2260 → 0 < i) := by
  obtain ⟨i,w,a,b,c,d,e⟩ := soft_round hp hX hf base he tc (by omega)
  exact ⟨i,w,a,b,by rw [c]; simp [Lib.softPos]; rcases hpc with rfl|rfl <;> simp,d,
    fun h => e (.inl h)⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
