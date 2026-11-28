-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Entry
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Lemmas.Flow.CtlStepsU
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000

/-- A rebuilt request is carried as data. Invalid bytes leave a concrete fault at the load. -/
theorem record {Q L g w} {d : D} (dn : Value → D) {a : MemAccess} {r : Nat}
    (hc : kernel.code[d.site.pc]? = some ⟨none,.mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [r])
    (free : r ∉ ctlLive d.site.pc) (sub : d.site.sub = 0) (sub' : ∀ v, (dn v).site.sub = 0)
    (go : ∀ ac bs, next Q L g d ⟨d.site.pc,.rd ac bs⟩ =
      some (some (dn ((rebuild 3 bs).toOption.getD (b32 0)))))
    (span : ∀ v, Inv (g%L.block) d →
      SegU kernel Assumptions.all L g (d.site.pc+1)
        ((r,v) :: facts Q L g w d d.site.pc)
        (dn v).site.pc (facts Q L g w (dn v) (dn v).site.pc))
    (inv : ∀ v, Inv (g%L.block) d → Inv (g%L.block) (dn v)) : (code Q L g w).StepAtU d where
  site := fun _ => ⟨_,hc,hl,trivial⟩
  step := by
    intro t ev u ins hat hi c fire
    obtain rfl := Option.some.inj (c.symm.trans hc)
    obtain ⟨ac,bs,rfl,rfl⟩ := fires_load hk hnc fire he
    rw [hr]
    let v := (rebuild 3 bs).toOption.getD (b32 0)
    suffices lands : ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (PTX.afterLoad t [r] bs) s ∧ (code Q L g w).GoodU (some (dn v)) s by
      obtain ⟨s,steps,good⟩ := lands
      exact .inl (.inr ⟨_,s,go ac bs,steps,good⟩)
    cases h : rebuild 3 bs with
    | error f =>
      exact Code.goodU_of_dead _ (Machine.dead_of_fault (f := f) (by simp [afterLoad,h]))
    | ok val =>
      have ht := Code.at_of_atD hat sub rfl
      obtain ⟨pc,hs,ha,fault,regs⟩ := ht
      rw [afterLoad_ok hs ha h]
      have eq : v = val := by simp [v,h,Except.toOption]
      rw [eq]
      apply Code.landsU (C := code Q L g w) _ (span val hi) (inv val hi) (sub' val) rfl
      refine ⟨congrArg (·+1) pc,rfl,rfl,fault,Function.update_self ..,?_⟩
      apply holds_update regs
      intro q hq eq
      have key := eq ▸ List.mem_map_of_mem (f := Prod.fst) hq
      change r ∈ (factsFrom _ _).map Prod.fst at key
      rw [factsFrom_keys] at key
      exact free key

private theorem addr_next (a : Nat) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 (a%2^64)) +
      truncBits 64 (BitVec.ofInt 64 4))) = u64 (a+4) := by
  apply congrArg (Value.bits 64)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits,BitVec.toNat_ofNat,BitVec.toNat_ofInt,BitVec.toNat_add]
  omega

private theorem addr_span {L g} (a : Nat) (V : Nat → Value) :
    Seg kernel Assumptions.all L g 2 35
      ((2055,u64 a)::factsFrom ((ctlLive 37).erase 2056) V)
      37 ((2056,u64 (a+4))::factsFrom ((ctlLive 37).erase 2056) V) := by
  intro t ht
  seg_fp ht using exact addr_next _

private def kept := [3,462,463,464,478,479,480,526,527,528,532,610,1949,2018,2019,2020,2021,2058]
private theorem kept_eq : (ctlLive 37).erase 2056 = kept := by decide +kernel

private def keptA := [3,462,463,464,478,479,480,526,527]
private def keptB := [528,532,1949,2018,2019,2020,2021,2058]

private theorem stableA {Q L g w v won bcast r} (hk : r ∈ keptA) :
    valueOf Q L g w ⟨.ld 0,b32 0,b32 0,b32 0,won,bcast⟩ r =
      valueOf Q L g w ⟨.ld 1,v,b32 0,b32 0,won,bcast⟩ r := by
  simp only [keptA,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [valueOf,registerValue]

private theorem stableB {Q L g w v won bcast r} (hk : r ∈ keptB) :
    valueOf Q L g w ⟨.ld 0,b32 0,b32 0,b32 0,won,bcast⟩ r =
      valueOf Q L g w ⟨.ld 1,v,b32 0,b32 0,won,bcast⟩ r := by
  simp only [keptB,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [valueOf,registerValue]

private theorem stable {Q L g w v won bcast r} (hk : r ∈ kept) (hne : r ≠ 610) :
    r ∈ ctlLive 34 ∧ valueOf Q L g w ⟨.ld 0,b32 0,b32 0,b32 0,won,bcast⟩ r =
      valueOf Q L g w ⟨.ld 1,v,b32 0,b32 0,won,bcast⟩ r := by
  have chk : kept.all (fun x => x == 610 || (ctlLive 34).contains x) := by decide +kernel
  have live := List.all_eq_true.mp chk r hk
  simp [hne] at live
  refine ⟨live,?_⟩
  have split : r ∈ keptA ∨ r ∈ keptB := by
    have := hk
    simp only [kept,keptA,keptB,List.mem_cons,List.not_mem_nil,or_false] at this ⊢
    omega
  rcases split with h|h
  · exact stableA h
  · exact stableB h

private theorem first_span {Q L g w} (v : Value) (won : Bool) (bcast : Value) :
    SegU kernel Assumptions.all L g 35
      ((610,v)::facts Q L g w ⟨.ld 0,b32 0,b32 0,b32 0,won,bcast⟩ 34)
      37 (facts Q L g w ⟨.ld 1,v,b32 0,b32 0,won,bcast⟩ 37) := by
  let V := valueOf Q L g w ⟨.ld 1,v,b32 0,b32 0,won,bcast⟩
  let a := Q.cuBase+4*((L.ctaidOf (g/L.block)).get .z%2^32)
  intro t ht
  obtain ⟨_,_,_,_,hv,old⟩ := id ht
  have keep : Holds t.regs (factsFrom ((ctlLive 37).erase 2056) V) := by
    apply holds_of_pointwise
    rw [kept_eq]
    intro r hr
    by_cases h : r=610
    · subst r; exact hv
    · obtain ⟨live,eq⟩ := stable (Q := Q) (L := L) (g := g) (w := w) (v := v)
        (won := won) (bcast := bcast) hr h
      exact (holds_mem old (mem_factsFrom live)).trans (congrArg some eq)
  have base : t.regs 2055 = some (u64 a) := holds_mem old
    (mem_factsFrom (val := valueOf Q L g w ⟨.ld 0,b32 0,b32 0,b32 0,won,bcast⟩)
      (by decide +kernel : 2055 ∈ ctlLive 34))
  obtain ⟨u,run,atU⟩ := addr_span (L := L) (g := g) a V t (ht.mono ⟨base,keep⟩)
  obtain ⟨_,_,_,_,written,keptRegs⟩ := id atU
  refine .inl ⟨u,run_rtg run,atU.mono ?_⟩
  apply holds_of_pointwise
  intro r hr
  by_cases h : r=2056
  · subst r; exact written
  · exact holds_mem keptRegs (mem_factsFrom ((List.mem_erase_of_ne h).mpr hr))

theorem step_read_first {Q L g w} (d : D) (hs : d.site = .ld 0) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.ld 0,a,b,c,won,bcast⟩
  let dn := fun v => ({d with first := v,site := .ld 1} : D)
  apply record (d := d) dn Flow.code_34 rfl rfl rfl rfl rfl
    (by change 610 ∉ ctlLive 34; decide +kernel) rfl (fun _ => rfl) (fun _ _ => rfl)
  · intro v hi
    obtain ⟨rfl,rfl,rfl⟩ := hi
    exact first_span v won bcast
  · intro _ hi
    exact hi.2

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
