-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Read
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Sub
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

private theorem seq_address (a n : Nat) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 a) +
      truncBits 64 (BitVec.ofNat 64 n))) = u64 (a+n) := by
  apply congrArg (Value.bits 64)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits,BitVec.toNat_ofNat,BitVec.toNat_add]
  omega

private theorem seq_addr_span {L g a n} (V : Nat → Value) :
    Seg kernel Assumptions.all L g 2 39
      ((2021,b64 a)::(2058,b64 n)::factsFrom ((ctlLive 41).erase 2057) V)
      41 ((2057,u64 (a+n))::factsFrom ((ctlLive 41).erase 2057) V) := by
  intro t ht
  seg_fp ht using exact seq_address _ _

private theorem carry {Q L g w first last won bcast r} (hr : r ∈ (ctlLive 41).erase 2057)
    (hk : r ≠ 481) : r ∈ ctlLive 37 ∧
      valueOf Q L g w ⟨.ld 1,first,b32 0,b32 0,won,bcast⟩ r =
      valueOf Q L g w ⟨.ld 2,first,last,b32 0,won,bcast⟩ r := by
  have keys : (ctlLive 41).erase 2057 =
      [3,462,463,464,478,479,480,481,526,527,528,532,610,1949,2018,2019,2020] := by decide +kernel
  rw [keys] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | contradiction | exact ⟨by decide +kernel,by simp only [valueOf,registerValue]⟩

private theorem length_span {Q L g w} (a v : Value) (won : Bool) (bcast : Value) :
    let d : D := ⟨.ld 1,a,b32 0,b32 0,won,bcast⟩
    let dn : D := {d with last := v,site := .ld 2}
    SegU kernel Assumptions.all L g 38 ((611,v)::facts Q L g w d 37)
      41 (facts Q L g w dn 41) := by
  intro d dn
  let V := valueOf Q L g w dn
  let n := 4*((L.ctaidOf (g/L.block)).get .z%2^32)
  let G := (2021,b64 Q.seqBase)::(2058,b64 n)::factsFrom ((ctlLive 41).erase 2057) V
  apply SegU.comp (b := 39) (G := G)
  · apply Lib.scalarStepU (r := 481) (v := subValue v a) Flow.code_38 rfl rfl (by decide)
    · intro t u h he
      have key : 610 ∈ ctlLive 37 := by decide +kernel
      exact (sub_result h.1 (holds_mem h.2 (mem_factsFrom (val := valueOf Q L g w d) key)) he).1
    · intro R h
      obtain ⟨_,old⟩ := h
      have get (r : Nat) (hr : r ∈ ctlLive 37) := holds_mem old (mem_factsFrom hr)
      refine ⟨?_,?_,?_⟩
      · exact (Function.update_of_ne (by decide : 2021 ≠ 481) ..).trans
          (get 2021 (by decide +kernel))
      · exact (Function.update_of_ne (by decide : 2058 ≠ 481) ..).trans
          (get 2058 (by decide +kernel))
      · apply holds_of_pointwise
        intro r hr
        by_cases h : r=481
        · subst r; exact Function.update_self ..
        · obtain ⟨key,eq⟩ := carry (Q := Q) (L := L) (g := g) (w := w) (first := a) (last := v)
            (won := won) (bcast := bcast) hr h
          rw [Function.update_of_ne h]
          exact (get r key).trans (congrArg some eq)
  · intro t ht
    obtain ⟨u,run,atU⟩ := seq_addr_span (a := Q.seqBase) (n := n) V t ht
    obtain ⟨_,_,_,_,written,regs⟩ := id atU
    refine .inl ⟨u,run_rtg run,atU.mono ?_⟩
    apply holds_of_pointwise
    intro r hr
    by_cases h : r=2057
    · subst r; exact written
    · exact holds_mem regs (mem_factsFrom ((List.mem_erase_of_ne h).mpr hr))

theorem step_read_last {Q L g w} (d : D) (hs : d.site = .ld 1) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.ld 1,a,b,c,won,bcast⟩
  let dn := fun v => ({d with last := v,site := .ld 2} : D)
  apply record (d := d) dn Flow.code_37 rfl rfl rfl rfl rfl
    (by change 611 ∉ ctlLive 37; decide +kernel) rfl (fun _ => rfl) (fun _ _ => rfl)
  · intro v hi
    obtain ⟨rfl,rfl⟩ := hi
    exact length_span a v won bcast
  · exact fun _ hi => hi.2

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
