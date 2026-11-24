-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Cont

@[expose] public section

/-! # The template of each site

`siteTmpl` is the event template of a site, as its abstract state determines it: the footprint
of element `sub` of a vector access, the value a store writes, the operand and lane offset of a
shuffle, the barrier. At a concrete state of the abstract state, the site's instruction has this
template (`tmpl_site`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Element `j` of a 16-byte vector access at `a`. -/
def vacc (sp : Space) (c a j : Nat) : Acc := { loc := ⟨sp, c, a + 4 * j⟩, size := 4, elem := j }

/-- The lane offset of butterfly round `k`. -/
def bfOff : Nat → Nat
  | 0 => 16 | 1 => 8 | 2 => 4 | 3 => 2 | _ => 1

/-- The destination register of round `k` of the warp's butterfly. -/
def bfaDst : Nat → Nat
  | 0 => 93 | 1 => 98 | 2 => 101 | 3 => 104 | _ => 107

/-- The destination register of round `k` of warp 0's butterfly. -/
def bfbDst : Nat → Nat
  | 0 => 134 | 1 => 138 | 2 => 141 | 3 => 144 | _ => 147

/-- The operand of round `k` of warp 0's butterfly: the loaded warp sum, then the partial sums. -/
def bfbOp (d : D) (k : Nat) : Value := bsumV d.u d.rb k

/-- The template of the site of `d` at a concrete state `t`. -/
def siteTmpl (P : Params) (g : Nat) (d : D) (t : TState) : Tmpl :=
  match d.site with
  | .shfl0 => .shfl .idx (b32 (g % 256 / 32)) 0 31 (fun recv ok =>
      PTX.next (setReg (setReg t 46 recv) 1 (.pred ok)))
  | .ldxa => .read (vacc .global 0 (P.I + off g d.i) d.sub) (afterLoad t [53, 54, 55, 56])
  | .stxa0 => .write (vacc .shared (g / 256) (P.S + 32 * (g % 256)) d.sub) (xw d.xa d.sub).toBytes
      (afterStore t [.reg 65, .reg 66, .reg 67, .reg 68])
  | .stxa1 => .write (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 16) d.sub)
      (xw d.xa (4 + d.sub)).toBytes (afterStore t [.reg 69, .reg 70, .reg 71, .reg 72])
  | .ldxb => .read (vacc .global 0 (P.I + off g d.i + 4096) d.sub) (afterLoad t [73, 74, 75, 76])
  | .stxb0 => .write (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192) d.sub)
      (xw d.xb d.sub).toBytes (afterStore t [.reg 85, .reg 86, .reg 87, .reg 88])
  | .stxb1 => .write (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8208) d.sub)
      (xw d.xb (4 + d.sub)).toBytes (afterStore t [.reg 89, .reg 90, .reg 91, .reg 92])
  | .bfa k => .shfl .bfly (bsumV (ssqV d) d.ra k) (bfOff k) 31 (fun recv _ =>
      PTX.next (setReg t (bfaDst k) recv))
  | .stws => .write { loc := ⟨.shared, g / 256, P.S + 4 * (g % 256 / 32) + 16384⟩, size := 4 }
      (bsumV (ssqV d) d.ra 5).toBytes (afterStore t [.reg 126])
  | .bar0 => .bar 0 (PTX.next t) none
  | .ldws => .read { loc := ⟨.shared, g / 256, P.S + 4 * (g % 256 % 32) + 16384⟩, size := 4 }
      (afterLoad t [281])
  | .bfb k => .shfl .bfly (bfbOp d k) (bfOff k) 31 (fun recv _ =>
      PTX.next (setReg t (bfbDst k) recv))
  | .stts => .write { loc := ⟨.shared, g / 256, P.S + 16384⟩, size := 4 }
      (bsumV d.u d.rb 5).toBytes (afterStore t [.reg 151])
  | .bar1 => .bar 0 (PTX.next t) none
  | .ldts => .read { loc := ⟨.shared, g / 256, P.S + 16384⟩, size := 4 } (afterLoad t [155])
  | .ldwa => .read (vacc .global 0 (P.W + 16 * (g % 256)) d.sub) (afterLoad t [167, 170, 173, 176])
  | .ldsa0 => .read (vacc .shared (g / 256) (P.S + 32 * (g % 256)) d.sub)
      (afterLoad t [157, 158, 159, 160])
  | .ldsa1 => .read (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 16) d.sub)
      (afterLoad t [162, 163, 164, 165])
  | .stoa => .write (vacc .global 0 (P.O + off g d.i) d.sub)
      (outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub).toBytes
      (afterStore t [.reg 211, .reg 212, .reg 213, .reg 214])
  | .ldwb => .read (vacc .global 0 (P.W + 16 * (g % 256) + 4096) d.sub)
      (afterLoad t [225, 228, 231, 234])
  | .ldsb0 => .read (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192) d.sub)
      (afterLoad t [215, 216, 217, 218])
  | .ldsb1 => .read (vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8208) d.sub)
      (afterLoad t [220, 221, 222, 223])
  | .stob => .write (vacc .global 0 (P.O + off g d.i + 4096) d.sub)
      (outV d.raw d.rs0 d.rs1 (cpair d.tt) d.sub).toBytes
      (afterStore t [.reg 269, .reg 270, .reg 271, .reg 272])
  | .bar2 => .bar 1 (PTX.next t) none
  | .exit => .exit

end
end PTX.Kernels.RmsNorm.Proof

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}


set_option maxRecDepth 100000

/-- The width of a register value: an outcome of the code has four bytes. -/
macro "val_bytes" : tactic => `(tactic| first
  | (rms_values; first
    | exact addV_bytes _ _ | exact ssqV_bytes _ | exact xw_bytes _ _
    | exact outV_bytes _ _ _ _ _ | exact ml1_bytes _ _ _ _ | exact mh1_bytes _ _ _ _
    | exact ml2_bytes _ _ _ _ _ | exact mh2_bytes _ _ _ _ _ | exact rrV_bytes _)
  | exact addV_bytes _ _ | exact ssqV_bytes _ | exact xw_bytes _ _ | exact outV_bytes _ _ _ _ _
  | exact ml1_bytes _ _ _ _ | exact mh1_bytes _ _ _ _ | exact ml2_bytes _ _ _ _ _
  | exact mh2_bytes _ _ _ _ _ | exact rrV_bytes _)

/-- **The template of a site.** -/
theorem tmpl_site (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} (hi : Inv P g d)
    (h : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Prod L g t ins.op = siteTmpl P g d t := by
  have hF : Holds t.regs (factsAt P g d.site.pc d) := h.2.2.2.2
  have hsub : t.sub = d.sub := h.2.1
  rms_hyps hpre
  unfold siteTmpl
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _
  all_goals rw [hs] at hc hF
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    exact tmpl_shfl0 hpre (reg_of hF (by table_decide))
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    rw [tmpl_ldx hpre (.inl rfl) (hi.row (by simp [hs, Site.inRow]))
      (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sts hpre rfl (.inl rfl) (reg_of hF (by table_decide)) (r := 65) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 65) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inl rfl) (reg_of hF (by table_decide)) (r := 66) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 66) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inl rfl) (reg_of hF (by table_decide)) (r := 67) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 67) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inl rfl) (reg_of hF (by table_decide)) (r := 68) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 68) (by val_bytes)]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sts hpre rfl (.inr (.inl rfl)) (reg_of hF (by table_decide)) (r := 69)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 69) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inl rfl)) (reg_of hF (by table_decide)) (r := 70)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 70) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inl rfl)) (reg_of hF (by table_decide)) (r := 71)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 71) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inl rfl)) (reg_of hF (by table_decide)) (r := 72)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 72) (by val_bytes)]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
    rw [tmpl_ldx hpre (.inr rfl) (hi.row (by simp [hs, Site.inRow]))
      (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_2)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inl rfl))) (reg_of hF (by table_decide)) (r := 85)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 85) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inl rfl))) (reg_of hF (by table_decide)) (r := 86)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 86) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inl rfl))) (reg_of hF (by table_decide)) (r := 87)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 87) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inl rfl))) (reg_of hF (by table_decide)) (r := 88)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 88) (by val_bytes)]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_3)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inr rfl))) (reg_of hF (by table_decide)) (r := 89)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 89) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inr rfl))) (reg_of hF (by table_decide)) (r := 90)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 90) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inr rfl))) (reg_of hF (by table_decide)) (r := 91)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 91) (by val_bytes)]; rfl
    · rw [tmpl_sts hpre rfl (.inr (.inr (.inr rfl))) (reg_of hF (by table_decide)) (r := 92)
        (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 92) (by val_bytes)]; rfl
  · have hk := hi.bfa k hs
    interval_cases k
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_3)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_4)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_5)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_4)
    have := tid_lt g
    rw [tmpl_st1 hpre (hsub.trans (hi.sub.2 (by simp [hs, Site.vec]))) (by omega) (by omega)
      (reg_of hF (by table_decide))
      (reg_of hF (by table_decide)),
      storeValue_of_bytes (v := valueOf P g d 126) (by val_bytes)]
    rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    exact tmpl_bar hpre (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_2)
    have := hi.ldws hs
    exact tmpl_ld1 hpre (hsub.trans (hi.sub.2 (by simp [hs, Site.vec]))) (by omega) (by omega)
      (reg_of hF (by table_decide))
  · have hk := (hi.bfb k hs).1
    interval_cases k
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_6)
      exact tmpl_shfl hpre (reg_of hF (by table_decide)) (hi.u hs) (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_7)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_8)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_9)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_10)
      refine tmpl_shfl hpre (reg_of hF (by table_decide)) ?_ (reg_of hF (by table_decide))
        (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
      val_bytes
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_5)
    rw [tmpl_st1 hpre (hsub.trans (hi.sub.2 (by simp [hs, Site.vec]))) (by omega) (by omega)
      (reg_of hF (by table_decide))
      (reg_of hF (by table_decide)),
      storeValue_of_bytes (v := valueOf P g d 151) (by val_bytes)]
    rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    exact tmpl_bar hpre (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_3)
    exact tmpl_ld1 hpre (hsub.trans (hi.sub.2 (by simp [hs, Site.vec]))) (by omega) (by omega)
      (reg_of hF (by table_decide))
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_4)
    rw [tmpl_ldw hpre (.inl rfl) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_5)
    rw [tmpl_lds hpre (.inl rfl) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_6)
    rw [tmpl_lds hpre (.inr (.inl rfl)) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_6)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sto hpre rfl (.inl rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 211) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 211) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inl rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 212) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 212) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inl rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 213) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 213) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inl rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 214) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 214) (by val_bytes)]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_7)
    rw [tmpl_ldw hpre (.inr rfl) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_8)
    rw [tmpl_lds hpre (.inr (.inr (.inl rfl))) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_9)
    rw [tmpl_lds hpre (.inr (.inr (.inr rfl))) (reg_of hF (by table_decide)), hsub]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_7)
    have := hi.sub.1 (by simp [hs, Site.vec])
    interval_cases d.sub
    · rw [tmpl_sto hpre rfl (.inr rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 269) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 269) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inr rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 270) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 270) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inr rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 271) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 271) (by val_bytes)]; rfl
    · rw [tmpl_sto hpre rfl (.inr rfl) (hi.row (by simp [hs, Site.inRow]))
        (reg_of hF (by table_decide)) (r := 272) (by simp [hsub])
        (reg_of hF (by table_decide)), hsub,
        storeValue_of_bytes (v := valueOf P g d 272) (by val_bytes)]; rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_2)
    exact tmpl_bar hpre (by decide) (reg_of hF (by table_decide)) (reg_of hF (by table_decide))
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    rfl

end
end PTX.Kernels.RmsNorm.Proof
