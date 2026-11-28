-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedSite
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LKeep
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The running sum starts at zero

From the barrier of pc 575 or the last preload (pc 806) the thread runs to the first stop of the
loop. On the way pc 944 sets the running sum (register 1915) to zero. The facts are given by
position, the control machine names the stop. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The positions that follow the write of pc 944 (the update's pcs 949 to 998 are not on the
path). -/
def lIniKeys (pc : Nat) : List Nat := if 944 < pc ∧ pc ≤ 948 ∨ 1049 ≤ pc then [1915] else []

def lIniSpec (pc : Nat) : Bool := decide (pc = 944)

/-- The value of the running sum's register: zero. -/
def lIniV : Nat → Value := fun _ => b32 0

theorem linit_at : OAt kernel Assumptions.all L g 944 [.base (.movImm 1915 0)] :=
  ⟨⟨by decide +kernel, Kernels.InklingRelDecode.Proof.segFree (by decide +kernel),
    fun s hs => move_none (L := L) (g := g) (t := s) (by omega) (by omega) (by omega) _⟩, trivial⟩

theorem linit_segd :
    SegD kernel Assumptions.all L g 1 944 (factsFrom [] lIniV) 945
      (factsFrom [1915] (xFinal lIniV [.base (.movImm 1915 0)]))
      (xCond lIniV [.base (.movImm 1915 0)]) :=
  SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (items := [.base (.movImm 1915 0)]) (liveS := []) (liveT := [1915])
    (V := lIniV) (linit_at (L := L) (g := g)).code (by decide +kernel)
    (by simp [xReq, XItem.req, OItem.req]) (by decide +kernel)
    (linit_at (L := L) (g := g)).rules (by decide +kernel)

theorem linit_val : xFinal lIniV [.base (.movImm 1915 0)] 1915 = lIniV 1915 := by
  simp [xFinal, XItem.upd, XItem.vals, OItem.vals, Function.update, lIniV, b32]

theorem lini_spec {ivs : List (Nat × Nat)} (h945 : inIvs ivs 944 = true → inIvs ivs 945 = true) :
    ∀ pc, lIniSpec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt lIniKeys (fun _ => false) lIniV lIniV t → Tau kernel Assumptions.all L g t t1 →
      ((inIvs ivs t1.pc || evAtB kernel t1.pc) = true ∧
        TabAt lIniKeys (fun _ => false) lIniV lIniV t1) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t1 := by
  intro pc hsp hin t t1 hpc hT ht1
  obtain ⟨hsub, hacc, -⟩ := hT
  have hfault : t.fault = none := by
    unfold Tau out at ht1
    cases hf : t.fault with
    | none => rfl
    | some f => rw [hf] at ht1; cases ht1
  simp only [lIniSpec, decide_eq_true_eq] at hsp
  subst hsp
  rcases SegD.tau_one (linit_segd (L := L) (g := g)) ⟨hpc, hsub, hacc, hfault, trivial⟩ ht1 with
    hu | hd
  · refine .inl ⟨by rw [hu.1]; simp [h945 hin], hu.2.1, hu.2.2.1, ?_⟩
    have hk : lIniKeys t1.pc = [1915] := by rw [show t1.pc = 945 from hu.1]; rfl
    refine holds_of_pointwise fun r hr => ?_
    rw [hk] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨-, -, -, -, hur⟩ := id hu
    simp only [ite_self]
    rw [← linit_val]
    exact holds_mem hur (mem_factsFrom (by simp))
  · exact .inr hd

/-- The facts a stop after the first code holds, from the table's at its position. -/
theorem lconv_ini {d' : D}
    (hd : d'.c.site = .pre 0 ∨ d'.c.site = .nxt 0 ∨ d'.c.site = .waitS ∨ d'.c.site = .epilogue)
    (hl : d'.c.site ≠ .pre 0 → d'.v.l = b32 0) {R : Nat → Option Value}
    (h : Holds R (phi lIniKeys (fun _ => false) lIniV lIniV d'.c.site.pc)) : Holds R (lF d') := by
  rcases hd with h1 | h1 | h1 | h1
  · simp [lF, lFS, h1]
  · have hk : R 1915 = some (lIniV 1915) :=
      holds_mem h (mem_factsFrom (val := lIniV) (by rw [h1]; decide))
    simp only [lF, lFS, h1, hl (by rw [h1]; decide)] at hk ⊢
    exact ⟨hk, trivial⟩
  · have hk : R 1915 = some (lIniV 1915) :=
      holds_mem h (mem_factsFrom (val := lIniV) (by rw [h1]; decide))
    simp only [lF, lFS, h1, hl (by rw [h1]; decide)] at hk ⊢
    exact ⟨hk, trivial⟩
  · simp [lF, lFS, h1]

theorem lini_bar0_l {d : D} {ev : Event} {z : Site} (hs : d.c.site = .bar0) (hl : loopB z) :
    (record L d ev z).l = b32 0 := by
  unfold record
  simp [hs, hl]

theorem lini_pre_l {d : D} {x : Acc} {bs : List (Option Byte)} {z : Site} {j : Fin 64}
    (hs : d.c.site = .pre j) (hl : loopB z) : (record L d ⟨806, .rd x bs⟩ z).l = b32 0 := by
  unfold record
  simp [hs, hl]

/-- **The running sum after the barrier of the entry.** -/
theorem l_bar0 {d : D} (hs : d.c.site = .bar0) : DataStep (codeS e L g) lF d := by
  refine @bar0_open e L g d hs lF fun t ev hat hpc hstops => ?_
  have hp : (afterBar0 e L g d).site = .pre 0 ∨ loopB (afterBar0 e L g d).site := by
    by_cases hp : preEnabled e (g % L.block) = true
    · simp [afterBar0, hp]
    · simp only [afterBar0, hp, Bool.false_eq_true, ↓reduceIte]
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h, loopB]
  refine goal_tab (ivs := [(576, 423), (1049, 208), (2560, 5)]) (keys := lIniKeys)
    (post := fun _ => false) (spec := lIniSpec) (V1 := lIniV) (V2 := lIniV)
    (by decide +kernel) (hseg_ivs (by decide +kernel))
    (lini_spec (fun _ => by decide +kernel)) (u := PTX.next t)
    (by rw [hpc]; decide +kernel) ⟨hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩ hstops
    (fun R h => lconv_ini ?_ ?_ h)
  · rw [hpc]; simp [phi, lIniKeys, factsFrom]
  · by_cases hq : preEnabled e (g % L.block) = true
    · simp [afterBar0, hq]
    · simp only [afterBar0, hq, Bool.false_eq_true, ↓reduceIte]
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h]
  · intro hne
    exact lini_bar0_l hs (hp.resolve_left hne)

/-- **The running sum after the last preload.** -/
theorem l_pre63 {d : D} (hs : d.c.site = .pre 63) : DataStep (codeS e L g) lF d := by
  refine @pre63_open e L g d hs lF fun t x bs v c' hat hv hc hpc => ?_
  subst hc
  intro hstops
  refine goal_tab (ivs := [(806, 193), (1049, 208), (2560, 5)]) (keys := lIniKeys)
    (post := fun _ => false) (spec := lIniSpec) (V1 := lIniV) (V2 := lIniV)
    (by decide +kernel) (hseg_ivs (by decide +kernel))
    (lini_spec (fun h => by revert h; decide +kernel)) (u := after806 t v)
    ?_ ⟨rfl, rfl, ?_⟩ hstops (fun R h => lconv_ini ?_ ?_ h)
  · show (inIvs _ (t.pc + 1) || evAtB kernel (t.pc + 1)) = true
    rw [hpc]; decide +kernel
  · show Holds _ (phi lIniKeys (fun _ => false) lIniV lIniV (t.pc + 1))
    rw [hpc]; simp [phi, lIniKeys, factsFrom]
  · exact .inr (loopSite_mem _ _ _)
  · intro _
    exact lini_pre_l hs (by
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h, loopB])

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
