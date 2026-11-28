-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
public import Lemmas.Flow.ElectU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- The live values at a new election predate its result. -/
theorem elect_facts {Q L g w} (d : D) (pc : Nat) (won : Bool)
    (keys : (ctlLive pc).all (fun r => !voteReg r)) :
    facts Q L g w d pc = facts Q L g w {d with elected := won} pc := by
  apply List.map_congr_left
  intro r key
  have fixed : voteReg r = false := by simpa using List.all_eq_true.mp keys r key
  simp only [valueOf,fixed,Bool.false_and]

/-- Project the election writes before crossing the predicate computation.
The integer leader register is used for data only. -/
theorem full_elect {Q L g w} (d : D) (z : Bool → Site) {r p : Nat}
    (fetch : kernel.code[d.site.pc]? =
      some ⟨none,.warp ⟨.elect,none,[some r,some p],[],some (.imm (-1))⟩⟩)
    (keys : (ctlLive d.site.pc).all (fun k => !voteReg k))
    (free : r ∉ ctlLive d.site.pc ∧ p ∉ ctlLive d.site.pc ∧ r ≠ p)
    (go : ∀ mk inst ld, let win := laneOf L g == ld
      next Q L g d ⟨d.site.pc,.elect mk inst ld⟩ =
        some (some {d with site := z win,elected := win}))
    (sub : d.site.sub = 0) (sub' : ∀ win, (z win).sub = 0)
    (inv : ∀ win, Inv (g%L.block) {d with site := z win,elected := win})
    (seg : ∀ win, let dd := {d with elected := win}
      SegU kernel Assumptions.all L g (d.site.pc+1) ((p,.pred win)::facts Q L g w dd d.site.pc)
        (z win).pc (facts Q L g w dd (z win).pc)) : (code Q L g w).StepAtU d := by
  let dest := fun ld => {d with site := z (laneOf L g == ld),elected := laneOf L g == ld}
  apply Code.electU (C := code Q L g w) (d := d) (dst := dest) fetch _ _ free.2.2 go sub rfl
    (fun ld => sub' _)
    (fun _ => rfl) (fun ld => inv _) _
  · change r ∉ (factsFrom _ _).map Prod.fst
    rw [factsFrom_keys]
    exact free.1
  · change p ∉ (factsFrom _ _).map Prod.fst
    rw [factsFrom_keys]
    exact free.2.1
  · intro ld t ht
    obtain ⟨_,_,_,_,pred,_,old⟩ := id ht
    change Holds t.regs (facts Q L g w d d.site.pc) at old
    rw [elect_facts d _ (laneOf L g == ld) keys] at old
    exact seg _ t (ht.mono ⟨pred,old⟩)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
