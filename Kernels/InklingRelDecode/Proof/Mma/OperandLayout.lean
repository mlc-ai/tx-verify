-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
import Lemmas.Flow.Step.TcDesc
import Lemmas.Flow.TcTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.EventFrame

private def Layout (L : Launch) (g : Nat) (d : TcMma.Descriptor) (sharedA : Bool) : Tmpl → Prop
  | .tc (.mma _ s _ _) _ => s.descriptor=d ∧ s.aTmem.isNone=sharedA ∧
      ∃ ctas, L.ctaGroup (g/L.block) d.group=some ctas ∧
        ctas.head?=some s.lowCta ∧ ctas.getLast?=some s.highCta
  | .ub _ => True
  | _ => False

variable {A : List Assumption} {L : Launch} {g pc dst : Nat} {t : TState} {o : Option TState}
  {s : TcMma.OperandSpec} {acc : Bool} {ms : List Nat} {ins : TcMmaInstr}

private theorem layout_event {d share tm} (h : Layout L g d share tm)
    (fire : Fires pc tm ⟨pc,.tc (.mma dst s acc ms)⟩ o) :
    s.descriptor=d ∧ s.aTmem.isNone=share ∧
      ∃ ctas, L.ctaGroup (g/L.block) d.group=some ctas ∧
        ctas.head?=some s.lowCta ∧ ctas.getLast?=some s.highCta := by
  cases tm <;> simp only [Layout] at h
  case tc k u => cases k <;> simp only at h; cases fire.1; exact h
  case ub => cases fire.1

/-- Inverting an actual issue keeps the instruction descriptor independently of
the contents or representability of the Tensor Memory destination register. The operand
CTAs are the first and last of the issuer's group. -/
theorem issue_layout {v : BitVec 64} {d} (rule : ins.rule=some .threadTc)
    (word : readBits L g t 32 ins.idesc=.ok v)
    (decode : TcMma.decode ins.group ins.ws ins.kind v.toNat=some d)
    (fire : Fires pc (eventTmpl A L g t (.tcMma ins)) ⟨pc,.tc (.mma dst s acc ms)⟩ o) :
    s.descriptor=d ∧ s.aTmem.isNone=(match ins.a with | .smem _ => true | .tmem .. => false) ∧
      ∃ ctas, L.ctaGroup (g/L.block) d.group=some ctas ∧
        ctas.head?=some s.lowCta ∧ ctas.getLast?=some s.highCta := by
  apply layout_event (fire := fire)
  cases source : ins.a with
  | smem addr =>
    simp only [eventTmpl,tcTmpl,mmaTmpl,rule,source,mmaSmemTmpl]
    apply ofExec_of_allOk (fun _ => trivial)
    split
    · iterate 3 refine allOk_bind fun _ => ?_
      refine allOk_okBind word ?_
      refine allOk_bind fun _ => ?_
      split
      · iterate 2 refine allOk_bind fun _ => ?_
        split <;> try exact trivial
        split <;> try exact trivial
        rw [decode]
        simp only
        split
        · rename_i result ok
          obtain ⟨eq,none,ctas,grp,lo,hi⟩ := makeOperands_fields ok
          exact ⟨eq,by change result.aTmem.isNone=true; simp [none],ctas,grp,lo,hi⟩
        · trivial
      · trivial
    · trivial
  | tmem reg off =>
    simp only [eventTmpl,tcTmpl,mmaTmpl,rule,source,mmaTmemTmpl]
    apply ofExec_of_allOk (fun _ => trivial)
    split
    · iterate 4 refine allOk_bind fun _ => ?_
      refine allOk_okBind word ?_
      refine allOk_bind fun _ => ?_
      split
      · iterate 2 refine allOk_bind fun _ => ?_
        split <;> try exact trivial
        rw [decode]
        simp only
        split
        · trivial
        · split
          · rename_i result ok
            obtain ⟨eq,_,ctas,grp,lo,hi⟩ := makeOperands_fields ok
            exact ⟨eq,rfl,ctas,grp,lo,hi⟩
          · trivial
      · trivial
    · trivial

end PTX.Kernels.InklingRelDecode.Proof.Mma
