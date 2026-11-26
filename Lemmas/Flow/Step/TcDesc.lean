-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.TcFields

@[expose] public section

/-! # The shared matrix descriptors of a `tcgen05.mma` and a `tcgen05.cp` issue

A proof tool, beside `Lemmas/Flow/Step/TcFields.lean` (the Tensor Memory operands): an issued
MMA's shared descriptors are the decoded words of its descriptor registers, and an issued copy's
source descriptor is the decoded word of its source register.

* `fires_tcMmaSmem_desc`: A in shared memory: `s.a` and `s.b` decode the A and B words;
* `fires_tcMmaTmem_desc`: A in Tensor Memory: `s.a` and `s.b` both decode the B word;
* `fires_tcCp_desc`: the copy's `src` decodes the source word. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState}

/-- An MMA issue whose shared descriptors decode the words `wa` and `wb`; anything else. -/
def MmaDescs (wa wb : Nat) : Tmpl → Prop
  | .tc (.mma _ s _ _) _ => TcShared.decode wa = some s.a ∧ TcShared.decode wb = some s.b
  | .ub _ => True
  | _ => False

/-- A copy whose source descriptor decodes the word `w`; anything else. -/
def CpDesc (w : Nat) : Tmpl → Prop
  | .tc (.cp s) _ => TcShared.decode w = some s.src
  | .ub _ => True
  | _ => False

/-- `makeOperands` takes the two shared descriptors as given. -/
theorem makeOperands_descs {issuer : Nat} {d : TcMma.Descriptor} {a b : TcShared.Descriptor}
    {s : TcMma.OperandSpec} (h : TcMma.makeOperands L issuer d a b = some s) :
    s.a = a ∧ s.b = b := by
  unfold TcMma.makeOperands at h
  cases hc : L.ctaGroup issuer d.group with
  | none => simp [hc] at h
  | some ctas =>
    cases hlo : ctas.head? <;> cases hhi : ctas.getLast? <;> simp [hc, hlo, hhi] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem mmaDescs_event {wa wb : Nat} {tm : Tmpl} (hm : MmaDescs wa wb tm) (hf : Fires pc tm e o)
    {c : Nat} {s : TcMma.OperandSpec} {acc : Bool} {ms : List Nat}
    (he : e.kind = .tc (.mma c s acc ms)) :
    TcShared.decode wa = some s.a ∧ TcShared.decode wb = some s.b := by
  cases tm <;> simp only [MmaDescs] at hm
  case tc k u =>
    cases k <;> simp only at hm
    simp only [Fires] at hf
    rw [hf.1] at he
    cases he
    exact hm
  case ub f =>
    simp only [Fires] at hf
    rw [hf.1] at he
    cases he

theorem cpDesc_event {w : Nat} {tm : Tmpl} (hm : CpDesc w tm) (hf : Fires pc tm e o)
    {s : TcCopy.Spec} (he : e.kind = .tc (.cp s)) : TcShared.decode w = some s.src := by
  cases tm <;> simp only [CpDesc] at hm
  case tc k u =>
    cases k <;> simp only at hm
    simp only [Fires] at hf
    rw [hf.1] at he
    cases he
    exact hm
  case ub f =>
    simp only [Fires] at hf
    rw [hf.1] at he
    cases he

/-- **A `tcgen05.mma` with A in shared memory**: its descriptors decode its A and B words. -/
theorem fires_tcMmaSmem_desc {m : TcMmaInstr} {ad : Opnd} {va vb : BitVec 64}
    (hr : m.rule = some .threadTc) (hmA : m.a = .smem ad)
    (hA : readBits L g t 64 ad = .ok va) (hB : readBits L g t 64 m.bdesc = .ok vb)
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) {c : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {ms : List Nat} (he : e.kind = .tc (.mma c s acc ms)) :
    TcShared.decode va.toNat = some s.a ∧ TcShared.decode vb.toNat = some s.b := by
  refine mmaDescs_event (tm := eventTmpl A L g t (.tcMma m)) ?_ hf he
  have hmt : mmaTmpl L g t m = mmaSmemTmpl L g t m.group m.ws m.kind m.d ad m.bdesc
      m.idesc m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA]
  simp only [eventTmpl, tcTmpl, hmt, mmaSmemTmpl]
  refine ofExec_of_allOk (fun _ => trivial) ?_
  split
  · refine allOk_bind fun _ => ?_
    refine allOk_okBind hA ?_
    refine allOk_okBind hB ?_
    refine allOk_bind fun _ => ?_
    refine allOk_bind fun _ => ?_
    split
    · refine allOk_bind fun _ => ?_
      refine allOk_bind fun _ => ?_
      split
      · rename_i da hda
        split
        · rename_i db hdb
          split
          · split
            · rename_i spec hs
              obtain ⟨h1, h2⟩ := makeOperands_descs hs
              exact ⟨by rw [hda, h1], by rw [hdb, h2]⟩
            · exact trivial
          · exact trivial
        · exact trivial
      · exact trivial
    · exact trivial
  · exact trivial

/-- **A `tcgen05.mma` with A in Tensor Memory**: both its descriptors decode its B word. -/
theorem fires_tcMmaTmem_desc {m : TcMmaInstr} {ta : Nat} {aoff : Int} {vb : BitVec 64}
    (hr : m.rule = some .threadTc) (hmA : m.a = .tmem ta aoff)
    (hB : readBits L g t 64 m.bdesc = .ok vb)
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) {c : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {ms : List Nat} (he : e.kind = .tc (.mma c s acc ms)) :
    TcShared.decode vb.toNat = some s.a ∧ TcShared.decode vb.toNat = some s.b := by
  refine mmaDescs_event (tm := eventTmpl A L g t (.tcMma m)) ?_ hf he
  have hmt : mmaTmpl L g t m = mmaTmemTmpl L g t m.group m.ws m.kind m.d ta aoff m.bdesc
      m.idesc m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA]
  simp only [eventTmpl, tcTmpl, hmt, mmaTmemTmpl]
  refine ofExec_of_allOk (fun _ => trivial) ?_
  split
  · refine allOk_bind fun _ => ?_
    refine allOk_bind fun _ => ?_
    refine allOk_bind fun _ => ?_
    refine allOk_okBind hB ?_
    refine allOk_bind fun _ => ?_
    refine allOk_bind fun _ => ?_
    split
    · refine allOk_bind fun _ => ?_
      refine allOk_bind fun _ => ?_
      split
      · rename_i db hdb
        split
        · split
          · exact trivial
          · split
            · rename_i spec hs
              obtain ⟨h1, h2⟩ := makeOperands_descs hs
              exact ⟨by rw [hdb, h1], by rw [hdb, h2]⟩
            · exact trivial
        · exact trivial
      · exact trivial
    · exact trivial
  · exact trivial

/-- **A `tcgen05.cp`**: its source descriptor decodes its source word. -/
theorem fires_tcCp_desc {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd}
    {fmt : Option TcCpFmt} {vs : BitVec 64} (hS : readBits L g t 64 sd = .ok vs)
    (hf : Fires pc (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) e o) {s : TcCopy.Spec}
    (he : e.kind = .tc (.cp s)) : TcShared.decode vs.toNat = some s.src := by
  refine cpDesc_event (tm := eventTmpl A L g t (.tcCp grp sh ta sd fmt)) ?_ hf he
  simp only [eventTmpl, tcTmpl]
  refine ofExec_of_allOk (fun _ => trivial) ?_
  split
  · refine allOk_bind fun _ => ?_
    split
    · refine allOk_okBind hS ?_
      split
      · rename_i src hs
        split
        · exact hs
        · exact trivial
      · exact trivial
    · exact trivial
  · exact trivial

end

end PTX.Flow
