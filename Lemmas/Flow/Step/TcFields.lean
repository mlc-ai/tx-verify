-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.TcCpWs

@[expose] public section

/-! # The operand fields of a `tcgen05.cp` and a `tcgen05.mma` issue, or undefined behaviour

A proof tool. `Lemmas/Flow/Step/TcCpWs.lean` gives the shape of a copy (`fires_tcCp_cases`) and
that an MMA fires an MMA issue (`shape_tcMma`), and the full templates when every read succeeds
(`tc_cp`, `tc_mmaTmem`, `tc_mmaSmem`). Here the issue's Tensor Memory operands follow from the
register reads alone, the rest of the template staying open (an issue or undefined behaviour):

* `fires_tcCp_fields`: a copy's address is its address register's word, its CTAs the group's;
* `fires_tcMmaTmem_fields`, `fires_tcMmaSmem_fields`: an MMA's D address, A address (or none),
  decoded instruction descriptor, CTAs, accumulate flag and output masks;
* `mmaEnable_of`, `tmemOffset_zero`: the accumulate flag of a predicate register, the address
  `[a + 0]`. -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState}

/-- The fields of a copy from its address word `a`: shape, decompression, address, CTAs. -/
def CpFields (L : Launch) (g : Nat) (grp : CtaGroup) (sh : TcCpShape) (fmt : Option TcCpFmt)
    (a : Nat) (t : TState) : Tmpl → Prop
  | .tc (.cp s) u => s.shape = sh ∧ s.fmt = fmt ∧ s.address = a ∧
      L.ctaGroup (g / L.block) grp = some s.ctas ∧ u = next t
  | .ub _ => True
  | _ => False

theorem ofExec_of_allOk {Q : Tmpl → Prop} {r : Exec Tmpl} (hub : ∀ f, Q (.ub f))
    (h : AllOk Q r) : Q (ofExec r) := by
  cases r with
  | error f => exact hub _
  | ok m => exact h

theorem allOk_okBind {α β : Type} {Q : β → Prop} {r : Exec α} {a : α} {f : α → Exec β}
    (hr : r = .ok a) (h : AllOk Q (f a)) : AllOk Q (r >>= f) := by
  subst hr
  exact h

/-- **A `tcgen05.cp` copies to its address register's word**, in the CTAs of its group, or is
undefined behaviour. -/
theorem fires_tcCp_fields {grp : CtaGroup} {sh : TcCpShape} {ta : Nat} {sd : Opnd}
    {fmt : Option TcCpFmt} {va : BitVec 64} (hA : readBits L g t 32 (.reg ta) = .ok va)
    (hf : Fires pc (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) e o) :
    (∃ s : TcCopy.Spec, e.kind = .tc (.cp s) ∧ s.shape = sh ∧ s.fmt = fmt ∧
      s.address = va.toNat ∧ L.ctaGroup (g / L.block) grp = some s.ctas) ∨
      ∃ f, e.kind = .ub f := by
  have hm : CpFields L g grp sh fmt va.toNat t (eventTmpl A L g t (.tcCp grp sh ta sd fmt)) := by
    simp only [eventTmpl, tcTmpl]
    refine ofExec_of_allOk (fun _ => trivial) ?_
    split
    · refine allOk_okBind hA ?_
      split
      · refine allOk_bind fun _ => ?_
        split
        · split
          · rename_i ctas hc
            exact ⟨rfl, rfl, rfl, hc, rfl⟩
          · exact trivial
        · exact trivial
      · exact trivial
    · exact trivial
  generalize eventTmpl A L g t (.tcCp grp sh ta sd fmt) = tm at hm hf
  cases tm <;> simp only [CpFields] at hm
  case tc k u =>
    cases k <;> simp only at hm
    obtain ⟨h1, h2, h3, h4, rfl⟩ := hm
    simp only [Fires] at hf
    exact .inl ⟨_, congrArg Event.kind hf.1, h1, h2, h3, h4⟩
  case ub f =>
    simp only [Fires] at hf
    exact .inr ⟨f, congrArg Event.kind hf.1⟩

/-- The operand fields of an MMA issue: D address `c`, A address `aT`, the descriptor decoded
from the word `i`, the CTAs of the descriptor's group, accumulate flag and output masks. -/
def MmaFields (L : Launch) (g : Nat) (grp : CtaGroup) (ws : Bool) (kind : MmaKind)
    (c : Nat) (aT : Option Nat) (i : Nat) (acc : Bool) (ms : List Nat) (t : TState) :
    Tmpl → Prop
  | .tc (.mma d s acc' ms') u => d = c ∧ s.aTmem = aT ∧
      TcMma.decode grp ws kind i = some s.descriptor ∧
      (∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
        ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∧
      acc' = acc ∧ ms' = ms ∧ u = next t
  | .ub _ => True
  | _ => False

/-- `makeOperands` keeps the descriptor, reads A from shared memory and takes the group's CTAs. -/
theorem makeOperands_fields {issuer : Nat} {d : TcMma.Descriptor} {a b : TcShared.Descriptor}
    {s : TcMma.OperandSpec} (h : TcMma.makeOperands L issuer d a b = some s) :
    s.descriptor = d ∧ s.aTmem = none ∧ ∃ ctas, L.ctaGroup issuer d.group = some ctas ∧
      ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta := by
  unfold TcMma.makeOperands at h
  cases hc : L.ctaGroup issuer d.group with
  | none => simp [hc] at h
  | some ctas =>
    cases hlo : ctas.head? <;> cases hhi : ctas.getLast? <;> simp [hc, hlo, hhi] at h
    subst h
    exact ⟨rfl, rfl, ctas, rfl, hlo, hhi⟩

theorem mmaFields_event {grp : CtaGroup} {ws : Bool} {kind : MmaKind} {c : Nat}
    {aT : Option Nat} {i : Nat} {acc : Bool} {ms : List Nat} {tm : Tmpl}
    (hm : MmaFields L g grp ws kind c aT i acc ms t tm) (hf : Fires pc tm e o) :
    (∃ s, e.kind = .tc (.mma c s acc ms) ∧ s.aTmem = aT ∧
      TcMma.decode grp ws kind i = some s.descriptor ∧
      ∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
        ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∨
      ∃ f, e.kind = .ub f := by
  cases tm <;> simp only [MmaFields] at hm
  case tc k u =>
    cases k <;> simp only at hm
    obtain ⟨rfl, h2, h3, h4, rfl, rfl, rfl⟩ := hm
    simp only [Fires] at hf
    exact .inl ⟨_, congrArg Event.kind hf.1, h2, h3, h4⟩
  case ub f =>
    simp only [Fires] at hf
    exact .inr ⟨f, congrArg Event.kind hf.1⟩

/-- The `enable-input-d` operand of a predicate register is its value. -/
theorem mmaEnable_of {r : Nat} {b : Bool} (h : t.regs r = some (.pred b)) :
    mmaEnable t (.reg r) = .ok b := by
  simp [mmaEnable, readReg, h, bind, Except.bind, pure, Except.pure]

/-- The Tensor Memory address `[a + 0]` is `a`. -/
theorem tmemOffset_zero (a : Nat) : tmemOffset a 0 = .ok a := by
  simp only [tmemOffset, Int.add_zero]
  split
  · simp only [pure, Except.pure, Except.ok.injEq]
    omega
  · omega

/-- **A `tcgen05.mma` with A in Tensor Memory** issues with the D address, the A address and the
descriptor of its registers, or is undefined behaviour. -/
theorem fires_tcMmaTmem_fields {m : TcMmaInstr} {ta : Nat} {aoff : Int} {vd va vi : BitVec 64}
    {a' : Nat} {msv : List (BitVec 64)} {acc : Bool} {rI : Opnd}
    (hr : m.rule = some .threadTc) (hmA : m.a = .tmem ta aoff) (hmI : m.idesc = rI)
    (hd : readBits L g t 32 (.reg m.d) = .ok vd) (hA : readBits L g t 32 (.reg ta) = .ok va)
    (ho : tmemOffset va.toNat aoff = .ok a') (hI : readBits L g t 32 rI = .ok vi)
    (hm : m.mask.mapM (readBits L g t 32) = .ok msv) (he : mmaEnable t m.enableD = .ok acc)
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) :
    (∃ s, e.kind = .tc (.mma vd.toNat s acc (msv.map BitVec.toNat)) ∧ s.aTmem = some a' ∧
      TcMma.decode m.group m.ws m.kind vi.toNat = some s.descriptor ∧
      ∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
        ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∨
      ∃ f, e.kind = .ub f := by
  refine mmaFields_event (t := t) (tm := eventTmpl A L g t (.tcMma m)) ?_ hf
  have hmt : mmaTmpl L g t m = mmaTmemTmpl L g t m.group m.ws m.kind m.d ta aoff m.bdesc
      m.idesc m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA]
  simp only [eventTmpl, tcTmpl, hmt, mmaTmemTmpl, hmI]
  refine ofExec_of_allOk (fun _ => trivial) ?_
  split
  · refine allOk_okBind hd ?_
    refine allOk_okBind hA ?_
    refine allOk_okBind ho ?_
    refine allOk_bind fun _ => ?_
    refine allOk_okBind hI ?_
    refine allOk_okBind hm ?_
    split
    · refine allOk_okBind he ?_
      refine allOk_bind fun _ => ?_
      split
      · split
        · rename_i desc hdi
          split
          · exact trivial
          · split
            · rename_i spec hs
              obtain ⟨h1, -, ctas, h3, h4, h5⟩ := makeOperands_fields hs
              refine ⟨rfl, rfl, ?_, ⟨ctas, ?_, h4, h5⟩, rfl, rfl, rfl⟩
              · rw [h1]; exact hdi
              · rw [h1]; exact h3
            · exact trivial
        · exact trivial
      · exact trivial
    · exact trivial
  · exact trivial

/-- **A `tcgen05.mma` with A in shared memory** issues with the D address and the descriptor of
its registers and no Tensor Memory A, or is undefined behaviour. -/
theorem fires_tcMmaSmem_fields {m : TcMmaInstr} {ad : Opnd} {vd vi : BitVec 64}
    {msv : List (BitVec 64)} {acc : Bool} {rI : Opnd}
    (hr : m.rule = some .threadTc) (hmA : m.a = .smem ad) (hmI : m.idesc = rI)
    (hd : readBits L g t 32 (.reg m.d) = .ok vd) (hI : readBits L g t 32 rI = .ok vi)
    (hm : m.mask.mapM (readBits L g t 32) = .ok msv) (he : mmaEnable t m.enableD = .ok acc)
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) :
    (∃ s, e.kind = .tc (.mma vd.toNat s acc (msv.map BitVec.toNat)) ∧ s.aTmem = none ∧
      TcMma.decode m.group m.ws m.kind vi.toNat = some s.descriptor ∧
      ∃ ctas, L.ctaGroup (g / L.block) s.descriptor.group = some ctas ∧
        ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta) ∨
      ∃ f, e.kind = .ub f := by
  refine mmaFields_event (t := t) (tm := eventTmpl A L g t (.tcMma m)) ?_ hf
  have hmt : mmaTmpl L g t m = mmaSmemTmpl L g t m.group m.ws m.kind m.d ad m.bdesc
      m.idesc m.mask m.enableD m.zeroColumnMask m.collectors := by
    simp only [mmaTmpl, hr, hmA]
  simp only [eventTmpl, tcTmpl, hmt, mmaSmemTmpl, hmI]
  refine ofExec_of_allOk (fun _ => trivial) ?_
  split
  · refine allOk_okBind hd ?_
    refine allOk_bind fun _ => ?_
    refine allOk_bind fun _ => ?_
    refine allOk_okBind hI ?_
    refine allOk_okBind hm ?_
    split
    · refine allOk_okBind he ?_
      refine allOk_bind fun _ => ?_
      split
      · split
        · split
          · rename_i desc hdi
            split
            · rename_i spec hs
              obtain ⟨h1, h2, ctas, h3, h4, h5⟩ := makeOperands_fields hs
              refine ⟨rfl, h2, ?_, ⟨ctas, ?_, h4, h5⟩, rfl, rfl, rfl⟩
              · rw [h1]; exact hdi
              · rw [h1]; exact h3
            · exact trivial
          · exact trivial
        · exact trivial
      · exact trivial
    · exact trivial
  · exact trivial

end

end PTX.Flow
