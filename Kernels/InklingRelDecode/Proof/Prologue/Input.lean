-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Flow.Code.Part000
import Lemmas.Flow.Step.ShapeRegs
import Lemmas.Kernel.Source.Launch
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Control

def requestAddr (Q : Params) (r : Nat) : Fin 3 → Nat
  | 0 => Q.cuBase+4*r | 1 => Q.cuBase+4*(r+1) | 2 => Q.seqBase+4*r

def requestWord (Q : Params) (r : Nat) : Fin 3 → Nat
  | 0 => Q.qStart r | 1 => Q.qStart (r+1) | 2 => Q.seqK r

private theorem address_lt {Q L m r} (hp : Pre Q L m) (hr : r<Q.b) (i : Fin 3) :
    requestAddr Q r i < 2^64 := by
  apply hp.readsRange
  fin_cases i
  · exact .inr (.inr (.inr (.inl ⟨r,hr.le,0,by decide,rfl⟩)))
  · exact .inr (.inr (.inr (.inl ⟨r+1,by omega,0,by decide,rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨r,hr,0,by decide,rfl⟩))))

private theorem request_read {Q L g w d t ins o a bs} (i : Fin 3) (hs : d.site=Site.ld i)
    (ht : (code Q L g w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc,.rd a bs⟩ o)
    {r : Nat} (req : (L.ctaidOf (g/L.block)).get .z = r) (small : r<2^32)
    (bound : requestAddr Q r i<2^64) : a = wordAcc (requestAddr Q r i) := by
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have hsub : t.sub=0 := by change t.sub=d.site.sub at sub; rw [hs] at sub; exact sub
  have key : ∀ j : Fin 3, 2055+j.val ∈ ctlLive (Site.ld j).pc := by decide +kernel
  have reg := holds_mem regs (mem_factsFrom (hs ▸ key i))
  have val : valueOf Q L g w d (2055+i.val) = b64 (requestAddr Q r i) := by
    fin_cases i <;> change u64 _ = b64 _
    all_goals rw [req,Nat.mod_eq_of_lt small]
    all_goals unfold u64
    all_goals apply congrArg b64
    all_goals dsimp only [requestAddr] at bound ⊢
    all_goals omega
  rw [val] at reg
  have fire : Fires d.site.pc (loadTmpl Assumptions.all L g t .global false 32 [610+i.val]
      (2055+i.val) 0) ⟨d.site.pc,.rd a bs⟩ o := by
    rw [hs] at hc
    fin_cases i
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_34); exact hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_37); exact hf
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_41); exact hf
  rcases fires_load_reg hsub reg fire with ⟨_,h⟩|⟨_,h⟩
  · have eq := (Kind.rd.inj h).1
    change requestAddr Q r i < 18446744073709551616 at bound
    simpa [truncBits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] using eq
  · cases h

/-- A request-word load reads input bytes. -/
theorem request_input {Q L m g w d t ins o a bs} (hp : Pre Q L m) (hg : g<L.threads) (i : Fin 3)
    (hs : d.site=Site.ld i) (ht : (code Q L g w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc,.rd a bs⟩ o) :
    Iface.InputAcc Q a := by
  let r := (L.ctaidOf (g/L.block)).get .z
  have hr : r<Q.b := (Lib.coordinate_bounds hp hg).2.2
  have hb := hp.bRange
  obtain rfl := request_read i hs ht hc hf (r := r) rfl (by omega) (address_lt hp hr i)
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  fin_cases i
  · exact .inr (.inr (.inr (.inl ⟨r, hr.le, j, hj, by simp [wordAcc, requestAddr]⟩)))
  · exact .inr (.inr (.inr (.inl ⟨r+1, by omega, j, hj, by simp [wordAcc, requestAddr]⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨r, hr, j, hj, by simp [wordAcc, requestAddr]⟩))))

/-- The three request registers retain the exact launch words, including the tags of their bytes. -/
theorem request_value {Q L m X g k w d t ins o a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (i : Fin 3)
    (hs : d.site=Site.ld i) (ht : (code Q L g w).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (he : X.get (g,k) = some ⟨d.site.pc,.rd a bs⟩)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc,.rd a bs⟩ o) :
    rebuild 3 bs = .ok (b32 (requestWord Q ((L.ctaidOf (g/L.block)).get .z) i)) := by
  let r := (L.ctaidOf (g/L.block)).get .z
  have hr : r<Q.b := (Lib.coordinate_bounds hp hg).2.2
  have hb := hp.bRange
  obtain rfl := request_read i hs ht hc hf (r := r) rfl (by omega) (address_lt hp hr i)
  have ro := Frame.LaunchReads.of_forall (hX.asm _ (show Assumptions.inputReadOnly ∈
    Assumptions.all by simp [Assumptions.all]))
  apply Frame.LaunchReads.value (v := b32 (requestWord Q r i)) hX ro he _ rfl
    (fun _ _ => trivial) _ (by decide : 0<4) rfl
  · rw [hs]; fin_cases i <;> decide
  · intro j hj
    change m ⟨.global,0,requestAddr Q r i+j⟩ = _
    fin_cases i
    · exact hp.cuInput _ hr.le j hj
    · exact hp.cuInput _ (by omega : r+1≤Q.b) j hj
    · exact hp.seqInput _ hr j hj

end PTX.Kernels.InklingRelDecode.Proof.Prologue
