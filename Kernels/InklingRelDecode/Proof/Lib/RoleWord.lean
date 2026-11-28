-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Lib.SymbolStore
import Kernels.InklingRelDecode.Flow.Code.Part008
import Kernels.InklingRelDecode.Flow.Code.Part044
import Lemmas.Flow.NotBulk
import Lemmas.Flow.Final

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

private theorem scalar_sub {A L g t e u pc x off} (hf : Fires pc (eventTmpl A L g t
    (.mem (symStore 1 off [.imm x]))) e (some u)) : t.sub = 0 := by
  by_contra h
  have miss : ([Opnd.imm x] : List Opnd)[t.sub]? = none := List.getElem?_eq_none (by simp; omega)
  have hr : (symStore 1 off [.imm x]).rule = some .threadAccess :=
    symStore_rule rfl (Or.inl rfl)
  simp only [eventTmpl,memTmpl,hr] at hf
  change Fires pc (accessTmpl A L g t (symStore 1 off [.imm x])) e (some u) at hf
  simp only [accessTmpl,symStore,miss] at hf
  split at hf <;> cases hf.2

/-- The two scalar publications to the dispatch table write immediate words. -/
theorem role_word {Q L m X g k pc a bs x} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨pc,.wr a bs⟩)
    (site : (pc=570 ∧ x=16777730) ∨ (pc=2848 ∧ x=50529027)) :
    a = wordAcc ⟨.shared,g/L.block,L.sharedBase+213336⟩ ∧ bs = (b32 x).toBytes := by
  have code : kernel.code[pc]? = some ⟨none,.mem (symStore 1 213336 [.imm x])⟩ := by
    rcases site with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Flow.code_570
    · exact Flow.code_2848
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,hc,fire⟩ := get_source hX he
  · cases bad
  obtain rfl := Option.some.inj (hc.symm.trans code)
  cases o with
  | none =>
    rcases fires_none_ends fire with ⟨_,bad⟩|bad <;> cases bad
  | some u =>
    change Fires pc (eventTmpl Assumptions.all L g t (.mem (symStore 1 213336 [.imm x])))
      ⟨pc,.wr a bs⟩ (some u) at fire
    generalize Assumptions.all = A at fire
    have sub := scalar_sub (off := 213336) (A := A) (L := L) (g := g) (t := t)
      (pc := pc) (x := (x : Int))
      (u := u) (e := ⟨pc,.wr a bs⟩)
    have src : readValue L g t 32 (.imm x) = .ok (b32 x) := by
      rcases site with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
    have get := fires_st_sym (A := A) (L := L) (g := g) (pc := pc) (t := t)
      (e := ⟨pc,.wr a bs⟩) (u := u) (op := .mem (symStore 1 213336 [.imm x]))
      (vec := 1) (off := 213336) (srcs := [.imm x]) (j := 0) (o := .imm x) (v := b32 x)
      rfl (by decide)
    generalize eventTmpl A L g t (.mem (symStore 1 213336 [.imm x])) = tpl at fire get sub
    obtain ⟨v,hv,eq⟩ := get (sub (by exact fire)) rfl src rfl (Or.inl rfl) (by exact fire)
    rw [storeValue_of_bytes (by rfl)] at hv
    cases hv
    obtain ⟨addr,rfl⟩ := Kind.wr.inj (congrArg Event.kind eq)
    have bound := hp.sharedRange
    change L.sharedBase+213340≤2^18 at bound
    change a = wordAcc ⟨.shared,g/L.block,(L.sharedBase+213336)%2^32 + 4*0⟩ 0 at addr
    rw [Nat.mod_eq_of_lt (show L.sharedBase+213336<2^32 by omega)] at addr
    exact ⟨addr,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
