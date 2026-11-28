-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.RefWords
public import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
public import Kernels.InklingRelDecode.Proof.Lib.SymbolStore
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow PTX.Proof Control

set_option maxRecDepth 8192

def publishValue (Q : Params) (L : Launch) (c : Nat) : Fin 2 → Nat
  | 0 => Iface.preloadCount Q L c
  | 1 => Q.numIters ((L.ctaidOf c).get .z) ((L.ctaidOf c).get .x)

/-- At the two substeps of the shared vector store, register 493 supplies the
preload count and register 487 supplies the total number of iterations. -/
theorem pair_store {Q L g w d t u m e} (hp : Pre Q L m) (hg : g<L.threads)
    (j : Fin 2) (site : d.site = .st9 j) (ht : (code Q L g w).AtD d t)
    (known : Known Q ((L.ctaidOf (g/L.block)).get .z) d)
    {ins : Instr} (hc : kernel.code[571]? = some ins)
    (hf : Fires 571 (eventTmpl Assumptions.all L g t ins.op) e (some u)) :
    e = ⟨571,.wr (Lib.wordAcc ⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ j.val)
      (b32 (publishValue Q L (g/L.block) j)).toBytes⟩ := by
  have sub : t.sub=j.val := by
    have sub := ht.2.1
    change t.sub=d.site.sub at sub
    rw [site] at sub
    exact sub
  let reg := fun i : Fin 2 => if i=0 then 493 else 487
  have key : reg j ∈ ctlLive d.site.pc := by rw [site]; fin_cases j <;> decide +kernel
  obtain ⟨_,_,_,_,regs⟩ := ht
  have read := holds_mem regs (mem_factsFrom key)
  have later : 41<d.site.pc := by rw [site]; change 41<571; decide
  have val : valueOf Q L g w d (reg j) = b32 (publishValue Q L (g/L.block) j) := by
    fin_cases j
    · apply congrArg b32
      exact preload_count hp hg (known.first (by omega)) (known.last (by omega)) (known.seq later)
    · exact published_iters hp hg (known.seq later)
  have op : ([Opnd.reg 493,.reg 487] : List Opnd)[j.val]? = some (.reg (reg j)) := by
    fin_cases j <;> rfl
  let v := b32 (publishValue Q L (g/L.block) j)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_571)
  change Fires 571 (eventTmpl Assumptions.all L g t
    (.mem (Lib.symStore 2 212992 [.reg 493,.reg 487]))) e (some u) at hf
  generalize Assumptions.all = A at hf
  have get := Lib.fires_st_sym (A := A) (L := L) (g := g)
    (pc := 571) (e := e) (u := u) (op := .mem (Lib.symStore 2 212992 [.reg 493,.reg 487]))
    (vec := 2) (off := 212992) (srcs := [.reg 493,.reg 487]) (t := t) rfl (by decide) sub op
    (v := v) (by simp [readValue,readReg,read,val,v,pure,Except.pure]) rfl
    (Or.inr (Or.inl rfl))
  generalize eventTmpl A L g t (.mem (Lib.symStore 2 212992 [.reg 493,.reg 487])) = tpl at hf get
  obtain ⟨v',hv,eq⟩ := get (by assumption)
  rw [storeValue_of_bytes (by rfl)] at hv
  cases hv
  have bound := hp.sharedRange
  change L.sharedBase+213340≤2^18 at bound
  change e = ⟨571,.wr (Lib.wordAcc ⟨.shared,g/L.block,(L.sharedBase+212992)%2^32+4*j.val⟩ j.val)
    v.toBytes⟩ at eq
  rw [Nat.mod_eq_of_lt (show L.sharedBase+212992<2^32 by omega)] at eq
  exact eq

end PTX.Kernels.InklingRelDecode.Proof.Prologue
