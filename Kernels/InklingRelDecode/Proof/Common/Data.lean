-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Payload
public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Lemmas.Flow.Glue

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow Arith32

noncomputable section

/-- The register values passed at pc 574. The signed quotient in 486 and
its nonnegative part in 487 remain distinct for arbitrary sequence words. -/
def dataEntry (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : Prologue.Control.D) :
    Softmax.Control.Entry :=
  let c := L.ctaidOf (g/L.block)
  let x := addi (Lib.word d.seq) 127
  let blocks := Prologue.Control.iters Q.splits (c.get .x) (Prologue.Control.div128 x)
  {base := w
   split := c.get .x
   qlen := (Prologue.Control.qlen d).toNat
   prior := Prologue.Control.subValue d.seq (Prologue.Control.subValue d.last d.first)
   nbias := (shru (Prologue.Control.positive (addi (Prologue.Control.past d) (-1023))) 7).toNat
   biasOffset := (andi (add32 x (shru (shrs x 31) 25)) (-128)).toNat
   blocks := blocks.toNat
   limit := (Prologue.Control.positive blocks).toNat
   head := c.get .y * 6
   firstWord := d.first
   stride := Q.strideRel
   splits := Q.splits
   tokens := Q.nTok
   rel := Q.relBase
   outBase := Q.oBase
   lseBase := Q.lseBase}

def dataExit (Q : Params) (L : Launch) (g : Nat) (w : Value) (d : Prologue.Control.D) :=
  if d.site = .exit then some (dataEntry Q L g w d) else none

open Classical in
/-- The address numbers of the epilogue: those of the Softmax entry when it passed the handoff
checks (`Softmax.Control.Entry.Ok`), zeros otherwise. -/
def epiAddr (e : Softmax.Control.Entry) : Epilogue.Control.Addr :=
  if h : e.firstWord.regBits.isSome ∧ e.tokens * e.split + 11 < 2^31 then
    ⟨e.split,e.head,e.tokens,e.firstWord,e.outBase,e.lseBase,h⟩
  else ⟨0,0,0,b32 0,0,0,⟨rfl,by decide⟩⟩

def epiEntry (e : Softmax.Control.Entry) (t : Nat) : Epilogue.Control.Entry :=
  ⟨e.base,decide (e.blocks=0 ∨ 2^31≤e.blocks),Softmax.Control.validRow e t,epiAddr e⟩

theorem epiEntry_eq' {e : Softmax.Control.Entry}
    (h : e.firstWord.regBits.isSome ∧ e.tokens * e.split + 11 < 2^31) (t : Nat) :
    epiEntry e t = ⟨e.base,decide (e.blocks=0 ∨ 2^31≤e.blocks),Softmax.Control.validRow e t,
      ⟨e.split,e.head,e.tokens,e.firstWord,e.outBase,e.lseBase,h⟩⟩ := by
  simp only [epiEntry, epiAddr, h.1, h.2, and_self, ↓reduceDIte]

theorem epiEntry_eq {e : Softmax.Control.Entry} (ok : e.Ok) (t : Nat) :
    epiEntry e t = ⟨e.base,decide (e.blocks=0 ∨ 2^31≤e.blocks),Softmax.Control.validRow e t,
      ⟨e.split,e.head,e.tokens,e.firstWord,e.outBase,e.lseBase,⟨ok.firstBits,ok.addrRange⟩⟩⟩ :=
  epiEntry_eq' ⟨ok.firstBits,ok.addrRange⟩ t

def epiExit (d : Softmax.Control.D) : Option Unit :=
  if d.site = .epilogue then some () else none

@[reducible] def softCode (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :=
  Code.glue (Softmax.Control.code e L g) (fun _ : Unit =>
    Epilogue.Control.code (epiEntry e (g%L.block)) L g) epiExit

@[reducible] def dataCode (Q : Params) (L : Launch) (g : Nat) (w : Value) :=
  Code.glue (Prologue.Control.checkedCode Q L g w) (fun e => softCode e L g)
    (dataExit Q L g w)

end
end PTX.Kernels.InklingRelDecode.Proof
