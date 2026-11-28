-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent

@[expose] public section

/-! # The counts of the data positions before a `tcgen05` event

`tcVec pc i R e` is the list of the numbers of earlier events at the positions of `dataPcs`, in
that order, for a lane about to make a collective `tcgen05` event at `pc`: in round `i` of the
Softmax loop with `R` visits of the optional rendezvous (pc 2326) counted; in the epilogue
(`i` is the launch's loop count); at the deallocation (pc 2851) with `e` the number of the
epilogue's loads. Startup events have no earlier data event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

def tcVec (pc i R e : Nat) : List Nat :=
  if pc = 1265 then [i,i,R,R,R,R,i,i,0,0]
  else if pc = 1298 then [i+1,i,R,R,R,R,i,i,0,0]
  else if pc = 2260 then [i+1,i+1,R,R,R,R,i,i,0,0]
  else if pc = 2261 then [i+1,i+1,R+1,R,R,R,i,i,0,0]
  else if pc = 2328 then [i+1,i+1,R,R,R-1,R-1,i,i,0,0]
  else if pc = 2329 then [i+1,i+1,R,R,R,R-1,i,i,0,0]
  else if pc = 1009 then [i+1,i+1,R,R,R,R,i,i,0,0]
  else if pc = 1010 then [i+1,i+1,R,R,R,R,i+1,i,0,0]
  else if pc = 2607 then [i,i,R,R,R,R,i,i,0,0]
  else if pc = 2608 then [i,i,R,R,R,R,i,i,1,0]
  else if pc = 2851 then [i,i,R,R,R,R,i,i,e,e]
  else [0,0,0,0,0,0,0,0,0,0]

/-- The positions of the collective `tcgen05` events that have earlier data events. -/
def tcVecPcs : List Nat := dataPcs ++ [2851]

theorem tcVec_off {pc i R e : Nat} (h : pc ∉ tcVecPcs) :
    tcVec pc i R e = [0,0,0,0,0,0,0,0,0,0] := by
  simp only [tcVecPcs,dataPcs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    not_or] at h
  unfold tcVec
  obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩,h11⟩ := h
  simp only [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,↓reduceIte]

/-- The loop's collective positions. -/
def loopTcPcs : List Nat := [1265,1298,2260,2261,2328,2329,1009,1010]

/-- The mandatory rendezvous passed before a Tensor Memory collective of the loop, beyond four per
earlier round and less the two the first round omits: the score load sits before the round's first
one (after both omitted ones in round zero), the accumulator load and store before the third, the
probability store before the last. -/
def softPos (pc i : Nat) : Nat :=
  if pc = 1265 then (if i = 0 then 2 else 0) else if pc = 1009 then 3 else 2

end PTX.Kernels.InklingRelDecode.Proof.Lib
