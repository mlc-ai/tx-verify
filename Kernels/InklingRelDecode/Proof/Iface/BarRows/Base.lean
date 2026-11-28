-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.BarRow
open PTX

/-- The optional thread count recorded by the CTA barrier template. -/
def recCnt (block n : Nat) : Option Nat := if n=0 ∨ n=block then none else some n

theorem barTmpl_cnt {L : Launch} {g : Nat} {t : TState} {a b : Opnd} {id n : BitVec 64}
    (ha : readBits L g t 32 a = .ok id) (hb : readBits L g t 32 b = .ok n)
    (hid : id.toNat < 16) (hn : n.toNat % 32 = 0) :
    barTmpl L g t a (some b) .sync = .bar id.toNat (next t) (recCnt L.block n.toNat) .sync := by
  simp only [barTmpl,ha,hb,recCnt,show ¬ 16 ≤ id.toNat by omega,↓reduceIte,hn,
    reduceCtorEq,false_imp_iff,and_self]

def fullZeroSites : List Nat := [12,14,2850,2853]

def halfZeroSites : List Nat :=
  [180,192,201,212,222,227,236,243,254,264,269,278,285,296,306,311,999,1012,2241,2251,2326]

end PTX.Kernels.InklingRelDecode.Proof.BarRow
