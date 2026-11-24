-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProASite
public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The registers of the default partition's prologue

`v_r20 L g dt` is the 64-bit stored value of `%r20` in a thread `g` whose data is `dt`: the
operation of its instruction (`wSub32` …) on the values of its operands. `table` lists every
register that is live at a site or at a checkpoint of a segment with its value, and `valueOf`
reads it (the registers carried unchanged, `%p3` and `%rd1`, are `dt.pro.rest`). The values are
the same at every site of the region; a site only decides which of them are live. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-- An abstract state: the next event and the data of the thread. -/
structure D where
  site : Site
  dt : Dat


/-- The 32-bit number a received word reads as (`Raw.word32Of`; 0 for a word without bits, at
which the machine stops: the `and.b32` that reads it faults). -/
def shW (v : Value) : Nat := (Raw.word32Of v).getD 0

/-! ### The registers -/

def v_r1 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 (tidOf L g)

def v_r2 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.tm

def v_r3 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 (tidOf L g / 32)

def v_r67 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.w67

def v_r68 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.w68

def v_r69 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.w69

def v_r70 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.w70

def v_r71 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.w71

def v_rd72 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.pro.btB

def v_r64 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 32 dt.pro.x15

def v_r65 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 32 dt.pro.x16

def v_r66 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 32 dt.pro.x17

def v_rd70 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x0

def v_rd71 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x6

def v_rd73 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x8

def v_rd74 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x9

def v_r72 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 32 dt.pro.x25

def v_rd75 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x10

def v_rd76 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 64 dt.pro.x11

def v_r149 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.cu0

def v_r150 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.cu1

def v_r151 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.sk

def v_r220 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b0

def v_r226 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b1

def v_r240 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b2

def v_r246 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b3

def v_r262 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b4

def v_r268 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 dt.b5

def v_r232 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 (shW dt.sh0)

def v_r253 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 (shW dt.sh1)

def v_r275 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  BitVec.ofNat 64 (shW dt.sh2)

def v_r17 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCta L g Dim.x

def v_r18 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCta L g Dim.y

def v_r19 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCta L g Dim.z

def v_rd110 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideU32 (v_r19 L g dt)
    (BitVec.ofInt 64 4)

def v_rd107 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd74 L g dt) (v_rd110 L g
    dt)

def v_rd108 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd107 L g dt) (BitVec.ofInt
    64 4)

def v_r20 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wSub32 (v_r150 L g dt) (v_r149 L g dt)

def v_rd109 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd73 L g dt) (v_rd110 L g
    dt)

def v_r21 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wSub32 (v_r151 L g dt) (v_r20 L g dt)

def v_r164 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r21 L g dt) (BitVec.ofInt 64
    (-1023))

def v_r165 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMaxS32 (v_r164 L g dt) (BitVec.ofInt
    64 0)

def v_r22 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrU32 (v_r165 L g dt) (BitVec.ofInt
    64 7)

def v_r166 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r21 L g dt) (BitVec.ofInt
    64 31)

def v_r167 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrU32 (v_r166 L g dt) (BitVec.ofInt
    64 25)

def v_r168 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r21 L g dt) (v_r167 L g dt)

def v_r23 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r168 L g dt) (BitVec.ofInt
    64 7)

def v_r169 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r151 L g dt) (BitVec.ofInt
    64 127)

def v_r170 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r169 L g dt) (BitVec.ofInt
    64 31)

def v_r171 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrU32 (v_r170 L g dt) (BitVec.ofInt
    64 25)

def v_r172 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r169 L g dt) (v_r171 L g dt)

def v_r173 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r172 L g dt) (BitVec.ofInt
    64 7)

def v_r24 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r172 L g dt) (BitVec.ofInt 64
    (-128))

def v_r174 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wNot32 (v_r17 L g dt)

def v_r175 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r71 L g dt) (v_r174 L g dt)

def v_r176 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r175 L g dt) (v_r173 L g dt)

def v_r25 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wDivS32 (v_r176 L g dt) (v_r71 L g dt)

def v_r26 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMaxS32 (v_r25 L g dt) (BitVec.ofInt 64
    0)

def v_r27 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r1 L g dt) (BitVec.ofInt 64
    127)

def v_r177 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wBfeU32 (v_r1 L g dt) (BitVec.ofInt 64
    3) (BitVec.ofInt 64 4)

def v_r178 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wOr32 (v_r177 L g dt) (BitVec.ofInt 64
    48)

def v_r179 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r1 L g dt) (BitVec.ofInt 64
    3)

def v_r28 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r179 L g dt) (BitVec.ofInt 64
    56)

def v_rs1 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt16of32 (v_r177 L g dt)

def v_rs2 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wOr16 (v_rs1 L g dt) (BitVec.ofInt 64
    16)

def v_rs3 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wOr16 (v_rs1 L g dt) (BitVec.ofInt 64
    32)

def v_p38 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pLtU32 (v_r178 L g dt) (BitVec.ofInt 64 60)

def v_rs4 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt16of32 (v_r178 L g dt)

def v_rs5 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulHiU16 (v_rs4 L g dt) (BitVec.ofInt
    64 10923)

def v_r180 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs5 L g dt)

def v_rs6 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulHiU16 (v_rs3 L g dt) (BitVec.ofInt
    64 10923)

def v_r181 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs6 L g dt)

def v_rs7 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulHiU16 (v_rs2 L g dt) (BitVec.ofInt
    64 10923)

def v_r182 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs7 L g dt)

def v_rs8 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulHiU16 (v_rs1 L g dt) (BitVec.ofInt
    64 10923)

def v_r183 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs8 L g dt)

def v_p81 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pGtS32 (v_r20 L g dt) (v_r183 L g dt)

def v_p82 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pGtS32 (v_r20 L g dt) (v_r182 L g dt)

def v_p83 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pGtS32 (v_r20 L g dt) (v_r181 L g dt)

def v_p39 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pGtS32 (v_r20 L g dt) (v_r180 L g dt)

def v_p84 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p38 L g dt) && (v_p39 L g dt)

def v_r184 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r149 L g dt) (v_r183 L g dt)

def v_r185 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r149 L g dt) (v_r182 L g dt)

def v_r186 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r149 L g dt) (v_r181 L g dt)

def v_r187 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r149 L g dt) (v_r180 L g dt)

def v_rd111 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideS32 (v_r65 L g dt) (v_r187 L
    g dt)

def v_rd112 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideS32 (v_r65 L g dt) (v_r186 L
    g dt)

def v_rd113 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideS32 (v_r65 L g dt) (v_r185 L
    g dt)

def v_rd114 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideS32 (v_r65 L g dt) (v_r184 L
    g dt)

def v_rd115 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl64 (v_rd114 L g dt) (BitVec.ofInt
    64 1)

def v_rd116 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd70 L g dt) (v_rd115 L g
    dt)

def v_rd117 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl64 (v_rd113 L g dt) (BitVec.ofInt
    64 1)

def v_rd118 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd70 L g dt) (v_rd117 L g
    dt)

def v_rd119 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl64 (v_rd112 L g dt) (BitVec.ofInt
    64 1)

def v_rd120 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd70 L g dt) (v_rd119 L g
    dt)

def v_rd121 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl64 (v_rd111 L g dt) (BitVec.ofInt
    64 1)

def v_rd122 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd70 L g dt) (v_rd121 L g
    dt)

def v_r29 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulLo32 (v_r18 L g dt) (BitVec.ofInt
    64 6)

def v_rs9 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl16 (v_rs5 L g dt) (BitVec.ofInt 64
    1)

def v_rs10 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd16 (v_rs4 L g dt) (v_rs9 L g dt)

def v_rs11 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl16 (v_rs6 L g dt) (BitVec.ofInt 64
    1)

def v_rs12 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd16 (v_rs1 L g dt) (v_rs11 L g dt)

def v_rs13 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl16 (v_rs7 L g dt) (BitVec.ofInt 64
    1)

def v_rs14 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd16 (v_rs1 L g dt) (v_rs13 L g dt)

def v_rs15 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl16 (v_rs8 L g dt) (BitVec.ofInt 64
    1)

def v_rs16 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd16 (v_rs1 L g dt) (v_rs15 L g dt)

def v_r188 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs16 L g dt)

def v_r189 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r188 L g dt) (BitVec.ofInt
    64 7)

def v_r190 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs14 L g dt)

def v_r191 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r190 L g dt) (BitVec.ofInt
    64 7)

def v_r192 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs12 L g dt)

def v_r193 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r192 L g dt) (BitVec.ofInt
    64 7)

def v_r194 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wCvt32of16 (v_rs10 L g dt)

def v_r195 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r194 L g dt) (BitVec.ofInt
    64 7)

def v_r196 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r29 L g dt) (v_r189 L g dt)

def v_r197 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r29 L g dt) (v_r191 L g dt)

def v_r198 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r29 L g dt) (v_r193 L g dt)

def v_r199 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r29 L g dt) (v_r195 L g dt)

def v_r200 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r196 L g dt) (BitVec.ofInt
    64 7)

def v_r201 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r197 L g dt) (BitVec.ofInt
    64 7)

def v_r202 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r198 L g dt) (BitVec.ofInt
    64 7)

def v_r203 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r199 L g dt) (BitVec.ofInt
    64 7)

def v_rd3 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideU32 (v_r200 L g dt)
    (BitVec.ofInt 64 2) (v_rd116 L g dt)

def v_rd4 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideU32 (v_r201 L g dt)
    (BitVec.ofInt 64 2) (v_rd118 L g dt)

def v_rd5 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideU32 (v_r202 L g dt)
    (BitVec.ofInt 64 2) (v_rd120 L g dt)

def v_rd6 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideU32 (v_r203 L g dt)
    (BitVec.ofInt 64 2) (v_rd122 L g dt)

def v_p40 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pEqB32 (v_r3 L g dt) (BitVec.ofInt 64 0)

def v_p26 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 130

def v_r205 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wSmem L

def v_r152 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213216)

def v_p27 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 135

def v_r153 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213248)

def v_p28 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 139

def v_r154 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213224)

def v_p29 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 143

def v_r155 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213256)

def v_p30 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 147

def v_r156 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213232)

def v_p31 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 151

def v_r157 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213264)

def v_p32 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 155

def v_r158 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213280)

def v_p33 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 159

def v_r159 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213296)

def v_p34 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 163

def v_r160 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213288)

def v_p35 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 167

def v_r161 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213304)

def v_p36 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 171

def v_r162 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213312)

def v_p37 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p40 L g dt) && dt.el 175

def v_r163 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 213328)

def v_r217 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r175 L g dt) (v_r23 L g dt)

def v_r218 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wDivS32 (v_r217 L g dt) (v_r71 L g dt)

def v_r219 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMaxS32 (v_r218 L g dt) (BitVec.ofInt
    64 0)

def v_r31 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMinS32 (v_r219 L g dt) (v_r26 L g dt)

def v_r32 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMinU32 (v_r31 L g dt) (BitVec.ofInt 64
    3)

def v_p53 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pNeB32 (v_r31 L g dt) (BitVec.ofInt 64 0)

def v_r1451 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r17 L g dt) (BitVec.ofInt
    64 7)

def v_p177 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pEqB32 (v_r27 L g dt) (BitVec.ofInt 64 0)

def v_r230 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulLo32 (v_r67 L g dt) (v_r19 L g dt)

def v_rd7 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideS32 (v_r230 L g dt)
    (BitVec.ofInt 64 4) (v_rd72 L g dt)

def v_r231 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r1451 L g dt) (BitVec.ofInt
    64 6)

def v_rd123 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideS32 (v_r231 L g dt)
    (BitVec.ofInt 64 4) (v_rd7 L g dt)

def v_r33 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulLo32 (v_r69 L g dt) (v_r18 L g dt)

def v_r223 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r220 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_r34 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulLo32 (v_r70 L g dt) (v_r18 L g dt)

def v_p59 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pLtU32 (v_r27 L g dt) (BitVec.ofInt 64 64)

def v_p54 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 203

def v_r234 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r232 L g dt) (BitVec.ofInt
    64 1)

def v_r235 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r234 L g dt) (BitVec.ofInt
    64 14)

def v_r221 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (v_r235 L g dt)

def v_r236 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r234 L g dt) (BitVec.ofInt
    64 6)

def v_r222 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r236 L g dt) (v_r34 L g dt)

def v_p55 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 213

def v_r224 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r221 L g dt) (BitVec.ofInt
    64 98304)

def v_r225 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r222 L g dt) (BitVec.ofInt
    64 128)

def v_rd124 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd123 L g dt) (BitVec.ofInt
    64 4)

def v_r228 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r226 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_p56 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 223

def v_r227 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r221 L g dt) (BitVec.ofInt
    64 8192)

def v_p57 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 228

def v_r229 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r221 L g dt) (BitVec.ofInt
    64 106496)

def v_p63 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pEqB32 (v_r31 L g dt) (BitVec.ofInt 64 1)

def v_r250 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r71 L g dt) (v_r17 L g dt)

def v_r251 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r250 L g dt) (BitVec.ofInt
    64 7)

def v_r252 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r251 L g dt) (BitVec.ofInt
    64 6)

def v_rd125 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideS32 (v_r252 L g dt)
    (BitVec.ofInt 64 4) (v_rd7 L g dt)

def v_r243 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r240 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_p64 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 245

def v_r255 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r253 L g dt) (BitVec.ofInt
    64 1)

def v_r256 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r255 L g dt) (BitVec.ofInt
    64 14)

def v_r257 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (v_r256 L g dt)

def v_r241 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r257 L g dt) (BitVec.ofInt
    64 32768)

def v_r258 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r255 L g dt) (BitVec.ofInt
    64 6)

def v_r242 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r258 L g dt) (v_r34 L g dt)

def v_p65 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 255

def v_r244 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r257 L g dt) (BitVec.ofInt
    64 131072)

def v_r245 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r242 L g dt) (BitVec.ofInt
    64 128)

def v_rd126 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd125 L g dt) (BitVec.ofInt
    64 4)

def v_r248 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r246 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_p66 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 265

def v_r247 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r257 L g dt) (BitVec.ofInt
    64 40960)

def v_p67 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 270

def v_r249 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r257 L g dt) (BitVec.ofInt
    64 139264)

def v_p72 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  pLtU32 (v_r31 L g dt) (BitVec.ofInt 64 3)

def v_r272 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r71 L g dt) (BitVec.ofInt 64
    8)

def v_r273 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r272 L g dt) (v_r1451 L g
    dt)

def v_r274 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShrS32 (v_r273 L g dt) (BitVec.ofInt
    64 6)

def v_rd127 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadWideS32 (v_r274 L g dt)
    (BitVec.ofInt 64 4) (v_rd7 L g dt)

def v_r265 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r262 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_p73 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 287

def v_r277 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r275 L g dt) (BitVec.ofInt
    64 1)

def v_r278 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r277 L g dt) (BitVec.ofInt
    64 14)

def v_r279 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (v_r278 L g dt)

def v_r263 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r279 L g dt) (BitVec.ofInt
    64 65536)

def v_r280 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r277 L g dt) (BitVec.ofInt
    64 6)

def v_r264 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r280 L g dt) (v_r34 L g dt)

def v_p74 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 297

def v_r266 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r279 L g dt) (BitVec.ofInt
    64 163840)

def v_r267 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r264 L g dt) (BitVec.ofInt
    64 128)

def v_rd128 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd127 L g dt) (BitVec.ofInt
    64 4)

def v_r270 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMadLo32 (v_r268 L g dt) (v_r68 L g
    dt) (v_r33 L g dt)

def v_p75 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 307

def v_r269 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r279 L g dt) (BitVec.ofInt
    64 73728)

def v_p76 (L : Launch) (g : Nat) (dt : Dat) : Bool :=
  (v_p59 L g dt) && dt.el 312

def v_r271 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r279 L g dt) (BitVec.ofInt
    64 172032)

def v_r30 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r2 L g dt) (BitVec.ofInt 64
    256)

/-- The word `add.s32 %r30, %r2, 256` (pc 319) writes: Core's outcome on the base word `w` the
common start loaded (`Raw.addImmE`); `b32 0` where the instruction faults (there the thread is
dead and no state holds it). For a good word it is `v_r30` (`r30Of_good`). -/
def r30Of (w : Value) : Value :=
  match Raw.addImmE w 256 with
  | .ok v => v
  | .error _ => b32 0

def v_rd257 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wMulWideU32 (v_r28 L g dt)
    (BitVec.ofInt 64 2)

def v_rd129 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd3 L g dt) (v_rd257 L g
    dt)

def v_rd130 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 2)

def v_rd131 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 4)

def v_rd132 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 6)

def v_rd133 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 8)

def v_rd134 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 10)

def v_rd135 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 12)

def v_rd136 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 14)

def v_rd137 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 128)

def v_rd138 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 130)

def v_rd139 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 132)

def v_rd140 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 134)

def v_rd141 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 136)

def v_rd142 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 138)

def v_rd143 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 140)

def v_rd144 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd129 L g dt) (BitVec.ofInt
    64 142)

def v_rd145 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd4 L g dt) (v_rd257 L g
    dt)

def v_rd146 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 2)

def v_rd147 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 4)

def v_rd148 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 6)

def v_rd149 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 8)

def v_rd150 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 10)

def v_rd151 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 12)

def v_rd152 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 14)

def v_rd153 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 128)

def v_rd154 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 130)

def v_rd155 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 132)

def v_rd156 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 134)

def v_rd157 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 136)

def v_rd158 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 138)

def v_rd159 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 140)

def v_rd160 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd145 L g dt) (BitVec.ofInt
    64 142)

def v_rd161 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd5 L g dt) (v_rd257 L g
    dt)

def v_rd162 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 2)

def v_rd163 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 4)

def v_rd164 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 6)

def v_rd165 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 8)

def v_rd166 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 10)

def v_rd167 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 12)

def v_rd168 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 14)

def v_rd169 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 128)

def v_rd170 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 130)

def v_rd171 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 132)

def v_rd172 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 134)

def v_rd173 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 136)

def v_rd174 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 138)

def v_rd175 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 140)

def v_rd176 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd161 L g dt) (BitVec.ofInt
    64 142)

def v_rd177 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd6 L g dt) (v_rd257 L g
    dt)

def v_rd178 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 2)

def v_rd179 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 4)

def v_rd180 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 6)

def v_rd181 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 8)

def v_rd182 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 10)

def v_rd183 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 12)

def v_rd184 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 14)

def v_rd185 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 128)

def v_rd186 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 130)

def v_rd187 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 132)

def v_rd188 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 134)

def v_rd189 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 136)

def v_rd190 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 138)

def v_rd191 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 140)

def v_rd192 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd64 (v_rd177 L g dt) (BitVec.ofInt
    64 142)

def v_rs18 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  truncBits 16 (BitVec.ofInt 64 0)

def v_r325 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r1 L g dt) (BitVec.ofInt 64
    4)

def v_r326 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r325 L g dt) (BitVec.ofInt
    64 2032)

def v_r327 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wShl32 (v_r1 L g dt) (BitVec.ofInt 64
    1)

def v_r328 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAnd32 (v_r327 L g dt) (BitVec.ofInt
    64 112)

def v_r329 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wXor32 (v_r326 L g dt) (v_r328 L g dt)

def v_r330 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (v_r329 L g dt)

def v_r285 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 196608)

def v_r286 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 0) (dt.q 1)

def v_r287 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 2) (dt.q 3)

def v_r288 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 4) (dt.q 5)

def v_r289 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 6) (dt.q 7)

def v_r290 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 204800)

def v_r291 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 8) (dt.q 9)

def v_r292 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 10) (dt.q 11)

def v_r293 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 12) (dt.q 13)

def v_r294 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 14) (dt.q 15)

def v_r295 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 198656)

def v_r296 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 16) (dt.q 17)

def v_r297 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 18) (dt.q 19)

def v_r298 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 20) (dt.q 21)

def v_r299 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 22) (dt.q 23)

def v_r300 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 206848)

def v_r301 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 24) (dt.q 25)

def v_r302 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 26) (dt.q 27)

def v_r303 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 28) (dt.q 29)

def v_r304 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 30) (dt.q 31)

def v_r305 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 200704)

def v_r306 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 32) (dt.q 33)

def v_r307 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 34) (dt.q 35)

def v_r308 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 36) (dt.q 37)

def v_r309 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 38) (dt.q 39)

def v_r310 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 208896)

def v_r311 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 40) (dt.q 41)

def v_r312 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 42) (dt.q 43)

def v_r313 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 44) (dt.q 45)

def v_r314 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 46) (dt.q 47)

def v_r315 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 202752)

def v_r316 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 48) (dt.q 49)

def v_r317 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 50) (dt.q 51)

def v_r318 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 52) (dt.q 53)

def v_r319 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 54) (dt.q 55)

def v_r320 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r330 L g dt) (BitVec.ofInt
    64 210944)

def v_r321 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 56) (dt.q 57)

def v_r322 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 58) (dt.q 59)

def v_r323 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 60) (dt.q 61)

def v_r324 (L : Launch) (g : Nat) (dt : Dat) : Value :=
  joinValue (dt.q 62) (dt.q 63)

def v_r331 (L : Launch) (g : Nat) (dt : Dat) : BitVec 64 :=
  wAdd32 (v_r205 L g dt) (BitVec.ofInt
    64 212992)

/-- Every register live at a site or checkpoint, with its value. -/
def table (L : Launch) (g : Nat) (dt : Dat) : List (Nat × Value) :=
  [(26, .pred true), (27, .pred true), (28, .pred true), (29, .pred true), (30, .pred true),
    (31, .pred true), (32, .pred true), (33, .pred true), (34, .pred true), (35, .pred true),
    (36, .pred true), (37, .pred true), (38, .pred (v_p38 L g dt)), (40, .pred (v_p40 L g dt)),
    (41, .pred (dt.el 130)), (42, .pred (dt.el 135)), (43, .pred (dt.el 139)),
    (44, .pred (dt.el 143)), (45, .pred (dt.el 147)), (46, .pred (dt.el 151)),
    (47, .pred (dt.el 155)), (48, .pred (dt.el 159)), (49, .pred (dt.el 163)),
    (50, .pred (dt.el 167)), (51, .pred (dt.el 171)), (52, .pred (dt.el 175)),
    (53, .pred (v_p53 L g dt)), (54, .pred true), (55, .pred true), (56, .pred true),
    (57, .pred true), (58, .pred (dt.el 203)), (59, .pred (v_p59 L g dt)),
    (60, .pred (dt.el 213)), (61, .pred (dt.el 223)), (62, .pred (dt.el 228)),
    (63, .pred (v_p63 L g dt)), (64, .pred true), (65, .pred true), (66, .pred true),
    (67, .pred true), (68, .pred (dt.el 245)), (69, .pred (dt.el 255)), (70, .pred (dt.el 265)),
    (71, .pred (dt.el 270)), (72, .pred (v_p72 L g dt)), (73, .pred true), (74, .pred true),
    (75, .pred true), (76, .pred true), (77, .pred (dt.el 287)), (78, .pred (dt.el 297)),
    (79, .pred (dt.el 307)), (80, .pred (dt.el 312)), (81, .pred (v_p81 L g dt)),
    (82, .pred (v_p82 L g dt)), (83, .pred (v_p83 L g dt)), (84, .pred (v_p84 L g dt)),
    (177, .pred (v_p177 L g dt)), (182, .bits 16 (v_rs1 L g dt)), (183, .bits 16 (v_rs2 L g dt)),
    (184, .bits 16 (v_rs3 L g dt)), (185, .bits 16 (v_rs4 L g dt)),
    (186, .bits 16 (v_rs5 L g dt)), (187, .bits 16 (v_rs6 L g dt)),
    (188, .bits 16 (v_rs7 L g dt)), (189, .bits 16 (v_rs8 L g dt)),
    (191, .bits 16 (v_rs10 L g dt)), (193, .bits 16 (v_rs12 L g dt)),
    (195, .bits 16 (v_rs14 L g dt)), (196, .bits 16 (v_rs15 L g dt)), (198, dt.q 0),
    (199, .bits 16 (v_rs18 L g dt)), (200, dt.q 1), (201, dt.q 2), (202, dt.q 3), (203, dt.q 4),
    (204, dt.q 5), (205, dt.q 6), (206, dt.q 7), (207, dt.q 8), (208, dt.q 9), (209, dt.q 10),
    (210, dt.q 11), (211, dt.q 12), (212, dt.q 13), (213, dt.q 14), (214, dt.q 15),
    (215, dt.q 16), (216, dt.q 17), (217, dt.q 18), (218, dt.q 19), (219, dt.q 20),
    (220, dt.q 21), (221, dt.q 22), (222, dt.q 23), (223, dt.q 24), (224, dt.q 25),
    (225, dt.q 26), (226, dt.q 27), (227, dt.q 28), (228, dt.q 29), (229, dt.q 30),
    (230, dt.q 31), (231, dt.q 32), (232, dt.q 33), (233, dt.q 34), (234, dt.q 35),
    (235, dt.q 36), (236, dt.q 37), (237, dt.q 38), (238, dt.q 39), (239, dt.q 40),
    (240, dt.q 41), (241, dt.q 42), (242, dt.q 43), (243, dt.q 44), (244, dt.q 45),
    (245, dt.q 46), (246, dt.q 47), (247, dt.q 48), (248, dt.q 49), (249, dt.q 50),
    (250, dt.q 51), (251, dt.q 52), (252, dt.q 53), (253, dt.q 54), (254, dt.q 55),
    (255, dt.q 56), (256, dt.q 57), (257, dt.q 58), (258, dt.q 59), (259, dt.q 60),
    (260, dt.q 61), (261, dt.q 62), (262, dt.q 63), (462, .bits 32 (v_r1 L g dt)),
    (463, dt.w), (464, .bits 32 (v_r3 L g dt)), (478, .bits 32 (v_r17 L g dt)),
    (479, .bits 32 (v_r18 L g dt)), (480, .bits 32 (v_r19 L g dt)),
    (481, .bits 32 (v_r20 L g dt)), (482, .bits 32 (v_r21 L g dt)),
    (483, .bits 32 (v_r22 L g dt)), (484, .bits 32 (v_r23 L g dt)),
    (485, .bits 32 (v_r24 L g dt)), (486, .bits 32 (v_r25 L g dt)),
    (487, .bits 32 (v_r26 L g dt)), (488, .bits 32 (v_r27 L g dt)),
    (489, .bits 32 (v_r28 L g dt)), (490, .bits 32 (v_r29 L g dt)),
    (491, r30Of dt.w), (492, .bits 32 (v_r31 L g dt)),
    (493, .bits 32 (v_r32 L g dt)), (494, .bits 32 (v_r33 L g dt)),
    (495, .bits 32 (v_r34 L g dt)), (525, .bits 32 (v_r64 L g dt)),
    (526, .bits 32 (v_r65 L g dt)), (527, .bits 32 (v_r66 L g dt)),
    (528, .bits 32 (v_r67 L g dt)), (529, .bits 32 (v_r68 L g dt)),
    (530, .bits 32 (v_r69 L g dt)), (531, .bits 32 (v_r70 L g dt)),
    (532, .bits 32 (v_r71 L g dt)), (533, .bits 32 (v_r72 L g dt)),
    (610, .bits 32 (v_r149 L g dt)), (611, .bits 32 (v_r150 L g dt)),
    (612, .bits 32 (v_r151 L g dt)), (613, .bits 32 (v_r152 L g dt)),
    (614, .bits 32 (v_r153 L g dt)), (615, .bits 32 (v_r154 L g dt)),
    (616, .bits 32 (v_r155 L g dt)), (617, .bits 32 (v_r156 L g dt)),
    (618, .bits 32 (v_r157 L g dt)), (619, .bits 32 (v_r158 L g dt)),
    (620, .bits 32 (v_r159 L g dt)), (621, .bits 32 (v_r160 L g dt)),
    (622, .bits 32 (v_r161 L g dt)), (623, .bits 32 (v_r162 L g dt)),
    (624, .bits 32 (v_r163 L g dt)), (633, .bits 32 (v_r172 L g dt)),
    (636, .bits 32 (v_r175 L g dt)), (637, .bits 32 (v_r176 L g dt)),
    (641, .bits 32 (v_r180 L g dt)), (642, .bits 32 (v_r181 L g dt)),
    (643, .bits 32 (v_r182 L g dt)), (644, .bits 32 (v_r183 L g dt)),
    (656, .bits 32 (v_r195 L g dt)), (657, .bits 32 (v_r196 L g dt)),
    (658, .bits 32 (v_r197 L g dt)), (659, .bits 32 (v_r198 L g dt)),
    (666, .bits 32 (v_r205 L g dt)), (678, .bits 32 (v_r217 L g dt)),
    (679, .bits 32 (v_r218 L g dt)), (681, .bits 32 (v_r220 L g dt)),
    (682, .bits 32 (v_r221 L g dt)), (683, .bits 32 (v_r222 L g dt)),
    (684, .bits 32 (v_r223 L g dt)), (685, .bits 32 (v_r224 L g dt)),
    (686, .bits 32 (v_r225 L g dt)), (687, .bits 32 (v_r226 L g dt)),
    (688, .bits 32 (v_r227 L g dt)), (689, .bits 32 (v_r228 L g dt)),
    (690, .bits 32 (v_r229 L g dt)), (693, dt.sh0), (695, .bits 32 (v_r234 L g dt)),
    (701, .bits 32 (v_r240 L g dt)), (702, .bits 32 (v_r241 L g dt)),
    (703, .bits 32 (v_r242 L g dt)), (704, .bits 32 (v_r243 L g dt)),
    (705, .bits 32 (v_r244 L g dt)), (706, .bits 32 (v_r245 L g dt)),
    (707, .bits 32 (v_r246 L g dt)), (708, .bits 32 (v_r247 L g dt)),
    (709, .bits 32 (v_r248 L g dt)), (710, .bits 32 (v_r249 L g dt)),
    (712, .bits 32 (v_r251 L g dt)), (714, dt.sh1), (716, .bits 32 (v_r255 L g dt)),
    (718, .bits 32 (v_r257 L g dt)), (723, .bits 32 (v_r262 L g dt)),
    (724, .bits 32 (v_r263 L g dt)), (725, .bits 32 (v_r264 L g dt)),
    (726, .bits 32 (v_r265 L g dt)), (727, .bits 32 (v_r266 L g dt)),
    (728, .bits 32 (v_r267 L g dt)), (729, .bits 32 (v_r268 L g dt)),
    (730, .bits 32 (v_r269 L g dt)), (731, .bits 32 (v_r270 L g dt)),
    (732, .bits 32 (v_r271 L g dt)), (734, .bits 32 (v_r273 L g dt)),
    (736, dt.sh2), (738, .bits 32 (v_r277 L g dt)), (740, .bits 32 (v_r279 L g dt)),
    (746, .bits 32 (v_r285 L g dt)), (747, v_r286 L g dt), (748, v_r287 L g dt),
    (749, v_r288 L g dt), (750, v_r289 L g dt), (751, .bits 32 (v_r290 L g dt)),
    (752, v_r291 L g dt), (753, v_r292 L g dt), (754, v_r293 L g dt), (755, v_r294 L g dt),
    (756, .bits 32 (v_r295 L g dt)), (757, v_r296 L g dt), (758, v_r297 L g dt),
    (759, v_r298 L g dt), (760, v_r299 L g dt), (761, .bits 32 (v_r300 L g dt)),
    (762, v_r301 L g dt), (763, v_r302 L g dt), (764, v_r303 L g dt), (765, v_r304 L g dt),
    (766, .bits 32 (v_r305 L g dt)), (767, v_r306 L g dt), (768, v_r307 L g dt),
    (769, v_r308 L g dt), (770, v_r309 L g dt), (771, .bits 32 (v_r310 L g dt)),
    (772, v_r311 L g dt), (773, v_r312 L g dt), (774, v_r313 L g dt), (775, v_r314 L g dt),
    (776, .bits 32 (v_r315 L g dt)), (777, v_r316 L g dt), (778, v_r317 L g dt),
    (779, v_r318 L g dt), (780, v_r319 L g dt), (781, .bits 32 (v_r320 L g dt)),
    (782, v_r321 L g dt), (783, v_r322 L g dt), (784, v_r323 L g dt), (785, v_r324 L g dt),
    (791, .bits 32 (v_r330 L g dt)), (792, .bits 32 (v_r331 L g dt)),
    (1912, .bits 32 (v_r1451 L g dt)), (1951, .bits 64 (v_rd3 L g dt)),
    (1952, .bits 64 (v_rd4 L g dt)), (1953, .bits 64 (v_rd5 L g dt)),
    (1954, .bits 64 (v_rd6 L g dt)), (1955, .bits 64 (v_rd7 L g dt)),
    (2018, .bits 64 (v_rd70 L g dt)), (2019, .bits 64 (v_rd71 L g dt)),
    (2020, .bits 64 (v_rd72 L g dt)), (2021, .bits 64 (v_rd73 L g dt)),
    (2022, .bits 64 (v_rd74 L g dt)), (2023, .bits 64 (v_rd75 L g dt)),
    (2024, .bits 64 (v_rd76 L g dt)), (2055, .bits 64 (v_rd107 L g dt)),
    (2056, .bits 64 (v_rd108 L g dt)), (2057, .bits 64 (v_rd109 L g dt)),
    (2058, .bits 64 (v_rd110 L g dt)), (2059, .bits 64 (v_rd111 L g dt)),
    (2060, .bits 64 (v_rd112 L g dt)), (2064, .bits 64 (v_rd116 L g dt)),
    (2066, .bits 64 (v_rd118 L g dt)), (2068, .bits 64 (v_rd120 L g dt)),
    (2070, .bits 64 (v_rd122 L g dt)), (2071, .bits 64 (v_rd123 L g dt)),
    (2072, .bits 64 (v_rd124 L g dt)), (2073, .bits 64 (v_rd125 L g dt)),
    (2074, .bits 64 (v_rd126 L g dt)), (2075, .bits 64 (v_rd127 L g dt)),
    (2076, .bits 64 (v_rd128 L g dt)), (2077, .bits 64 (v_rd129 L g dt)),
    (2078, .bits 64 (v_rd130 L g dt)), (2079, .bits 64 (v_rd131 L g dt)),
    (2080, .bits 64 (v_rd132 L g dt)), (2081, .bits 64 (v_rd133 L g dt)),
    (2082, .bits 64 (v_rd134 L g dt)), (2083, .bits 64 (v_rd135 L g dt)),
    (2084, .bits 64 (v_rd136 L g dt)), (2085, .bits 64 (v_rd137 L g dt)),
    (2086, .bits 64 (v_rd138 L g dt)), (2087, .bits 64 (v_rd139 L g dt)),
    (2088, .bits 64 (v_rd140 L g dt)), (2089, .bits 64 (v_rd141 L g dt)),
    (2090, .bits 64 (v_rd142 L g dt)), (2091, .bits 64 (v_rd143 L g dt)),
    (2092, .bits 64 (v_rd144 L g dt)), (2093, .bits 64 (v_rd145 L g dt)),
    (2094, .bits 64 (v_rd146 L g dt)), (2095, .bits 64 (v_rd147 L g dt)),
    (2096, .bits 64 (v_rd148 L g dt)), (2097, .bits 64 (v_rd149 L g dt)),
    (2098, .bits 64 (v_rd150 L g dt)), (2099, .bits 64 (v_rd151 L g dt)),
    (2100, .bits 64 (v_rd152 L g dt)), (2101, .bits 64 (v_rd153 L g dt)),
    (2102, .bits 64 (v_rd154 L g dt)), (2103, .bits 64 (v_rd155 L g dt)),
    (2104, .bits 64 (v_rd156 L g dt)), (2105, .bits 64 (v_rd157 L g dt)),
    (2106, .bits 64 (v_rd158 L g dt)), (2107, .bits 64 (v_rd159 L g dt)),
    (2108, .bits 64 (v_rd160 L g dt)), (2109, .bits 64 (v_rd161 L g dt)),
    (2110, .bits 64 (v_rd162 L g dt)), (2111, .bits 64 (v_rd163 L g dt)),
    (2112, .bits 64 (v_rd164 L g dt)), (2113, .bits 64 (v_rd165 L g dt)),
    (2114, .bits 64 (v_rd166 L g dt)), (2115, .bits 64 (v_rd167 L g dt)),
    (2116, .bits 64 (v_rd168 L g dt)), (2117, .bits 64 (v_rd169 L g dt)),
    (2118, .bits 64 (v_rd170 L g dt)), (2119, .bits 64 (v_rd171 L g dt)),
    (2120, .bits 64 (v_rd172 L g dt)), (2121, .bits 64 (v_rd173 L g dt)),
    (2122, .bits 64 (v_rd174 L g dt)), (2123, .bits 64 (v_rd175 L g dt)),
    (2124, .bits 64 (v_rd176 L g dt)), (2125, .bits 64 (v_rd177 L g dt)),
    (2126, .bits 64 (v_rd178 L g dt)), (2127, .bits 64 (v_rd179 L g dt)),
    (2128, .bits 64 (v_rd180 L g dt)), (2129, .bits 64 (v_rd181 L g dt)),
    (2130, .bits 64 (v_rd182 L g dt)), (2131, .bits 64 (v_rd183 L g dt)),
    (2132, .bits 64 (v_rd184 L g dt)), (2133, .bits 64 (v_rd185 L g dt)),
    (2134, .bits 64 (v_rd186 L g dt)), (2135, .bits 64 (v_rd187 L g dt)),
    (2136, .bits 64 (v_rd188 L g dt)), (2137, .bits 64 (v_rd189 L g dt)),
    (2138, .bits 64 (v_rd190 L g dt)), (2139, .bits 64 (v_rd191 L g dt)),
    (2140, .bits 64 (v_rd192 L g dt)), (2205, .bits 64 (v_rd257 L g dt))]

/-- The value of register `r`: the table's, else the register the partition carries. -/
def valueOf (L : Launch) (g : Nat) (dt : Dat) (r : Nat) : Value :=
  ((table L g dt).lookup r).getD (dt.pro.rest r)

/-- The registers live at `pc` with their values. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (dt : Dat) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g dt)

/-- The facts of a state: the registers live at its site. -/
abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d.dt

theorem valueOf_463 {L : Launch} {g : Nat} (dt : Dat) : valueOf L g dt 463 = dt.w := by
  simp [valueOf, table, PTX.Flow.lookupLit]

theorem valueOf_491 {L : Launch} {g : Nat} (dt : Dat) : valueOf L g dt 491 = r30Of dt.w := by
  simp [valueOf, table, PTX.Flow.lookupLit]

/-- For a good base word, `%r30` is the base word plus 256 (`v_r30`). -/
theorem r30Of_good {L : Launch} {g : Nat} {dt : Dat} (h : dt.w = b32 dt.pro.tm) :
    r30Of dt.w = .bits 32 (v_r30 L g dt) := by
  rw [h]
  simp [r30Of, Raw.addImmE, b32, Value.regBits, v_r30, v_r2, wAdd32]

/-- The sub-step of a state: the element of a vector store. -/
def sub (d : D) : Nat := d.site.sub

/-- The accumulator of a state: no vector load is in progress. -/
def acc (_ : D) : List Value := []

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
