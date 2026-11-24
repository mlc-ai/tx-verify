-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxTable
public import Lemmas.Flow.OutRun
public import Lemmas.Flow.SegTwoDead

@[expose] public section

/-! # The outcome runs of the softmax arithmetic

The floating code of a tile, as pieces (`Piece`): runs of instructions on any values
(`OutRun`'s items, generated from the PTX) and the instances of the software `exp2` template
(`Assumptions.swExp2`, with the registers of their slots). A list of pieces takes facts by a
value function `V` to facts by `chainV V ps`, under `chainCond V ps` (the condition of each
piece on the values before it: no instruction faults, the software `exp2`'s inputs read as
numbers); otherwise the thread is dead (`ArithBase`). The conditions of the machine's
transitions (`SoftmaxReads`) are these conditions on the table of the state. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### The software `exp2` instances -/

/-- The software `exp2` instance at `2121`. -/
def m2121 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Define
  reg :=
    [(.y1, 1021), (.o1, 5479), (.xe1, 5478), (.fe1, 5477), (.xr1, 5476), (.y0, 1018), (.o0, 5475),
     (.xe0, 5474), (.fe0, 5473), (.xr0, 5472), (.q1, 1023), (.q0, 1020), (.p3, 4256), (.c0, 4255),
     (.k0, 1836), (.p2, 4254), (.c1, 4253), (.k1, 1835), (.p1, 4252), (.c3, 4251), (.k3, 1834),
     (.c2, 4250), (.k2, 1833), (.f, 4249), (.s, 4248), (.ri1, 1022), (.ri0, 1019), (.r, 4247),
     (.cM, 4246), (.kM, 1832), (.a, 4245), (.m1, 1831), (.x1, 1725), (.m0, 1830), (.x0, 1724)]
  stop := 2152


/-- The software `exp2` instance at `2152`. -/
def m2152 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1027), (.o1, 5487), (.xe1, 5486), (.fe1, 5485), (.xr1, 5484), (.y0, 1024), (.o0, 5483),
     (.xe0, 5482), (.fe0, 5481), (.xr0, 5480), (.q1, 1029), (.q0, 1026), (.p3, 4263), (.c0, 4255),
     (.p2, 4262), (.c1, 4253), (.p1, 4261), (.c2, 4250), (.c3, 4251), (.f, 4260), (.s, 4259),
     (.ri1, 1028), (.ri0, 1025), (.r, 4258), (.cM, 4246), (.a, 4257), (.m1, 1838), (.x1, 1727),
     (.m0, 1837), (.x0, 1726)]
  stop := 2173


/-- The software `exp2` instance at `2179`. -/
def m2179 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1033), (.o1, 5495), (.xe1, 5494), (.fe1, 5493), (.xr1, 5492), (.y0, 1030), (.o0, 5491),
     (.xe0, 5490), (.fe0, 5489), (.xr0, 5488), (.q1, 1035), (.q0, 1032), (.p3, 4270), (.c0, 4255),
     (.p2, 4269), (.c1, 4253), (.p1, 4268), (.c2, 4250), (.c3, 4251), (.f, 4267), (.s, 4266),
     (.ri1, 1034), (.ri0, 1031), (.r, 4265), (.cM, 4246), (.a, 4264), (.m1, 1840), (.x1, 1735),
     (.m0, 1839), (.x0, 1734)]
  stop := 2200


/-- The software `exp2` instance at `2200`. -/
def m2200 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1039), (.o1, 5503), (.xe1, 5502), (.fe1, 5501), (.xr1, 5500), (.y0, 1036), (.o0, 5499),
     (.xe0, 5498), (.fe0, 5497), (.xr0, 5496), (.q1, 1041), (.q0, 1038), (.p3, 4277), (.c0, 4255),
     (.p2, 4276), (.c1, 4253), (.p1, 4275), (.c2, 4250), (.c3, 4251), (.f, 4274), (.s, 4273),
     (.ri1, 1040), (.ri0, 1037), (.r, 4272), (.cM, 4246), (.a, 4271), (.m1, 1842), (.x1, 1737),
     (.m0, 1841), (.x0, 1736)]
  stop := 2221


/-- The software `exp2` instance at `2227`. -/
def m2227 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1045), (.o1, 5511), (.xe1, 5510), (.fe1, 5509), (.xr1, 5508), (.y0, 1042), (.o0, 5507),
     (.xe0, 5506), (.fe0, 5505), (.xr0, 5504), (.q1, 1047), (.q0, 1044), (.p3, 4284), (.c0, 4255),
     (.p2, 4283), (.c1, 4253), (.p1, 4282), (.c2, 4250), (.c3, 4251), (.f, 4281), (.s, 4280),
     (.ri1, 1046), (.ri0, 1043), (.r, 4279), (.cM, 4246), (.a, 4278), (.m1, 1844), (.x1, 1745),
     (.m0, 1843), (.x0, 1744)]
  stop := 2248


/-- The software `exp2` instance at `2248`. -/
def m2248 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1051), (.o1, 5519), (.xe1, 5518), (.fe1, 5517), (.xr1, 5516), (.y0, 1048), (.o0, 5515),
     (.xe0, 5514), (.fe0, 5513), (.xr0, 5512), (.q1, 1053), (.q0, 1050), (.p3, 4291), (.c0, 4255),
     (.p2, 4290), (.c1, 4253), (.p1, 4289), (.c2, 4250), (.c3, 4251), (.f, 4288), (.s, 4287),
     (.ri1, 1052), (.ri0, 1049), (.r, 4286), (.cM, 4246), (.a, 4285), (.m1, 1846), (.x1, 1747),
     (.m0, 1845), (.x0, 1746)]
  stop := 2269


/-- The software `exp2` instance at `2301`. -/
def m2301 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1057), (.o1, 5527), (.xe1, 5526), (.fe1, 5525), (.xr1, 5524), (.y0, 1054), (.o0, 5523),
     (.xe0, 5522), (.fe0, 5521), (.xr0, 5520), (.q1, 1059), (.q0, 1056), (.p3, 4306), (.c0, 4255),
     (.p2, 4305), (.c1, 4253), (.p1, 4304), (.c2, 4250), (.c3, 4251), (.f, 4303), (.s, 4302),
     (.ri1, 1058), (.ri0, 1055), (.r, 4301), (.cM, 4246), (.a, 4300), (.m1, 1864), (.x1, 1757),
     (.m0, 1863), (.x0, 1756)]
  stop := 2322


/-- The software `exp2` instance at `2322`. -/
def m2322 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1063), (.o1, 5535), (.xe1, 5534), (.fe1, 5533), (.xr1, 5532), (.y0, 1060), (.o0, 5531),
     (.xe0, 5530), (.fe0, 5529), (.xr0, 5528), (.q1, 1065), (.q0, 1062), (.p3, 4313), (.c0, 4255),
     (.p2, 4312), (.c1, 4253), (.p1, 4311), (.c2, 4250), (.c3, 4251), (.f, 4310), (.s, 4309),
     (.ri1, 1064), (.ri0, 1061), (.r, 4308), (.cM, 4246), (.a, 4307), (.m1, 1866), (.x1, 1759),
     (.m0, 1865), (.x0, 1758)]
  stop := 2343


/-- The software `exp2` instance at `2349`. -/
def m2349 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1069), (.o1, 5543), (.xe1, 5542), (.fe1, 5541), (.xr1, 5540), (.y0, 1066), (.o0, 5539),
     (.xe0, 5538), (.fe0, 5537), (.xr0, 5536), (.q1, 1071), (.q0, 1068), (.p3, 4320), (.c0, 4255),
     (.p2, 4319), (.c1, 4253), (.p1, 4318), (.c2, 4250), (.c3, 4251), (.f, 4317), (.s, 4316),
     (.ri1, 1070), (.ri0, 1067), (.r, 4315), (.cM, 4246), (.a, 4314), (.m1, 1868), (.x1, 1767),
     (.m0, 1867), (.x0, 1766)]
  stop := 2370


/-- The software `exp2` instance at `2370`. -/
def m2370 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1075), (.o1, 5551), (.xe1, 5550), (.fe1, 5549), (.xr1, 5548), (.y0, 1072), (.o0, 5547),
     (.xe0, 5546), (.fe0, 5545), (.xr0, 5544), (.q1, 1077), (.q0, 1074), (.p3, 4327), (.c0, 4255),
     (.p2, 4326), (.c1, 4253), (.p1, 4325), (.c2, 4250), (.c3, 4251), (.f, 4324), (.s, 4323),
     (.ri1, 1076), (.ri0, 1073), (.r, 4322), (.cM, 4246), (.a, 4321), (.m1, 1870), (.x1, 1769),
     (.m0, 1869), (.x0, 1768)]
  stop := 2391


/-- The software `exp2` instance at `2397`. -/
def m2397 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1081), (.o1, 5559), (.xe1, 5558), (.fe1, 5557), (.xr1, 5556), (.y0, 1078), (.o0, 5555),
     (.xe0, 5554), (.fe0, 5553), (.xr0, 5552), (.q1, 1083), (.q0, 1080), (.p3, 4334), (.c0, 4255),
     (.p2, 4333), (.c1, 4253), (.p1, 4332), (.c2, 4250), (.c3, 4251), (.f, 4331), (.s, 4330),
     (.ri1, 1082), (.ri0, 1079), (.r, 4329), (.cM, 4246), (.a, 4328), (.m1, 1872), (.x1, 1777),
     (.m0, 1871), (.x0, 1776)]
  stop := 2418


/-- The software `exp2` instance at `2418`. -/
def m2418 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1087), (.o1, 5567), (.xe1, 5566), (.fe1, 5565), (.xr1, 5564), (.y0, 1084), (.o0, 5563),
     (.xe0, 5562), (.fe0, 5561), (.xr0, 5560), (.q1, 1089), (.q0, 1086), (.p3, 4341), (.c0, 4255),
     (.p2, 4340), (.c1, 4253), (.p1, 4339), (.c2, 4250), (.c3, 4251), (.f, 4338), (.s, 4337),
     (.ri1, 1088), (.ri0, 1085), (.r, 4336), (.cM, 4246), (.a, 4335), (.m1, 1874), (.x1, 1779),
     (.m0, 1873), (.x0, 1778)]
  stop := 2439


/-- The software `exp2` instance at `3136`. -/
def m3136 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Define
  reg :=
    [(.y1, 1984), (.o1, 5577), (.xe1, 5576), (.fe1, 5575), (.xr1, 5574), (.y0, 1981), (.o0, 5573),
     (.xe0, 5572), (.fe0, 5571), (.xr0, 5570), (.q1, 1986), (.q0, 1983), (.p3, 4574), (.c0, 4573),
     (.k0, 2549), (.p2, 4572), (.c1, 4571), (.k1, 2548), (.p1, 4570), (.c3, 4569), (.k3, 2547),
     (.c2, 4568), (.k2, 2546), (.f, 4567), (.s, 4566), (.ri1, 1985), (.ri0, 1982), (.r, 4565),
     (.cM, 4564), (.kM, 2545), (.a, 4563), (.m1, 2544), (.x1, 2438), (.m0, 2543), (.x0, 2437)]
  stop := 3167


/-- The software `exp2` instance at `3167`. -/
def m3167 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1990), (.o1, 5585), (.xe1, 5584), (.fe1, 5583), (.xr1, 5582), (.y0, 1987), (.o0, 5581),
     (.xe0, 5580), (.fe0, 5579), (.xr0, 5578), (.q1, 1992), (.q0, 1989), (.p3, 4581), (.c0, 4573),
     (.p2, 4580), (.c1, 4571), (.p1, 4579), (.c2, 4568), (.c3, 4569), (.f, 4578), (.s, 4577),
     (.ri1, 1991), (.ri0, 1988), (.r, 4576), (.cM, 4564), (.a, 4575), (.m1, 2551), (.x1, 2440),
     (.m0, 2550), (.x0, 2439)]
  stop := 3188


/-- The software `exp2` instance at `3194`. -/
def m3194 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 1996), (.o1, 5593), (.xe1, 5592), (.fe1, 5591), (.xr1, 5590), (.y0, 1993), (.o0, 5589),
     (.xe0, 5588), (.fe0, 5587), (.xr0, 5586), (.q1, 1998), (.q0, 1995), (.p3, 4588), (.c0, 4573),
     (.p2, 4587), (.c1, 4571), (.p1, 4586), (.c2, 4568), (.c3, 4569), (.f, 4585), (.s, 4584),
     (.ri1, 1997), (.ri0, 1994), (.r, 4583), (.cM, 4564), (.a, 4582), (.m1, 2553), (.x1, 2448),
     (.m0, 2552), (.x0, 2447)]
  stop := 3215


/-- The software `exp2` instance at `3215`. -/
def m3215 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2002), (.o1, 5601), (.xe1, 5600), (.fe1, 5599), (.xr1, 5598), (.y0, 1999), (.o0, 5597),
     (.xe0, 5596), (.fe0, 5595), (.xr0, 5594), (.q1, 2004), (.q0, 2001), (.p3, 4595), (.c0, 4573),
     (.p2, 4594), (.c1, 4571), (.p1, 4593), (.c2, 4568), (.c3, 4569), (.f, 4592), (.s, 4591),
     (.ri1, 2003), (.ri0, 2000), (.r, 4590), (.cM, 4564), (.a, 4589), (.m1, 2555), (.x1, 2450),
     (.m0, 2554), (.x0, 2449)]
  stop := 3236


/-- The software `exp2` instance at `3242`. -/
def m3242 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2008), (.o1, 5609), (.xe1, 5608), (.fe1, 5607), (.xr1, 5606), (.y0, 2005), (.o0, 5605),
     (.xe0, 5604), (.fe0, 5603), (.xr0, 5602), (.q1, 2010), (.q0, 2007), (.p3, 4602), (.c0, 4573),
     (.p2, 4601), (.c1, 4571), (.p1, 4600), (.c2, 4568), (.c3, 4569), (.f, 4599), (.s, 4598),
     (.ri1, 2009), (.ri0, 2006), (.r, 4597), (.cM, 4564), (.a, 4596), (.m1, 2557), (.x1, 2458),
     (.m0, 2556), (.x0, 2457)]
  stop := 3263


/-- The software `exp2` instance at `3263`. -/
def m3263 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2014), (.o1, 5617), (.xe1, 5616), (.fe1, 5615), (.xr1, 5614), (.y0, 2011), (.o0, 5613),
     (.xe0, 5612), (.fe0, 5611), (.xr0, 5610), (.q1, 2016), (.q0, 2013), (.p3, 4609), (.c0, 4573),
     (.p2, 4608), (.c1, 4571), (.p1, 4607), (.c2, 4568), (.c3, 4569), (.f, 4606), (.s, 4605),
     (.ri1, 2015), (.ri0, 2012), (.r, 4604), (.cM, 4564), (.a, 4603), (.m1, 2559), (.x1, 2460),
     (.m0, 2558), (.x0, 2459)]
  stop := 3284


/-- The software `exp2` instance at `3316`. -/
def m3316 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2020), (.o1, 5625), (.xe1, 5624), (.fe1, 5623), (.xr1, 5622), (.y0, 2017), (.o0, 5621),
     (.xe0, 5620), (.fe0, 5619), (.xr0, 5618), (.q1, 2022), (.q0, 2019), (.p3, 4624), (.c0, 4573),
     (.p2, 4623), (.c1, 4571), (.p1, 4622), (.c2, 4568), (.c3, 4569), (.f, 4621), (.s, 4620),
     (.ri1, 2021), (.ri0, 2018), (.r, 4619), (.cM, 4564), (.a, 4618), (.m1, 2577), (.x1, 2470),
     (.m0, 2576), (.x0, 2469)]
  stop := 3337


/-- The software `exp2` instance at `3337`. -/
def m3337 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2026), (.o1, 5633), (.xe1, 5632), (.fe1, 5631), (.xr1, 5630), (.y0, 2023), (.o0, 5629),
     (.xe0, 5628), (.fe0, 5627), (.xr0, 5626), (.q1, 2028), (.q0, 2025), (.p3, 4631), (.c0, 4573),
     (.p2, 4630), (.c1, 4571), (.p1, 4629), (.c2, 4568), (.c3, 4569), (.f, 4628), (.s, 4627),
     (.ri1, 2027), (.ri0, 2024), (.r, 4626), (.cM, 4564), (.a, 4625), (.m1, 2579), (.x1, 2472),
     (.m0, 2578), (.x0, 2471)]
  stop := 3358


/-- The software `exp2` instance at `3364`. -/
def m3364 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2032), (.o1, 5641), (.xe1, 5640), (.fe1, 5639), (.xr1, 5638), (.y0, 2029), (.o0, 5637),
     (.xe0, 5636), (.fe0, 5635), (.xr0, 5634), (.q1, 2034), (.q0, 2031), (.p3, 4638), (.c0, 4573),
     (.p2, 4637), (.c1, 4571), (.p1, 4636), (.c2, 4568), (.c3, 4569), (.f, 4635), (.s, 4634),
     (.ri1, 2033), (.ri0, 2030), (.r, 4633), (.cM, 4564), (.a, 4632), (.m1, 2581), (.x1, 2480),
     (.m0, 2580), (.x0, 2479)]
  stop := 3385


/-- The software `exp2` instance at `3385`. -/
def m3385 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2038), (.o1, 5649), (.xe1, 5648), (.fe1, 5647), (.xr1, 5646), (.y0, 2035), (.o0, 5645),
     (.xe0, 5644), (.fe0, 5643), (.xr0, 5642), (.q1, 2040), (.q0, 2037), (.p3, 4645), (.c0, 4573),
     (.p2, 4644), (.c1, 4571), (.p1, 4643), (.c2, 4568), (.c3, 4569), (.f, 4642), (.s, 4641),
     (.ri1, 2039), (.ri0, 2036), (.r, 4640), (.cM, 4564), (.a, 4639), (.m1, 2583), (.x1, 2482),
     (.m0, 2582), (.x0, 2481)]
  stop := 3406


/-- The software `exp2` instance at `3412`. -/
def m3412 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2044), (.o1, 5657), (.xe1, 5656), (.fe1, 5655), (.xr1, 5654), (.y0, 2041), (.o0, 5653),
     (.xe0, 5652), (.fe0, 5651), (.xr0, 5650), (.q1, 2046), (.q0, 2043), (.p3, 4652), (.c0, 4573),
     (.p2, 4651), (.c1, 4571), (.p1, 4650), (.c2, 4568), (.c3, 4569), (.f, 4649), (.s, 4648),
     (.ri1, 2045), (.ri0, 2042), (.r, 4647), (.cM, 4564), (.a, 4646), (.m1, 2585), (.x1, 2490),
     (.m0, 2584), (.x0, 2489)]
  stop := 3433


/-- The software `exp2` instance at `3433`. -/
def m3433 : Assumption.SegMatch Assumption.CuteSlot where
  shape := Assumption.cuteExp2Reuse
  reg :=
    [(.y1, 2050), (.o1, 5665), (.xe1, 5664), (.fe1, 5663), (.xr1, 5662), (.y0, 2047), (.o0, 5661),
     (.xe0, 5660), (.fe0, 5659), (.xr0, 5658), (.q1, 2052), (.q0, 2049), (.p3, 4659), (.c0, 4573),
     (.p2, 4658), (.c1, 4571), (.p1, 4657), (.c2, 4568), (.c3, 4569), (.f, 4656), (.s, 4655),
     (.ri1, 2051), (.ri0, 2048), (.r, 4654), (.cM, 4564), (.a, 4653), (.m1, 2587), (.x1, 2492),
     (.m0, 2586), (.x0, 2491)]
  stop := 3454

/-! ### Pieces -/

/-- A piece of an arithmetic segment: a run of items, or an instance of the software `exp2`. -/
inductive Piece where
  | run (items : List OItem)
  | sw (m : Assumption.SegMatch Assumption.CuteSlot)

/-- The values after a piece. -/
def Piece.apply (V : Nat → Value) : Piece → Nat → Value
  | .run items => oFinal V items
  | .sw m => valueEx V (segVals m Assumption.cuteExp2.fn .y0 .y1 (rd32 (V (m.regOf .x0)))
      (rd32 (V (m.regOf .x1))))

/-- The condition of a piece: the run's, or the instance's inputs read as numbers. -/
def Piece.cond (V : Nat → Value) : Piece → Prop
  | .run items => oCond V items
  | .sw m => (∃ x, valFloat .f32 (V (m.regOf .x0)) = .ok x) ∧
      ∃ y, valFloat .f32 (V (m.regOf .x1)) = .ok y

/-- The local steps of a piece. -/
def Piece.len : Piece → Nat
  | .run items => items.length
  | .sw _ => 1

/-- The `pc` after a piece from `pc`. -/
def Piece.stop (pc : Nat) : Piece → Nat
  | .run items => pc + items.length
  | .sw m => m.stop

/-- The values after a list of pieces. -/
def chainV (V : Nat → Value) : List Piece → Nat → Value
  | [] => V
  | p :: ps => chainV (p.apply V) ps

/-- The condition of a list of pieces. -/
def chainCond (V : Nat → Value) : List Piece → Prop
  | [] => True
  | p :: ps => p.cond V ∧ chainCond (p.apply V) ps

/-- The local steps of a list of pieces. -/
def chainLen : List Piece → Nat
  | [] => 0
  | p :: ps => p.len + chainLen ps

/-- The `pc` after a list of pieces from `pc`. -/
def chainStop (pc : Nat) : List Piece → Nat
  | [] => pc
  | p :: ps => chainStop (p.stop pc) ps

/-! ### The runs (generated from the PTX) -/

/-- The first tile's exponential run from `1863`. -/
def exp0A_1863 : List OItem :=
  [.mul false 1683 3901 1682, .movImm 1684 0, .sub false 1685 1684 1683, .pack 4107 1685 1685,
   .pack 4108 1237 1239, .fma2 4110 4108 4109 4107, .unpack 1686 1687 4110, .pack 4111 1243 1245,
   .fma2 4112 4111 4109 4107, .unpack 1688 1689 4112, .pack 4113 1249 1251,
   .fma2 4114 4113 4109 4107, .unpack 1690 1691 4114, .pack 4115 1255 1257,
   .fma2 4116 4115 4109 4107, .unpack 1692 1693 4116, .pack 4117 1261 1263,
   .fma2 4118 4117 4109 4107, .unpack 1694 1695 4118, .pack 4119 1267 1269,
   .fma2 4120 4119 4109 4107, .unpack 1696 1697 4120, .pack 4121 1273 1275,
   .fma2 4122 4121 4109 4107, .unpack 1698 1699 4122, .pack 4123 1279 1281,
   .fma2 4124 4123 4109 4107, .unpack 1700 1701 4124, .pack 4125 1285 1287,
   .fma2 4126 4125 4109 4107, .unpack 1702 1703 4126, .pack 4127 1291 1293,
   .fma2 4128 4127 4109 4107, .unpack 1704 1705 4128, .pack 4129 1297 1299,
   .fma2 4130 4129 4109 4107, .unpack 1706 1707 4130, .pack 4131 1303 1305,
   .fma2 4132 4131 4109 4107, .unpack 1708 1709 4132, .pack 4133 1309 1311,
   .fma2 4134 4133 4109 4107, .unpack 1710 1711 4134, .pack 4135 1315 1317,
   .fma2 4136 4135 4109 4107, .unpack 1712 1713 4136, .pack 4137 1321 1323,
   .fma2 4138 4137 4109 4107, .unpack 1714 1715 4138, .pack 4139 1327 1328,
   .fma2 4140 4139 4109 4107, .unpack 1716 1717 4140, .pack 4141 1333 1335,
   .fma2 4142 4141 4109 4107, .unpack 1718 1719 4142, .pack 4143 1339 1341,
   .fma2 4144 4143 4109 4107, .unpack 1720 1721 4144, .pack 4145 1345 1347,
   .fma2 4146 4145 4109 4107, .unpack 1722 1723 4146, .pack 4147 1351 1353,
   .fma2 4148 4147 4109 4107, .unpack 1724 1725 4148, .pack 4149 1357 1359,
   .fma2 4150 4149 4109 4107, .unpack 1726 1727 4150, .pack 4151 1363 1365,
   .fma2 4152 4151 4109 4107, .unpack 1728 1729 4152, .pack 4153 1369 1371,
   .fma2 4154 4153 4109 4107, .unpack 1730 1731 4154, .pack 4155 1375 1377,
   .fma2 4156 4155 4109 4107, .unpack 1732 1733 4156, .pack 4157 1381 1383,
   .fma2 4158 4157 4109 4107, .unpack 1734 1735 4158, .pack 4159 1387 1389,
   .fma2 4160 4159 4109 4107, .unpack 1736 1737 4160, .pack 4161 1393 1395,
   .fma2 4162 4161 4109 4107, .unpack 1738 1739 4162, .pack 4163 1399 1401,
   .fma2 4164 4163 4109 4107, .unpack 1740 1741 4164, .pack 4165 1405 1407,
   .fma2 4166 4165 4109 4107, .unpack 1742 1743 4166, .pack 4167 1411 1413,
   .fma2 4168 4167 4109 4107, .unpack 1744 1745 4168, .pack 4169 1417 1419,
   .fma2 4170 4169 4109 4107, .unpack 1746 1747 4170, .pack 4171 1423 1424,
   .fma2 4172 4171 4109 4107, .unpack 1748 1749 4172, .pack 4173 1429 1431,
   .fma2 4174 4173 4109 4107, .unpack 1750 1751 4174, .pack 4175 1435 1437,
   .fma2 4176 4175 4109 4107, .unpack 1752 1753 4176, .pack 4177 1441 1443,
   .fma2 4178 4177 4109 4107, .unpack 1754 1755 4178, .pack 4179 1447 1449,
   .fma2 4180 4179 4109 4107, .unpack 1756 1757 4180, .pack 4181 1453 1455,
   .fma2 4182 4181 4109 4107, .unpack 1758 1759 4182, .pack 4183 1459 1461,
   .fma2 4184 4183 4109 4107, .unpack 1760 1761 4184, .pack 4185 1465 1467,
   .fma2 4186 4185 4109 4107, .unpack 1762 1763 4186, .pack 4187 1471 1473,
   .fma2 4188 4187 4109 4107, .unpack 1764 1765 4188, .pack 4189 1477 1479,
   .fma2 4190 4189 4109 4107, .unpack 1766 1767 4190, .pack 4191 1483 1485,
   .fma2 4192 4191 4109 4107, .unpack 1768 1769 4192, .pack 4193 1489 1491,
   .fma2 4194 4193 4109 4107, .unpack 1770 1771 4194, .pack 4195 1495 1497,
   .fma2 4196 4195 4109 4107, .unpack 1772 1773 4196, .pack 4197 1501 1503,
   .fma2 4198 4197 4109 4107, .unpack 1774 1775 4198, .pack 4199 1507 1509,
   .fma2 4200 4199 4109 4107, .unpack 1776 1777 4200, .pack 4201 1513 1515,
   .fma2 4202 4201 4109 4107, .unpack 1778 1779 4202, .pack 4203 1519 1520,
   .fma2 4204 4203 4109 4107, .unpack 1780 1781 4204, .pack 4205 1525 1527,
   .fma2 4206 4205 4109 4107, .unpack 1782 1783 4206, .pack 4207 1531 1533,
   .fma2 4208 4207 4109 4107, .unpack 1784 1785 4208, .pack 4209 1537 1539,
   .fma2 4210 4209 4109 4107, .unpack 1786 1787 4210, .pack 4211 1543 1545,
   .fma2 4212 4211 4109 4107, .unpack 1788 1789 4212, .pack 4213 1549 1551,
   .fma2 4214 4213 4109 4107, .unpack 1790 1791 4214, .pack 4215 1555 1557,
   .fma2 4216 4215 4109 4107, .unpack 1792 1793 4216, .pack 4217 1561 1563,
   .fma2 4218 4217 4109 4107, .unpack 1794 1795 4218, .pack 4219 1567 1569,
   .fma2 4220 4219 4109 4107, .unpack 1796 1797 4220, .pack 4221 1573 1575,
   .fma2 4222 4221 4109 4107, .unpack 1798 1799 4222, .pack 4223 1579 1581,
   .fma2 4224 4223 4109 4107, .unpack 1800 1801 4224, .pack 4225 1585 1587,
   .fma2 4226 4225 4109 4107, .unpack 1802 1803 4226, .pack 4227 1591 1593,
   .fma2 4228 4227 4109 4107, .unpack 1804 1805 4228, .pack 4229 1597 1599,
   .fma2 4230 4229 4109 4107, .unpack 1806 1807 4230, .pack 4231 1603 1605,
   .fma2 4232 4231 4109 4107, .unpack 1808 1809 4232, .pack 4233 1609 1611,
   .fma2 4234 4233 4109 4107, .unpack 1810 1811 4234, .pack 4235 1615 1616,
   .fma2 4236 4235 4109 4107, .unpack 1812 1813 4236, .ex2 true 408 1686, .ex2 true 409 1687,
   .ex2 true 410 1688, .ex2 true 411 1689, .ex2 true 412 1690, .ex2 true 413 1691,
   .ex2 true 414 1692, .ex2 true 415 1693, .ex2 true 416 1694, .ex2 true 417 1695,
   .ex2 true 418 1696, .ex2 true 419 1697, .ex2 true 420 1698, .ex2 true 421 1699,
   .ex2 true 422 1700, .ex2 true 423 1701, .ex2 true 424 1702, .ex2 true 425 1703,
   .ex2 true 426 1704, .ex2 true 427 1705, .ex2 true 428 1706, .ex2 true 429 1707,
   .ex2 true 430 1708, .ex2 true 431 1709, .ex2 true 432 1710, .ex2 true 433 1711,
   .ex2 true 434 1712, .ex2 true 435 1713, .ex2 true 436 1714, .ex2 true 437 1715,
   .ex2 true 438 1716, .ex2 true 439 1717, .cvt 1814 411 410, .cvt 1815 409 408,
   .pack 4237 1815 1814, .cvt 1816 415 414, .cvt 1817 413 412, .pack 4238 1817 1816,
   .cvt 1818 419 418, .cvt 1819 417 416, .pack 4239 1819 1818, .cvt 1820 423 422,
   .cvt 1821 421 420, .pack 4240 1821 1820, .cvt 1822 427 426, .cvt 1823 425 424,
   .pack 4241 1823 1822, .cvt 1824 431 430, .cvt 1825 429 428, .pack 4242 1825 1824,
   .cvt 1826 435 434, .cvt 1827 433 432, .pack 4243 1827 1826, .cvt 1828 439 438,
   .cvt 1829 437 436, .pack 4244 1829 1828, .ex2 true 440 1718, .ex2 true 441 1719,
   .ex2 true 442 1720, .ex2 true 443 1721, .ex2 true 444 1722, .ex2 true 445 1723]

/-- Part A of the first tile's exponentials. -/
def exp0A : List Piece :=
  [.run exp0A_1863]

/-- The first tile's exponential run from `2173`. -/
def exp0B_2173 : List OItem :=
  [.ex2 true 446 1728, .ex2 true 447 1729, .ex2 true 448 1730, .ex2 true 449 1731,
   .ex2 true 450 1732, .ex2 true 451 1733]

/-- The first tile's exponential run from `2221`. -/
def exp0B_2221 : List OItem :=
  [.ex2 true 452 1738, .ex2 true 453 1739, .ex2 true 454 1740, .ex2 true 455 1741,
   .ex2 true 456 1742, .ex2 true 457 1743]

/-- Part B of the first tile's exponentials. -/
def exp0B : List Piece :=
  [.sw m2121,
   .sw m2152,
   .run exp0B_2173,
   .sw m2179,
   .sw m2200,
   .run exp0B_2221,
   .sw m2227,
   .sw m2248]

/-- The first tile's exponential run from `2269`. -/
def exp0C_2269 : List OItem :=
  [.ex2 true 458 1748, .ex2 true 459 1749, .cvt 1847 1039 1036, .cvt 1848 1033 1030,
   .pack 4292 1848 1847, .cvt 1849 1021 1018, .cvt 1850 445 444, .pack 4293 1850 1849,
   .cvt 1851 1027 1024, .cvt 1852 447 446, .pack 4294 1851 1852, .cvt 1853 1045 1042,
   .cvt 1854 457 456, .pack 4295 1854 1853, .cvt 1855 1051 1048, .cvt 1856 459 458,
   .pack 4296 1855 1856, .cvt 1857 443 442, .cvt 1858 441 440, .pack 4297 1858 1857,
   .cvt 1859 451 450, .cvt 1860 449 448, .pack 4298 1860 1859, .cvt 1861 455 454,
   .cvt 1862 453 452, .pack 4299 1862 1861, .ex2 true 460 1750, .ex2 true 461 1751,
   .ex2 true 462 1752, .ex2 true 463 1753, .ex2 true 464 1754, .ex2 true 465 1755]

/-- The first tile's exponential run from `2343`. -/
def exp0C_2343 : List OItem :=
  [.ex2 true 466 1760, .ex2 true 467 1761, .ex2 true 468 1762, .ex2 true 469 1763,
   .ex2 true 470 1764, .ex2 true 471 1765]

/-- The first tile's exponential run from `2391`. -/
def exp0C_2391 : List OItem :=
  [.ex2 true 472 1770, .ex2 true 473 1771, .ex2 true 474 1772, .ex2 true 475 1773,
   .ex2 true 476 1774, .ex2 true 477 1775]

/-- Part C of the first tile's exponentials. -/
def exp0C : List Piece :=
  [.run exp0C_2269,
   .sw m2301,
   .sw m2322,
   .run exp0C_2343,
   .sw m2349,
   .sw m2370,
   .run exp0C_2391,
   .sw m2397,
   .sw m2418]

/-- The first tile's exponential run from `2439`. -/
def exp0D_2439 : List OItem :=
  [.ex2 true 478 1780, .ex2 true 479 1781, .cvt 1875 1075 1072, .cvt 1876 1069 1066,
   .pack 4342 1876 1875, .cvt 1877 1057 1054, .cvt 1878 465 464, .pack 4343 1878 1877,
   .cvt 1879 1063 1060, .cvt 1880 467 466, .pack 4344 1879 1880, .cvt 1881 1081 1078,
   .cvt 1882 477 476, .pack 4345 1882 1881, .cvt 1883 1087 1084, .cvt 1884 479 478,
   .pack 4346 1883 1884, .cvt 1885 463 462, .cvt 1886 461 460, .pack 4347 1886 1885,
   .cvt 1887 471 470, .cvt 1888 469 468, .pack 4348 1888 1887, .cvt 1889 475 474,
   .cvt 1890 473 472, .pack 4349 1890 1889, .ex2 true 480 1782, .ex2 true 481 1783,
   .ex2 true 482 1784, .ex2 true 483 1785, .ex2 true 484 1786, .ex2 true 485 1787,
   .ex2 true 486 1788, .ex2 true 487 1789, .ex2 true 488 1790, .ex2 true 489 1791,
   .ex2 true 490 1792, .ex2 true 491 1793, .ex2 true 492 1794, .ex2 true 493 1795,
   .ex2 true 494 1796, .ex2 true 495 1797, .ex2 true 496 1798, .ex2 true 497 1799,
   .ex2 true 498 1800, .ex2 true 499 1801, .ex2 true 500 1802, .ex2 true 501 1803,
   .ex2 true 502 1804, .ex2 true 503 1805, .ex2 true 504 1806, .ex2 true 505 1807,
   .ex2 true 506 1808, .ex2 true 507 1809, .ex2 true 508 1810, .ex2 true 509 1811,
   .ex2 true 510 1812, .ex2 true 511 1813, .cvt 1891 483 482, .cvt 1892 481 480,
   .pack 4350 1892 1891, .cvt 1893 487 486, .cvt 1894 485 484, .pack 4351 1894 1893,
   .cvt 1895 491 490, .cvt 1896 489 488, .pack 4352 1896 1895, .cvt 1897 495 494,
   .cvt 1898 493 492, .pack 4353 1898 1897, .cvt 1899 499 498, .cvt 1900 497 496,
   .pack 4354 1900 1899, .cvt 1901 503 502, .cvt 1902 501 500, .pack 4355 1902 1901,
   .cvt 1903 507 506, .cvt 1904 505 504, .pack 4356 1904 1903, .cvt 1905 511 510,
   .cvt 1906 509 508, .pack 4357 1906 1905, .unpack 1907 1908 4244, .unpack 1909 1910 4243,
   .unpack 1911 1912 4242, .unpack 1913 1914 4241, .unpack 1915 1916 4240, .unpack 1917 1918 4239,
   .unpack 1919 1920 4238, .unpack 1921 1922 4237]

/-- Part D of the first tile's exponentials. -/
def exp0D : List Piece :=
  [.run exp0D_2439]

/-- The loop tile's exponential run from `2941`. -/
def exp1A_2941 : List OItem :=
  [.mul false 2396 3902 2391, .movImm 2397 0, .sub false 2398 2397 2396, .pack 4489 2398 2398,
   .pack 4490 3902 3902, .fma2 4491 4488 4490 4489, .unpack 2399 2400 4491,
   .fma2 4492 4487 4490 4489, .unpack 2401 2402 4492, .fma2 4493 4486 4490 4489,
   .unpack 2403 2404 4493, .fma2 4494 4485 4490 4489, .unpack 2405 2406 4494,
   .fma2 4495 4005 4490 4489, .unpack 2407 2408 4495, .fma2 4496 4006 4490 4489,
   .unpack 2409 2410 4496, .fma2 4497 4007 4490 4489, .unpack 2411 2412 4497,
   .fma2 4498 4008 4490 4489, .unpack 2413 2414 4498, .fma2 4499 4009 4490 4489,
   .unpack 2415 2416 4499, .fma2 4500 4010 4490 4489, .unpack 2417 2418 4500,
   .fma2 4501 4011 4490 4489, .unpack 2419 2420 4501, .fma2 4502 4012 4490 4489,
   .unpack 2421 2422 4502, .fma2 4503 4013 4490 4489, .unpack 2423 2424 4503,
   .fma2 4504 4014 4490 4489, .unpack 2425 2426 4504, .fma2 4505 4015 4490 4489,
   .unpack 2427 2428 4505, .fma2 4506 4016 4490 4489, .unpack 2429 2430 4506,
   .fma2 4507 4017 4490 4489, .unpack 2431 2432 4507, .fma2 4508 4018 4490 4489,
   .unpack 2433 2434 4508, .fma2 4509 4019 4490 4489, .unpack 2435 2436 4509,
   .fma2 4510 4020 4490 4489, .unpack 2437 2438 4510, .fma2 4511 4021 4490 4489,
   .unpack 2439 2440 4511, .fma2 4512 4022 4490 4489, .unpack 2441 2442 4512,
   .fma2 4513 4023 4490 4489, .unpack 2443 2444 4513, .fma2 4514 4024 4490 4489,
   .unpack 2445 2446 4514, .fma2 4515 4025 4490 4489, .unpack 2447 2448 4515,
   .fma2 4516 4026 4490 4489, .unpack 2449 2450 4516, .fma2 4517 4027 4490 4489,
   .unpack 2451 2452 4517, .fma2 4518 4028 4490 4489, .unpack 2453 2454 4518,
   .fma2 4519 4029 4490 4489, .unpack 2455 2456 4519, .fma2 4520 4030 4490 4489,
   .unpack 2457 2458 4520, .fma2 4521 4031 4490 4489, .unpack 2459 2460 4521,
   .fma2 4522 4032 4490 4489, .unpack 2461 2462 4522, .fma2 4523 4033 4490 4489,
   .unpack 2463 2464 4523, .fma2 4524 4034 4490 4489, .unpack 2465 2466 4524,
   .fma2 4525 4035 4490 4489, .unpack 2467 2468 4525, .fma2 4526 4036 4490 4489,
   .unpack 2469 2470 4526, .fma2 4527 4037 4490 4489, .unpack 2471 2472 4527,
   .fma2 4528 4038 4490 4489, .unpack 2473 2474 4528, .fma2 4529 4039 4490 4489,
   .unpack 2475 2476 4529, .fma2 4530 4040 4490 4489, .unpack 2477 2478 4530,
   .fma2 4531 4041 4490 4489, .unpack 2479 2480 4531, .fma2 4532 4042 4490 4489,
   .unpack 2481 2482 4532, .fma2 4533 4043 4490 4489, .unpack 2483 2484 4533,
   .fma2 4534 4044 4490 4489, .unpack 2485 2486 4534, .fma2 4535 4045 4490 4489,
   .unpack 2487 2488 4535, .fma2 4536 4046 4490 4489, .unpack 2489 2490 4536,
   .fma2 4537 4047 4490 4489, .unpack 2491 2492 4537, .fma2 4538 4048 4490 4489,
   .unpack 2493 2494 4538, .fma2 4539 4049 4490 4489, .unpack 2495 2496 4539,
   .fma2 4540 4050 4490 4489, .unpack 2497 2498 4540, .fma2 4541 4051 4490 4489,
   .unpack 2499 2500 4541, .fma2 4542 4052 4490 4489, .unpack 2501 2502 4542,
   .fma2 4543 4053 4490 4489, .unpack 2503 2504 4543, .fma2 4544 4054 4490 4489,
   .unpack 2505 2506 4544, .fma2 4545 4055 4490 4489, .unpack 2507 2508 4545,
   .fma2 4546 4056 4490 4489, .unpack 2509 2510 4546, .fma2 4547 4057 4490 4489,
   .unpack 2511 2512 4547, .fma2 4548 4058 4490 4489, .unpack 2513 2514 4548,
   .fma2 4549 4059 4490 4489, .unpack 2515 2516 4549, .fma2 4550 4060 4490 4489,
   .unpack 2517 2518 4550, .fma2 4551 4061 4490 4489, .unpack 2519 2520 4551,
   .fma2 4552 4062 4490 4489, .unpack 2521 2522 4552, .fma2 4553 4063 4490 4489,
   .unpack 2523 2524 4553, .fma2 4554 4064 4490 4489, .unpack 2525 2526 4554, .ex2 true 514 2399,
   .ex2 true 515 2400, .ex2 true 516 2401, .ex2 true 517 2402, .ex2 true 518 2403,
   .ex2 true 519 2404, .ex2 true 520 2405, .ex2 true 521 2406, .ex2 true 522 2407,
   .ex2 true 523 2408, .ex2 true 524 2409, .ex2 true 525 2410, .ex2 true 526 2411,
   .ex2 true 527 2412, .ex2 true 528 2413, .ex2 true 529 2414, .ex2 true 530 2415,
   .ex2 true 531 2416, .ex2 true 532 2417, .ex2 true 533 2418, .ex2 true 534 2419,
   .ex2 true 535 2420, .ex2 true 536 2421, .ex2 true 537 2422, .ex2 true 538 2423,
   .ex2 true 539 2424, .ex2 true 540 2425, .ex2 true 541 2426, .ex2 true 542 2427,
   .ex2 true 543 2428, .ex2 true 544 2429, .ex2 true 545 2430, .cvt 2527 517 516,
   .cvt 2528 515 514, .pack 4555 2528 2527, .cvt 2529 521 520, .cvt 2530 519 518,
   .pack 4556 2530 2529, .cvt 2531 525 524, .cvt 2532 523 522, .pack 4557 2532 2531,
   .cvt 2533 529 528, .cvt 2534 527 526, .pack 4558 2534 2533, .cvt 2535 533 532,
   .cvt 2536 531 530, .pack 4559 2536 2535, .cvt 2537 537 536, .cvt 2538 535 534,
   .pack 4560 2538 2537, .cvt 2539 541 540, .cvt 2540 539 538, .pack 4561 2540 2539,
   .cvt 2541 545 544, .cvt 2542 543 542, .pack 4562 2542 2541, .ex2 true 546 2431,
   .ex2 true 547 2432, .ex2 true 548 2433, .ex2 true 549 2434, .ex2 true 550 2435,
   .ex2 true 551 2436]

/-- Part A of the loop tile's exponentials. -/
def exp1A : List Piece :=
  [.run exp1A_2941]

/-- The loop tile's exponential run from `3188`. -/
def exp1B_3188 : List OItem :=
  [.ex2 true 552 2441, .ex2 true 553 2442, .ex2 true 554 2443, .ex2 true 555 2444,
   .ex2 true 556 2445, .ex2 true 557 2446]

/-- The loop tile's exponential run from `3236`. -/
def exp1B_3236 : List OItem :=
  [.ex2 true 558 2451, .ex2 true 559 2452, .ex2 true 560 2453, .ex2 true 561 2454,
   .ex2 true 562 2455, .ex2 true 563 2456]

/-- Part B of the loop tile's exponentials. -/
def exp1B : List Piece :=
  [.sw m3136,
   .sw m3167,
   .run exp1B_3188,
   .sw m3194,
   .sw m3215,
   .run exp1B_3236,
   .sw m3242,
   .sw m3263]

/-- The loop tile's exponential run from `3284`. -/
def exp1C_3284 : List OItem :=
  [.ex2 true 564 2461, .ex2 true 565 2462, .cvt 2560 2002 1999, .cvt 2561 1996 1993,
   .pack 4610 2561 2560, .cvt 2562 1984 1981, .cvt 2563 551 550, .pack 4611 2563 2562,
   .cvt 2564 1990 1987, .cvt 2565 553 552, .pack 4612 2564 2565, .cvt 2566 2008 2005,
   .cvt 2567 563 562, .pack 4613 2567 2566, .cvt 2568 2014 2011, .cvt 2569 565 564,
   .pack 4614 2568 2569, .cvt 2570 549 548, .cvt 2571 547 546, .pack 4615 2571 2570,
   .cvt 2572 557 556, .cvt 2573 555 554, .pack 4616 2573 2572, .cvt 2574 561 560,
   .cvt 2575 559 558, .pack 4617 2575 2574, .ex2 true 566 2463, .ex2 true 567 2464,
   .ex2 true 568 2465, .ex2 true 569 2466, .ex2 true 570 2467, .ex2 true 571 2468]

/-- The loop tile's exponential run from `3358`. -/
def exp1C_3358 : List OItem :=
  [.ex2 true 572 2473, .ex2 true 573 2474, .ex2 true 574 2475, .ex2 true 575 2476,
   .ex2 true 576 2477, .ex2 true 577 2478]

/-- The loop tile's exponential run from `3406`. -/
def exp1C_3406 : List OItem :=
  [.ex2 true 578 2483, .ex2 true 579 2484, .ex2 true 580 2485, .ex2 true 581 2486,
   .ex2 true 582 2487, .ex2 true 583 2488]

/-- Part C of the loop tile's exponentials. -/
def exp1C : List Piece :=
  [.run exp1C_3284,
   .sw m3316,
   .sw m3337,
   .run exp1C_3358,
   .sw m3364,
   .sw m3385,
   .run exp1C_3406,
   .sw m3412,
   .sw m3433]

/-- The loop tile's exponential run from `3454`. -/
def exp1D_3454 : List OItem :=
  [.ex2 true 584 2493, .ex2 true 585 2494, .cvt 2588 2038 2035, .cvt 2589 2032 2029,
   .pack 4660 2589 2588, .cvt 2590 2020 2017, .cvt 2591 571 570, .pack 4661 2591 2590,
   .cvt 2592 2026 2023, .cvt 2593 573 572, .pack 4662 2592 2593, .cvt 2594 2044 2041,
   .cvt 2595 583 582, .pack 4663 2595 2594, .cvt 2596 2050 2047, .cvt 2597 585 584,
   .pack 4664 2596 2597, .cvt 2598 569 568, .cvt 2599 567 566, .pack 4665 2599 2598,
   .cvt 2600 577 576, .cvt 2601 575 574, .pack 4666 2601 2600, .cvt 2602 581 580,
   .cvt 2603 579 578, .pack 4667 2603 2602, .ex2 true 586 2495, .ex2 true 587 2496,
   .ex2 true 588 2497, .ex2 true 589 2498, .ex2 true 590 2499, .ex2 true 591 2500,
   .ex2 true 592 2501, .ex2 true 593 2502, .ex2 true 594 2503, .ex2 true 595 2504,
   .ex2 true 596 2505, .ex2 true 597 2506, .ex2 true 598 2507, .ex2 true 599 2508,
   .ex2 true 600 2509, .ex2 true 601 2510, .ex2 true 602 2511, .ex2 true 603 2512,
   .ex2 true 604 2513, .ex2 true 605 2514, .ex2 true 606 2515, .ex2 true 607 2516,
   .ex2 true 608 2517, .ex2 true 609 2518, .ex2 true 610 2519, .ex2 true 611 2520,
   .ex2 true 612 2521, .ex2 true 613 2522, .ex2 true 614 2523, .ex2 true 615 2524,
   .ex2 true 616 2525, .ex2 true 617 2526, .cvt 2604 589 588, .cvt 2605 587 586,
   .pack 4668 2605 2604, .cvt 2606 593 592, .cvt 2607 591 590, .pack 4669 2607 2606,
   .cvt 2608 597 596, .cvt 2609 595 594, .pack 4670 2609 2608, .cvt 2610 601 600,
   .cvt 2611 599 598, .pack 4671 2611 2610, .cvt 2612 605 604, .cvt 2613 603 602,
   .pack 4672 2613 2612, .cvt 2614 609 608, .cvt 2615 607 606, .pack 4673 2615 2614,
   .cvt 2616 613 612, .cvt 2617 611 610, .pack 4674 2617 2616, .cvt 2618 617 616,
   .cvt 2619 615 614, .pack 4675 2619 2618, .unpack 2620 2621 4562, .unpack 2622 2623 4561,
   .unpack 2624 2625 4560, .unpack 2626 2627 4559, .unpack 2628 2629 4558, .unpack 2630 2631 4557,
   .unpack 2632 2633 4556, .unpack 2634 2635 4555]

/-- Part D of the loop tile's exponentials. -/
def exp1D : List Piece :=
  [.run exp1D_3454]

/-- The unpacks before the first tile's store 1. -/
def pst0a : List OItem :=
  [.unpack 1923 1924 4292, .unpack 1925 1926 4296, .unpack 1927 1928 4295, .unpack 1929 1930 4294,
   .unpack 1931 1932 4293, .unpack 1933 1934 4299, .unpack 1935 1936 4298, .unpack 1937 1938 4297]

/-- The unpacks before the first tile's store 2. -/
def pst0b : List OItem :=
  [.unpack 1939 1940 4342, .unpack 1941 1942 4346, .unpack 1943 1944 4345, .unpack 1945 1946 4344,
   .unpack 1947 1948 4343, .unpack 1949 1950 4349, .unpack 1951 1952 4348, .unpack 1953 1954 4347]

/-- The unpacks before the first tile's store 3. -/
def pst0c : List OItem :=
  [.unpack 1956 1957 4357, .unpack 1958 1959 4356, .unpack 1960 1961 4355, .unpack 1962 1963 4354,
   .unpack 1964 1965 4353, .unpack 1966 1967 4352, .unpack 1968 1969 4351, .unpack 1970 1971 4350]

/-- The first tile's row sum (`add.rn.f32x2` tree, unpack, `add.f32`). -/
def sum0Items : List OItem :=
  [.pack 4358 408 409, .pack 4359 410 411, .pack 4360 412 413, .pack 4361 414 415,
   .pack 4362 416 417, .add2 4363 4358 4362, .pack 4364 418 419, .add2 4365 4359 4364,
   .pack 4366 420 421, .add2 4367 4360 4366, .pack 4368 422 423, .add2 4369 4361 4368,
   .pack 4370 424 425, .add2 4371 4363 4370, .pack 4372 426 427, .add2 4373 4365 4372,
   .pack 4374 428 429, .add2 4375 4367 4374, .pack 4376 430 431, .add2 4377 4369 4376,
   .pack 4378 432 433, .add2 4379 4371 4378, .pack 4380 434 435, .add2 4381 4373 4380,
   .pack 4382 436 437, .add2 4383 4375 4382, .pack 4384 438 439, .add2 4385 4377 4384,
   .pack 4386 440 441, .add2 4387 4379 4386, .pack 4388 442 443, .add2 4389 4381 4388,
   .pack 4390 444 445, .add2 4391 4383 4390, .pack 4392 1018 1021, .add2 4393 4385 4392,
   .pack 4394 1024 1027, .add2 4395 4387 4394, .pack 4396 446 447, .add2 4397 4389 4396,
   .pack 4398 448 449, .add2 4399 4391 4398, .pack 4400 450 451, .add2 4401 4393 4400,
   .pack 4402 1030 1033, .add2 4403 4395 4402, .pack 4404 1036 1039, .add2 4405 4397 4404,
   .pack 4406 452 453, .add2 4407 4399 4406, .pack 4408 454 455, .add2 4409 4401 4408,
   .pack 4410 456 457, .add2 4411 4403 4410, .pack 4412 1042 1045, .add2 4413 4405 4412,
   .pack 4414 1048 1051, .add2 4415 4407 4414, .pack 4416 458 459, .add2 4417 4409 4416,
   .pack 4418 460 461, .add2 4419 4411 4418, .pack 4420 462 463, .add2 4421 4413 4420,
   .pack 4422 464 465, .add2 4423 4415 4422, .pack 4424 1054 1057, .add2 4425 4417 4424,
   .pack 4426 1060 1063, .add2 4427 4419 4426, .pack 4428 466 467, .add2 4429 4421 4428,
   .pack 4430 468 469, .add2 4431 4423 4430, .pack 4432 470 471, .add2 4433 4425 4432,
   .pack 4434 1066 1069, .add2 4435 4427 4434, .pack 4436 1072 1075, .add2 4437 4429 4436,
   .pack 4438 472 473, .add2 4439 4431 4438, .pack 4440 474 475, .add2 4441 4433 4440,
   .pack 4442 476 477, .add2 4443 4435 4442, .pack 4444 1078 1081, .add2 4445 4437 4444,
   .pack 4446 1084 1087, .add2 4447 4439 4446, .pack 4448 478 479, .add2 4449 4441 4448,
   .pack 4450 480 481, .add2 4451 4443 4450, .pack 4452 482 483, .add2 4453 4445 4452,
   .pack 4454 484 485, .add2 4455 4447 4454, .pack 4456 486 487, .add2 4457 4449 4456,
   .pack 4458 488 489, .add2 4459 4451 4458, .pack 4460 490 491, .add2 4461 4453 4460,
   .pack 4462 492 493, .add2 4463 4455 4462, .pack 4464 494 495, .add2 4465 4457 4464,
   .pack 4466 496 497, .add2 4467 4459 4466, .pack 4468 498 499, .add2 4469 4461 4468,
   .pack 4470 500 501, .add2 4471 4463 4470, .pack 4472 502 503, .add2 4473 4465 4472,
   .pack 4474 504 505, .add2 4475 4467 4474, .pack 4476 506 507, .add2 4477 4469 4476,
   .pack 4478 508 509, .add2 4479 4471 4478, .pack 4480 510 511, .add2 4481 4473 4480,
   .add2 4482 4475 4477, .add2 4483 4479 4481, .add2 4484 4482 4483, .unpack 1978 1979 4484,
   .add false 3933 1978 1979]

/-- A loop tile's lazy rescale: the test of the maximum against `-∞`, the gap, its exponential,
the comparison with `-8` and the selections. -/
def max1T : List OItem :=
  [.setp (.unord .ne) false 281 2386 4286578688, .selp 2387 (.reg 2386) (.f32imm 0) 281,
   .sub false 2388 3932 2387, .mul false 2389 3902 2388, .ex2 true 2390 2389,
   .setp (.ord .ge) false 282 2389 3238002688, .selp 512 (.reg 3932) (.reg 2386) 282,
   .selp 2391 (.reg 3932) (.reg 2387) 282, .selp 513 (.f32imm 1065353216) (.reg 2390) 282]

/-- The unpacks before a loop tile's store 1. -/
def pst1a : List OItem :=
  [.unpack 2636 2637 4610, .unpack 2638 2639 4614, .unpack 2640 2641 4613, .unpack 2642 2643 4612,
   .unpack 2644 2645 4611, .unpack 2646 2647 4617, .unpack 2648 2649 4616, .unpack 2650 2651 4615]

/-- The unpacks before a loop tile's store 2. -/
def pst1b : List OItem :=
  [.unpack 2652 2653 4660, .unpack 2654 2655 4664, .unpack 2656 2657 4663, .unpack 2658 2659 4662,
   .unpack 2660 2661 4661, .unpack 2662 2663 4667, .unpack 2664 2665 4666, .unpack 2666 2667 4665]

/-- The unpacks before a loop tile's store 3. -/
def pst1c : List OItem :=
  [.unpack 2669 2670 4675, .unpack 2671 2672 4674, .unpack 2673 2674 4673, .unpack 2675 2676 4672,
   .unpack 2677 2678 4671, .unpack 2679 2680 4670, .unpack 2681 2682 4669, .unpack 2683 2684 4668]

/-- A loop tile's row sum, from `l · α`. -/
def sum1Items : List OItem :=
  [.mul false 2690 3933 513, .movImm 2691 0, .pack 4676 2690 2691, .pack 4677 514 515,
   .add2 4678 4676 4677, .pack 4679 516 517, .pack 4680 518 519, .pack 4681 520 521,
   .pack 4682 522 523, .add2 4683 4678 4682, .pack 4684 524 525, .add2 4685 4679 4684,
   .pack 4686 526 527, .add2 4687 4680 4686, .pack 4688 528 529, .add2 4689 4681 4688,
   .pack 4690 530 531, .add2 4691 4683 4690, .pack 4692 532 533, .add2 4693 4685 4692,
   .pack 4694 534 535, .add2 4695 4687 4694, .pack 4696 536 537, .add2 4697 4689 4696,
   .pack 4698 538 539, .add2 4699 4691 4698, .pack 4700 540 541, .add2 4701 4693 4700,
   .pack 4702 542 543, .add2 4703 4695 4702, .pack 4704 544 545, .add2 4705 4697 4704,
   .pack 4706 546 547, .add2 4707 4699 4706, .pack 4708 548 549, .add2 4709 4701 4708,
   .pack 4710 550 551, .add2 4711 4703 4710, .pack 4712 1981 1984, .add2 4713 4705 4712,
   .pack 4714 1987 1990, .add2 4715 4707 4714, .pack 4716 552 553, .add2 4717 4709 4716,
   .pack 4718 554 555, .add2 4719 4711 4718, .pack 4720 556 557, .add2 4721 4713 4720,
   .pack 4722 1993 1996, .add2 4723 4715 4722, .pack 4724 1999 2002, .add2 4725 4717 4724,
   .pack 4726 558 559, .add2 4727 4719 4726, .pack 4728 560 561, .add2 4729 4721 4728,
   .pack 4730 562 563, .add2 4731 4723 4730, .pack 4732 2005 2008, .add2 4733 4725 4732,
   .pack 4734 2011 2014, .add2 4735 4727 4734, .pack 4736 564 565, .add2 4737 4729 4736,
   .pack 4738 566 567, .add2 4739 4731 4738, .pack 4740 568 569, .add2 4741 4733 4740,
   .pack 4742 570 571, .add2 4743 4735 4742, .pack 4744 2017 2020, .add2 4745 4737 4744,
   .pack 4746 2023 2026, .add2 4747 4739 4746, .pack 4748 572 573, .add2 4749 4741 4748,
   .pack 4750 574 575, .add2 4751 4743 4750, .pack 4752 576 577, .add2 4753 4745 4752,
   .pack 4754 2029 2032, .add2 4755 4747 4754, .pack 4756 2035 2038, .add2 4757 4749 4756,
   .pack 4758 578 579, .add2 4759 4751 4758, .pack 4760 580 581, .add2 4761 4753 4760,
   .pack 4762 582 583, .add2 4763 4755 4762, .pack 4764 2041 2044, .add2 4765 4757 4764,
   .pack 4766 2047 2050, .add2 4767 4759 4766, .pack 4768 584 585, .add2 4769 4761 4768,
   .pack 4770 586 587, .add2 4771 4763 4770, .pack 4772 588 589, .add2 4773 4765 4772,
   .pack 4774 590 591, .add2 4775 4767 4774, .pack 4776 592 593, .add2 4777 4769 4776,
   .pack 4778 594 595, .add2 4779 4771 4778, .pack 4780 596 597, .add2 4781 4773 4780,
   .pack 4782 598 599, .add2 4783 4775 4782, .pack 4784 600 601, .add2 4785 4777 4784,
   .pack 4786 602 603, .add2 4787 4779 4786, .pack 4788 604 605, .add2 4789 4781 4788,
   .pack 4790 606 607, .add2 4791 4783 4790, .pack 4792 608 609, .add2 4793 4785 4792,
   .pack 4794 610 611, .add2 4795 4787 4794, .pack 4796 612 613, .add2 4797 4789 4796,
   .pack 4798 614 615, .add2 4799 4791 4798, .pack 4800 616 617, .add2 4801 4793 4800,
   .add2 4802 4795 4797, .add2 4803 4799 4801, .add2 4804 4802 4803, .unpack 2692 2693 4804,
   .add false 3933 2692 2693]

/-- The first tile's exponentials, from the named barrier to the first probability store. -/
def exp0Pieces : List Piece := exp0A ++ (exp0B ++ (exp0C ++ exp0D))

/-- A loop tile's exponentials, from the named barrier to the first probability store. -/
def exp1Pieces : List Piece := exp1A ++ (exp1B ++ (exp1C ++ exp1D))

/-- The first tile's maximum's test against `-∞` (`setp.neu.f32`, `selp.f32`). -/
def max0T : List OItem :=
  [.setp (.unord .ne) false 275 3932 4286578688, .selp 1682 (.reg 3932) (.f32imm 0) 275]

/-- The update of the reference maximum at the end of a loop trip. -/
def movM : List OItem := [.mov 3932 512]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
