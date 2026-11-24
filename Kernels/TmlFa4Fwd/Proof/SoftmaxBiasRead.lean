-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
public import Kernels.TmlFa4Fwd.Flow.Code.Part054
public import Kernels.TmlFa4Fwd.Flow.Code.Part055
public import Kernels.TmlFa4Fwd.Flow.Code.Part081
public import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Lemmas.Flow.CommitTarget

import Lemmas.Step.ReadSource
import Lemmas.Step.DrainInOrder
import Lemmas.Kernel.ProgressDescent
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

structure BiasReadSite where
  base : Nat
  offset : Nat
  firstReg : Nat

/-- The 16 vector loads in each biased round. A vector contains eight BF16 bias elements. -/
def biasReadSite (repeated : Bool) (i : Fin 16) : BiasReadSite :=
  if repeated then (#v[
    ⟨4170, 0, 4171⟩, ⟨4034, 0, 4175⟩, ⟨4030, 0, 4179⟩, ⟨4026, 0, 4183⟩,
    ⟨4022, 0, 4187⟩, ⟨4018, 0, 4191⟩, ⟨4014, 0, 4195⟩, ⟨4010, 0, 4199⟩,
    ⟨4170, 16384, 4203⟩, ⟨4006, 0, 4207⟩, ⟨4002, 0, 4211⟩, ⟨3998, 0, 4215⟩,
    ⟨3994, 0, 4219⟩, ⟨3990, 0, 4223⟩, ⟨3986, 0, 4227⟩, ⟨3982, 0, 4231⟩] : Vector BiasReadSite 16)[i]
  else (#v[
    ⟨2784, 0, 3011⟩, ⟨2846, 0, 3015⟩, ⟨2842, 0, 3019⟩, ⟨2838, 0, 3023⟩,
    ⟨2834, 0, 3027⟩, ⟨2830, 0, 3031⟩, ⟨2826, 0, 3035⟩, ⟨2822, 0, 3039⟩,
    ⟨2784, 16384, 3043⟩, ⟨2818, 0, 3047⟩, ⟨2814, 0, 3051⟩, ⟨2810, 0, 3055⟩,
    ⟨2806, 0, 3059⟩, ⟨2802, 0, 3063⟩, ⟨2798, 0, 3067⟩, ⟨2794, 0, 3071⟩] : Vector BiasReadSite 16)[i]

def biasReadPc (repeated : Bool) (i : Fin 16) : Nat :=
  (if repeated then 5189 else 3501) + 5 * i.val

def biasReadRegs (repeated : Bool) (i : Fin 16) : List Nat :=
  let d := (biasReadSite repeated i).firstReg
  [d, d + 1, d + 2, d + 3]

private def biasReadOp (repeated : Bool) (i : Fin 16) : Op :=
  let site := biasReadSite repeated i
  .mem {
    kind := .load
    space := some (.shared .cta)
    sem := .weak
    elem := .int .b 32
    vec := 4
    addr := ⟨.reg site.base 32, site.offset⟩
    dsts := (biasReadRegs repeated i).map some }

private theorem biasReadCode (repeated : Bool) (i : Fin 16) :
    kernel.code[biasReadPc repeated i]? = some ⟨none, biasReadOp repeated i⟩ := by
  cases repeated <;> fin_cases i
  · exact Flow.code_3501
  · exact Flow.code_3506
  · exact Flow.code_3511
  · exact Flow.code_3516
  · exact Flow.code_3521
  · exact Flow.code_3526
  · exact Flow.code_3531
  · exact Flow.code_3536
  · exact Flow.code_3541
  · exact Flow.code_3546
  · exact Flow.code_3551
  · exact Flow.code_3556
  · exact Flow.code_3561
  · exact Flow.code_3566
  · exact Flow.code_3571
  · exact Flow.code_3576
  · exact Flow.code_5189
  · exact Flow.code_5194
  · exact Flow.code_5199
  · exact Flow.code_5204
  · exact Flow.code_5209
  · exact Flow.code_5214
  · exact Flow.code_5219
  · exact Flow.code_5224
  · exact Flow.code_5229
  · exact Flow.code_5234
  · exact Flow.code_5239
  · exact Flow.code_5244
  · exact Flow.code_5249
  · exact Flow.code_5254
  · exact Flow.code_5259
  · exact Flow.code_5264

def biasReadAcc (l : Launch) (g base : Nat) (repeated : Bool) (i : Fin 16) (word : Nat) :
    Acc :=
  ⟨⟨.shared, g / l.block, base + (biasReadSite repeated i).offset + 4 * word⟩, 4,
    false, false, .cta, word, false⟩

private theorem biasEffAddr {l : Launch} {g : Nat} {t : TState} {r base off : Nat}
    (hr : t.regs r = some (b32 base)) (hSum : base + off < 2 ^ 32) :
    effAddr l g t .shared r off = .ok ⟨.shared, g / l.block, base + off⟩ := by
  have hBase : base < 2 ^ 32 := by omega
  simp only [effAddr, sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind,
    pure, Except.pure, truncBits_ofNat hBase (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
    truncBits_ofNat hSum (by decide), BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show base + off < 2 ^ 64 by omega)]

/-- The fired read accesses one four-byte element of its computed vector address. -/
theorem biasReadAccessAtRegister {l : Launch} {g base : Nat} {t : TState}
    (repeated : Bool) (i : Fin 16)
    (hPc : t.pc = biasReadPc repeated i)
    (hReg : t.regs (biasReadSite repeated i).base = some (b32 base))
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0)
    {a : Acc} {bytes : List (Option Byte)} {o : Option TState}
    (he : EStep kernel Assumptions.all l g t ⟨biasReadPc repeated i, .rd a bytes⟩ o) :
    a = biasReadAcc l g base repeated i t.sub := by
  obtain ⟨tmpl, hOut, hFire⟩ := he
  rw [hPc] at hFire
  rcases out_ev hOut with ⟨_, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rw [hPc, biasReadCode] at hc
  obtain rfl := Option.some.inj hc
  have hTmpl : eventTmpl Assumptions.all l g t (biasReadOp repeated i) =
      loadTmpl Assumptions.all l g t .shared false 32 (biasReadRegs repeated i)
        (biasReadSite repeated i).base (biasReadSite repeated i).offset := by
    cases repeated <;> fin_cases i <;> rfl
  rw [hTmpl] at hFire
  have hEff := biasEffAddr (l := l) (g := g) hReg hAddr
  have hLen : (biasReadRegs repeated i).length = 4 := rfl
  simp only [loadTmpl, hEff, bind, Except.bind, elemAcc, hLen, Nat.reduceDiv, hAlign, pure,
    Except.pure, Bool.false_eq_true, ite_false, Fires] at hFire
  obtain ⟨_, _, eq, _⟩ := hFire
  exact (Kind.rd.inj (congrArg Event.kind eq)).1

/-- The decoded Bias vector instruction requests its current four-byte element. -/
theorem biasReadTemplate {l : Launch} {g base : Nat} {t : TState}
    (repeated : Bool) (i : Fin 16) (hpc : t.pc = biasReadPc repeated i)
    (hf : t.fault = none)
    (hr : t.regs (biasReadSite repeated i).base = some (b32 base))
    (hAddr : base + (biasReadSite repeated i).offset < 2^32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0) :
    out kernel Assumptions.all l g t = .ev
      (.read (biasReadAcc l g base repeated i t.sub) (afterLoad t (biasReadRegs repeated i))) := by
  let a := biasReadAcc l g base repeated i t.sub
  let ds := biasReadRegs repeated i
  have hCode := biasReadCode repeated i
  rw [← hpc] at hCode
  have hLen : ds.length = 4 := rfl
  have hEff := biasEffAddr (l := l) (g := g) hr hAddr
  change out kernel Assumptions.all l g t = .ev (.read a (afterLoad t ds))
  rw [out_event hf hCode rfl (by cases repeated <;> fin_cases i <;> rfl)]
  have hTmpl : eventTmpl Assumptions.all l g t (biasReadOp repeated i) =
      loadTmpl Assumptions.all l g t .shared false 32 ds
        (biasReadSite repeated i).base (biasReadSite repeated i).offset := by
    cases repeated <;> fin_cases i <;> rfl
  rw [hTmpl]
  simp [loadTmpl, hEff, elemAcc, hLen, hAlign, bind, Except.bind, pure, Except.pure,
    Loc.at, a, biasReadAcc]

section
variable {l : Launch} {X : Execution} (repeated : Bool) (i : Fin 16) {g j base : Nat} {t : TState}
    {ending : Option TState} (hpc : t.pc = biasReadPc repeated i) (hf : t.fault = none)
    (hr : t.regs (biasReadSite repeated i).base = some (b32 base))
    (hAddr : base + (biasReadSite repeated i).offset < 2 ^ 32)
    (hAlign : (base + (biasReadSite repeated i).offset) % 16 = 0)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
include repeated i hpc hf hr hAddr hAlign hRun

/-- An element of the bias vector is observed as a separate four-byte read at its exact
lane address. The returned bytes feed the actual vector-load continuation. -/
theorem biasReadElementStepInPrefix (hMore : (X.tr g).drop j ≠ []) :
    ∃ bs, X.get (g, j) = some ⟨biasReadPc repeated i,
      .rd (biasReadAcc l g base repeated i t.sub) bs⟩ ∧
      Run kernel Assumptions.all l g (afterLoad t (biasReadRegs repeated i) bs)
        ((X.tr g).drop (j + 1)) ending ∧
      EStep kernel Assumptions.all l g t
        ⟨biasReadPc repeated i,.rd (biasReadAcc l g base repeated i t.sub) bs⟩
        (some (afterLoad t (biasReadRegs repeated i) bs)) := by
  let a := biasReadAcc l g base repeated i t.sub
  let ds := biasReadRegs repeated i
  have ho := biasReadTemplate (l := l) (g := g) repeated i hpc hf hr hAddr hAlign
  have hn : Next kernel Assumptions.all l g t t (.read a (afterLoad t ds)) := ⟨.refl, ho⟩
  obtain ⟨e,u,he,hFires,hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, _, _, hBad⟩
    cases hBad) hRun hMore
  have hStep : EStep kernel Assumptions.all l g t e (some u) := ⟨_,ho,hFires⟩
  obtain ⟨bs,_,rfl,hU⟩ := hFires
  obtain rfl := Option.some.inj hU
  exact ⟨bs, by simpa only [hpc] using he, hTail, by simpa only [hpc] using hStep⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Softmax
