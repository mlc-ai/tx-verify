-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueBarrierRelease
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part055
public import Kernels.TmlFa4Fwd.Flow.Code.Part068
public import Kernels.TmlFa4Fwd.Flow.Code.Part082
public import Kernels.TmlFa4Fwd.Flow.Code.Part088
public import Kernels.TmlFa4Fwd.Flow.Code.Part107
public import Kernels.TmlFa4Fwd.Flow.Code.Part119
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part124
public import Kernels.TmlFa4Fwd.Flow.Code.Part125
public import Kernels.TmlFa4Fwd.Flow.Code.Part128
public import Kernels.TmlFa4Fwd.Flow.Code.Part132
public import Kernels.TmlFa4Fwd.Flow.Code.Part136
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The only four count forms of the frozen CTA barriers. -/
def namedBarrierCount (pc : Nat) : Option Nat :=
  if pc = 173 then none else if [3583, 5271].contains pc then some 128
  else if [1910, 2764, 3103, 7741, 7747, 9204].contains pc then some 416 else some 64

def namedBarrierMode (pc : Nat) : BarMode :=
  if [4397, 5683, 6891, 7616, 7741, 9204].contains pc then .arrive else .sync

def namedBarrierSites : List Nat :=
  [173, 1910, 2764, 3103, 3583, 4397, 5271, 5683, 6891, 7616, 7741, 7747, 7985, 7988,
    8006, 8225, 8465, 8761, 9204]

private theorem barrierTable : OpPcsFast kernel.code barOp namedBarrierSites = true := by
  decide +kernel

private theorem barrierIssueTmpl {l : Launch} {A : List Assumption} {g pc : Nat}
    {t : TState} {ins : Instr} (hp : pc ∈ namedBarrierSites) (hc : kernel.code[pc]? = some ins) :
    ∃ src, eventTmpl A l g t ins.op = barTmpl l g t src
      ((namedBarrierCount pc).map (.imm ∘ Int.ofNat)) (namedBarrierMode pc) ∧
      (pc = 173 → src = .imm 0) ∧ (namedBarrierCount pc = some 416 → src = .imm 2) := by
  simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | rw [Flow.code_173] at hc
    | rw [Flow.code_1910] at hc
    | rw [Flow.code_2764] at hc
    | rw [Flow.code_3103] at hc
    | rw [Flow.code_3583] at hc
    | rw [Flow.code_4397] at hc
    | rw [Flow.code_5271] at hc
    | rw [Flow.code_5683] at hc
    | rw [Flow.code_6891] at hc
    | rw [Flow.code_7616] at hc
    | rw [Flow.code_7741] at hc
    | rw [Flow.code_7747] at hc
    | rw [Flow.code_7985] at hc
    | rw [Flow.code_7988] at hc
    | rw [Flow.code_8006] at hc
    | rw [Flow.code_8225] at hc
    | rw [Flow.code_8465] at hc
    | rw [Flow.code_8761] at hc
    | rw [Flow.code_9204] at hc
  all_goals obtain rfl := Option.some.inj hc
  all_goals first
    | refine ⟨.imm 0, rfl, ?_, ?_⟩
    | refine ⟨.imm 2, rfl, ?_, ?_⟩
    | refine ⟨_, rfl, ?_, ?_⟩
  all_goals simp [namedBarrierCount]

private theorem firesBarrierCount {l : Launch} {g pc id : Nat} {t : TState}
    {src : Opnd} {count observed : Option Nat} {mode tag : BarMode} {o : Option TState}
    (hBlock : l.block = 512)
    (hc : count = none ∨ count = some 64 ∨ count = some 128 ∨ count = some 416)
    (hs : Fires pc (barTmpl l g t src (count.map (.imm ∘ Int.ofNat)) mode)
      ⟨pc, .bar id observed tag⟩ o) :
    id < 16 ∧ observed = count ∧ tag = mode ∧ readBits l g t 32 src = .ok (BitVec.ofNat 64 id)
    := by
  cases hId : readBits l g t 32 src with
  | error f =>
    rw [show barTmpl l g t src (count.map (.imm ∘ Int.ofNat)) mode = .ub f by
      simp only [barTmpl, hId]] at hs
    cases hs.1
  | ok n =>
    by_cases hN : 16 ≤ n.toNat
    · rw [show barTmpl l g t src (count.map (.imm ∘ Int.ofNat)) mode = .ub .badBarrier by
        simp only [barTmpl, hId, ite_eq_left hN]] at hs
      cases hs.1
    · have hTmpl : barTmpl l g t src (count.map (.imm ∘ Int.ofNat)) mode =
          .bar n.toNat (next t) count mode := by
        rcases hc with rfl | rfl | rfl | rfl
        all_goals simp only [barTmpl, hId, ite_eq_right hN]
        · rfl
        all_goals
          change (if _ then Tmpl.bar n.toNat (next t)
            (if _ then none else some _) mode else Tmpl.ub .badBarrier) = _
          simp [hBlock, truncBits]
      rw [hTmpl] at hs
      have he := hs.1
      simp only [Event.mk.injEq, Kind.bar.injEq] at he
      obtain ⟨-, rfl, rfl, rfl⟩ := he
      exact ⟨by omega, rfl, rfl, by simp⟩

/-- Every real named barrier event carries its encoded mode and count. The only
full-CTA form is the common prologue, and every 416-lane event is barrier 2. -/
theorem actualNamedBarrier {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel A m X)
    {i : EvId} {pc id : Nat} {count : Option Nat} {mode : BarMode}
    (h : X.get i = some ⟨pc, .bar id count mode⟩) :
    pc ∈ namedBarrierSites ∧ count = namedBarrierCount pc ∧ mode = namedBarrierMode pc ∧ id < 16 ∧
      (count = none ↔ pc = 173) ∧ (pc = 173 → id = 0) ∧ (count = some 416 → id = 2) := by
  rcases get_source hX h with ⟨_, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  have hP := OpPcsFast.mem barrierTable hc (fires_bar_op hf rfl)
  obtain ⟨src, hSrc, hZero, hTwo⟩ := barrierIssueTmpl (A := A) (l := l) (g := i.1)
    (t := t) hP hc
  have hCount : namedBarrierCount pc = none ∨ namedBarrierCount pc = some 64 ∨
      namedBarrierCount pc = some 128 ∨ namedBarrierCount pc = some 416 := by
    unfold namedBarrierCount
    split <;> (try split) <;> (try split) <;> simp
  rw [hSrc] at hf
  obtain ⟨hId, hC, hM, hWord⟩ := firesBarrierCount hp.block hCount hf
  refine ⟨hP, hC, hM, hId, ?_, ?_, ?_⟩
  · rw [hC]
    unfold namedBarrierCount
    split <;> (try split) <;> (try split) <;> simp_all
  · intro hpc
    rw [hZero hpc] at hWord
    have h : (0 : BitVec 64) = BitVec.ofNat 64 id := Except.ok.inj hWord
    have := congrArg BitVec.toNat h
    simpa [toNat_ofNat_lt (show id < 2 ^ 64 by omega)] using this.symm
  · intro hcnt
    rw [hTwo (hC.symm.trans hcnt)] at hWord
    have h : BitVec.ofNat 64 2 = BitVec.ofNat 64 id := Except.ok.inj hWord
    have := congrArg BitVec.toNat h
    simpa [toNat_ofNat_lt (show id < 2 ^ 64 by omega)] using this.symm

end
end PTX.Kernels.TmlFa4Fwd
