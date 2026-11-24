-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part022

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

def signedCompareOp (cmp : Cmp) (dst src bound : Nat) : Op :=
  .int ⟨.setp cmp none, .int .s 32, false, [some dst], [.reg src, .imm (bound : Int)]⟩

private theorem signedCompareLocal {l : Launch} {g dst src bound value : Nat} {s : TState}
    (cmp : Cmp) (hCmp : cmp = .lt ∨ cmp = .gt) (hWord : s.regs src = some (b32 value))
    (hValue : value < 2^31) (hBound : bound < 2^31) :
    execLocalA [] l g s (signedCompareOp cmp dst src bound) =
      .ok (next (setReg s dst (.pred (compare cmp .s 32 (BitVec.ofNat 64 value)
        (BitVec.ofNat 64 bound))))) := by
  have hImm : truncBits 32 (BitVec.ofInt 64 (bound : Int)) = BitVec.ofNat 64 bound := by
    rw [BitVec.ofInt_natCast, truncBits_ofNat (show bound < 2^32 by omega) (by decide)]
  unfold signedCompareOp
  have hRule : (⟨.setp cmp none, .int .s 32, false, [some dst],
      [.reg src, .imm (bound : Int)]⟩ : IntInstr).rule = some .threadInt := by
    rcases hCmp with rfl | rfl <;> rfl
  rw [execLocalA_nil, execLocal_int hRule]
  have hBits := readBits_b32 (L := l) (g := g) hWord (show value < 2^32 by omega)
  have hRight : readBits l g s 32 (.imm (bound : Int)) = .ok (BitVec.ofNat 64 bound) :=
    congrArg Except.ok hImm
  change (do
    let x ← readBits l g s 32 (.reg src)
    let y ← readBits l g s 32 (.imm (bound : Int))
    pure (next (setReg s dst (.pred (compare cmp .s 32 x y))))) = _
  rw [hBits, hRight]
  rfl

private def residualSelectOp (dst src pred : Nat) : Op :=
  .int ⟨.selp, .int .b 32, false, [some dst], [.imm 0, .reg src, .reg pred]⟩

private theorem residualSelectCore {l : Launch} {g pc dst src pred value : Nat}
    (hCode : kernel.code[pc]? = some ⟨none, residualSelectOp dst src pred⟩)
    : Seg kernel [] l g 1 pc [(pred,.pred false),(src,b32 value)]
      (pc+1) [(dst,b32 value)] := by
  intro s hs
  let u := next (setReg s dst (b32 value))
  refine ⟨u, run_local hCode rfl hs ?_, ?_⟩
  · have hp : s.regs pred = some (.pred false) := hs.2.2.2.2.1
    have hv : s.regs src = some (b32 value) := hs.2.2.2.2.2.1
    unfold residualSelectOp
    have hRule : (⟨.selp, .int .b 32, false, [some dst],
        [.imm 0, .reg src, .reg pred]⟩ : IntInstr).rule = some .threadMove := rfl
    rw [execLocalA_nil, execLocal_selp hRule]
    simp [execMove, readReg, hp, readValue, hv, b32, u,
      bind, Except.bind, pure, Except.pure, DType.width, Value.bytes]
  · exact ((hs.mono (G := []) trivial).set (r := dst) (v := b32 value)
      (by simp)).mono ⟨Function.update_self .., trivial⟩

private theorem liveResidualCore {l : Launch} {g pc tileReg valueReg pred dst tile value : Nat}
    (hCmp : kernel.code[pc]? = some ⟨none, signedCompareOp .lt pred tileReg 0⟩)
    (hSelect : kernel.code[pc+1]? = some ⟨none, residualSelectOp dst valueReg pred⟩)
    (hTile : tile < 2^31) (hRegs : pred ≠ valueReg) :
    Seg kernel [] l g 2 pc [(tileReg,b32 tile),(valueReg,b32 value)]
      (pc+2) [(dst,b32 value)] := by
  have hc : Seg kernel [] l g 1 pc [(tileReg,b32 tile),(valueReg,b32 value)]
      (pc+1) [(pred,.pred false),(valueReg,b32 value)] := by
    intro s hs
    let u := next (setReg s pred (.pred false))
    refine ⟨u, run_local hCmp rfl hs ?_, ?_⟩
    · rw [signedCompareLocal .lt (.inl rfl) hs.2.2.2.2.1 hTile (by decide)]
      have hNonneg : ¬ (tile : Int) < 0 := by omega
      simp [compare, signedWord hTile, signedWord (by decide : 0 < 2^31), u, hNonneg]
    · exact (hs.mono (G := [(valueReg,b32 value)]) ⟨hs.2.2.2.2.2.1,trivial⟩).set
        (by simpa using hRegs.symm)
  exact hc.comp (residualSelectCore hSelect)

/-- Both K copy paths start their mask-row calculation with the same lane quotient. -/
theorem keyCopyLaneOffsetCore {l : Launch} {g tid : Nat} (hTid : tid < 512)
    (steady : Bool) :
    let pc := if steady then 1386 else 981
    let r := if steady then 1146 else 1979
    Seg kernel [] l g 2 pc [(1061, b32 tid)] (pc + 2) [(r, b32 (tid/8%8))] := by
  have hTid32 : tid < 4294967296 := by omega
  have hTid64 : tid < 18446744073709551616 := by omega
  have hDiv32 : tid/8 < 4294967296 := by omega
  have hDiv64 : tid/8 < 18446744073709551616 := by omega
  have hRow : tid/8 &&& 7 = tid/8%8 := Nat.and_two_pow_sub_one_eq_mod _ 3
  have hRow32 : tid/8%8 < 4294967296 := by omega
  have hRow64 : tid/8%8 < 18446744073709551616 := by omega
  cases steady <;> dsimp only <;> intro s hs <;>
    seg_fp hs using nf_simp [Nat.mod_eq_of_lt hTid32, Nat.mod_eq_of_lt hTid64,
      Nat.mod_eq_of_lt hDiv32, Nat.mod_eq_of_lt hDiv64, hRow,
      Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64]

/-- Warm copy masks use the number of rows after this lane's first row in the tile. -/
theorem warmKeyCopyResidualCore {l : Launch} {g high round lane len : Nat}
    (hRound : round ≤ high) (hHigh : high < 2^31) (hLane : lane < 8)
    (hLive : 128*(high-round)+lane < len) (hLen : len < 2^31) :
    Seg kernel [] l g 6 996
      [(1116, b32 high), (7174, b32 round), (1979, b32 lane), (1086, b32 len)]
      1002 [(1997, b32 (len-(128*(high-round)+lane)))] := by
  let tile := high-round
  let base := 128*tile
  let row := base+lane
  let residual := len-row
  have hTile31 : tile < 2^31 := by omega
  have hDiff32 : tile < 4294967296 := by omega
  have hDiff64 : tile < 18446744073709551616 := by omega
  have hBase32 : base < 4294967296 := by omega
  have hBase64 : base < 18446744073709551616 := by omega
  have hLane32 : lane < 4294967296 := by omega
  have hLane64 : lane < 18446744073709551616 := by omega
  have hRow32 : row < 4294967296 := by omega
  have hRow64 : row < 18446744073709551616 := by omega
  have hLen32 : len < 4294967296 := by omega
  have hLen64 : len < 18446744073709551616 := by omega
  have hResidual32 : residual < 4294967296 := by omega
  have hResidual64 : residual < 18446744073709551616 := by omega
  have hHigh32 : high < 4294967296 := by omega
  have hHigh64 : high < 18446744073709551616 := by omega
  have hRound32 : round < 4294967296 := by omega
  have hRound64 : round < 18446744073709551616 := by omega
  have hOr : lane ||| base = row := by
    rw [Nat.or_comm, lor_eq_add (k := 7) (by omega) (by omega)]
  have hDiff : (18446744073709551616-round+high)%4294967296 = tile := by
    have h := show 18446744073709551616-round+high = 18446744073709551616+tile by omega
    rw [h]
    rw [Nat.add_mod, show (18446744073709551616:Nat)%4294967296 = 0 by decide,
      Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hDiff32
  have hRemaining : (18446744073709551616-row+len)%4294967296 = residual := by
    have h := show 18446744073709551616-row+len = 18446744073709551616+residual by omega
    rw [h]
    rw [Nat.add_mod, show (18446744073709551616:Nat)%4294967296 = 0 by decide,
      Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hResidual32
  have hBaseNat : (tile*128)%4294967296 = base := by
    rw [Nat.mul_comm, show 128*tile = base from rfl, Nat.mod_eq_of_lt hBase32]
  have hStart : Seg kernel [] l g 4 996
      [(1116, b32 high), (7174, b32 round), (1979, b32 lane), (1086, b32 len)]
      1000 [(1993, b32 tile), (1996, b32 residual)] := by
    intro s hs
    seg_fp hs using nf_simp [Nat.mod_eq_of_lt hHigh32, Nat.mod_eq_of_lt hHigh64,
      Nat.mod_eq_of_lt hRound32, Nat.mod_eq_of_lt hRound64,
      Nat.mod_eq_of_lt hDiff32, Nat.mod_eq_of_lt hDiff64,
      Nat.mod_eq_of_lt hBase32, Nat.mod_eq_of_lt hBase64,
      Nat.mod_eq_of_lt hLane32, Nat.mod_eq_of_lt hLane64,
      Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64,
      Nat.mod_eq_of_lt hLen32, Nat.mod_eq_of_lt hLen64,
      Nat.mod_eq_of_lt hResidual32, Nat.mod_eq_of_lt hResidual64, hDiff, hBaseNat, hOr,
      hRemaining]
  have hEnd : Seg kernel [] l g 2 1000 [(1993, b32 tile), (1996, b32 residual)]
      1002 [(1997, b32 residual)] :=
    liveResidualCore Flow.code_1000 Flow.code_1001 hTile31 (by decide)
  exact hStart.comp hEnd

/-- The steady tile offset is computed before its two scratch iterations. -/
theorem steadyKeyCopyTileCore {l : Launch} {g high round : Nat}
    (hRound : round ≤ high) (hHigh : 128*high < 2^31) :
    Seg kernel [] l g 2 1396 [(1116,b32 high),(7181,b32 round)]
      1398 [(1144,b32 (high-round)),(1145,b32 (128*(high-round)))] := by
  have hHigh32 : high < 4294967296 := by omega
  have hHigh64 : high < 18446744073709551616 := by omega
  have hRound32 : round < 4294967296 := by omega
  have hRound64 : round < 18446744073709551616 := by omega
  have hDiff32 : high-round < 4294967296 := by omega
  have hDiff64 : high-round < 18446744073709551616 := by omega
  have hBase32 : 128*(high-round) < 4294967296 := by omega
  have hBase64 : 128*(high-round) < 18446744073709551616 := by omega
  have hDiff : (18446744073709551616-round+high)%4294967296 = high-round := by
    have h := show 18446744073709551616-round+high = 18446744073709551616+(high-round)
      by omega
    rw [h, Nat.add_mod, show (18446744073709551616:Nat)%4294967296 = 0 by decide,
      Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hDiff32
  intro s hs
  seg_fp hs using nf_simp [Nat.mod_eq_of_lt hHigh32, Nat.mod_eq_of_lt hHigh64,
    Nat.mod_eq_of_lt hRound32, Nat.mod_eq_of_lt hRound64,
    Nat.mod_eq_of_lt hDiff32, Nat.mod_eq_of_lt hDiff64, hDiff,
    Nat.mod_eq_of_lt hBase32, Nat.mod_eq_of_lt hBase64, Nat.mul_comm (high-round) 128]

/-- The steady mask subtracts its lane's effective row from the selected used-K length. -/
theorem steadyKeyCopyResidualCore {l : Launch} {g tile lane len : Nat}
    (hLive : 128*tile+lane < len) (hLen : len < 2^31) :
    Seg kernel [] l g 4 1464
      [(1144,b32 tile),(1145,b32 (128*tile)),(1146,b32 lane),(1086,b32 len)]
      1468 [(2155,b32 (len-(128*tile+lane)))] := by
  let base := 128*tile
  let row := base+lane
  let value := len-row
  have hTile : tile < 2^31 := by omega
  have hBase32 : base < 4294967296 := by omega
  have hBase64 : base < 18446744073709551616 := by omega
  have hLane32 : lane < 4294967296 := by omega
  have hLane64 : lane < 18446744073709551616 := by omega
  have hLen32 : len < 4294967296 := by omega
  have hLen64 : len < 18446744073709551616 := by omega
  have hRow32 : row < 4294967296 := by omega
  have hRow64 : row < 18446744073709551616 := by omega
  have hValue32 : value < 4294967296 := by omega
  have hValue64 : value < 18446744073709551616 := by omega
  have hRemaining : (18446744073709551616-row+len)%4294967296 = value := by
    have h := show 18446744073709551616-row+len = 18446744073709551616+value by omega
    rw [h, Nat.add_mod, show (18446744073709551616:Nat)%4294967296 = 0 by decide,
      Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hValue32
  have hPrep : Seg kernel [] l g 2 1464
      [(1144,b32 tile),(1145,b32 base),(1146,b32 lane),(1086,b32 len)]
      1466 [(1144,b32 tile),(2154,b32 value)] := by
    intro s hs
    have hRowEq : lane+base = row := Nat.add_comm _ _
    seg_fp hs using nf_simp [Nat.mod_eq_of_lt hBase32, Nat.mod_eq_of_lt hBase64,
      Nat.mod_eq_of_lt hLane32, Nat.mod_eq_of_lt hLane64, Nat.mod_eq_of_lt hLen32,
      Nat.mod_eq_of_lt hLen64, Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64,
      Nat.mod_eq_of_lt hValue32, Nat.mod_eq_of_lt hValue64, hRowEq, hRemaining]
  exact hPrep.comp (liveResidualCore Flow.code_1466 Flow.code_1467 hTile (by decide))

/-- Every row in a noninitial K tile has a complete source vector. -/
theorem recurringKeyResidualLive {trips len round lane : Nat} (pair : Fin 16)
    (hTrips : 2 ≤ trips) (hBound : trips ≤ (len+127)/128) (hLane : lane < 8) :
    8*pair.val < len-(128*(trips-2-round)+lane) := by
  have hPair := pair.isLt
  omega

/-- A signed comparison with the row offset evaluates true when the row is live. -/
theorem liveKeyCompareCore {l : Launch} {g pc pred src bound value : Nat}
    (hCode : kernel.code[pc]? = some ⟨none, signedCompareOp .gt pred src bound⟩)
    (hLive : bound < value) (hValue : value < 2^31) :
    Seg kernel [] l g 1 pc [(src,b32 value)] (pc+1) [(pred,.pred true)] := by
  intro s hs
  let u := next (setReg s pred (.pred true))
  refine ⟨u, run_local hCode rfl hs ?_, ?_⟩
  · have hBound := hLive.trans hValue
    rw [signedCompareLocal .gt (.inr rfl) hs.2.2.2.2.1 hValue hBound]
    have hInt : (bound : Int) < (value : Int) := by omega
    simp [compare, signedWord hValue, signedWord hBound, u, hInt]
  · exact ((hs.mono (G := []) trivial).set (r := pred) (v := .pred true)
      (by simp)).mono ⟨Function.update_self .., trivial⟩

/-- The actual full-vector selector writes sixteen source bytes for a live row. -/
theorem liveKeySelectCore {l : Launch} {g pc dst pred : Nat}
    (hCode : kernel.code[pc]? = some ⟨none,
      .int ⟨.selp,.int .b 32,false,[some dst],[.imm 16,.imm 0,.reg pred]⟩⟩) :
    Seg kernel [] l g 1 pc [(pred,.pred true)] (pc+1) [(dst,b32 16)] := by
  intro s hs
  let u := next (setReg s dst (b32 16))
  refine ⟨u, run_local hCode rfl hs ?_, ?_⟩
  · have hp : s.regs pred = some (.pred true) := hs.2.2.2.2.1
    have hRule : (⟨.selp,.int .b 32,false,[some dst],
        [.imm 16,.imm 0,.reg pred]⟩ : IntInstr).rule = some .threadMove := rfl
    rw [execLocalA_nil, execLocal_selp hRule]
    simp [execMove, readReg, hp, u, b32, readValue, readBits, bind, Except.bind, pure,
      Except.pure, DType.width, Value.bytes, show truncBits 32 (16#64) = 16#64 from rfl]
  · exact ((hs.mono (G := []) trivial).set (r := dst) (v := b32 16)
      (by simp)).mono ⟨Function.update_self .., trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
