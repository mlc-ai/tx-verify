-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKReload
import Lemmas.Flow.SignedBits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

def primingKPredicatePc (pair : Fin 16) : Nat :=
  kCopyPc pair - (if pair.val = 8 then 7 else 6)

def primingKFirstHalfPair (j : Fin 7) : Fin 16 := ⟨j.val + 1, by omega⟩

private def primingPredicate (dest off : Nat) : IntInstr :=
  { op := .setp .gt none, ty := .int .s 32, dsts := [some dest],
    srcs := [.reg 1852, .imm off] }

private theorem signedSetpGtFromReads {l : Launch} {g dst : Nat} {t : TState} {a b : Opnd}
    {x y : BitVec 64} (hA : readBits l g t 32 a = .ok x) (hB : readBits l g t 32 b = .ok y) :
    execInt l g t
      { op := .setp .gt none, ty := .int .s 32, dsts := [some dst], srcs := [a, b] } =
      .ok (next (setReg t dst (.pred (compare .gt .s 32 x y)))) := by
  change (do
    let u ← readBits l g t 32 a
    let v ← readBits l g t 32 b
    pure (next (setReg t dst (.pred (compare .gt .s 32 u v))))) = _
  rewrite [hA, hB]
  rfl

private theorem primingPredicateSegment {K : Kernel} {l : Launch} {g start dest off word : Nat}
    {value : Bool} (hCode : K.code[start]? = some ⟨none, .int (primingPredicate dest off)⟩)
    (hWord : word < 2 ^ 32) (hOff : off < 2 ^ 32)
    (hCmp : compare .gt .s 32 (BitVec.ofNat 64 word) (BitVec.ofNat 64 off) = value) :
    Seg K [] l g 1 start [(1852, b32 word)] (start + 1) [(dest, .pred value)] := by
  intro t ht
  let u := next (setReg t dest (.pred value))
  have hRead := readBits_b32 (L := l) (g := g) ht.2.2.2.2.1 hWord
  have hImmediate := readBits_imm (L := l) (g := g) (t := t) hOff
  have hExec : execLocalA [] l g t (.int (primingPredicate dest off)) = .ok u := by
    rewrite [execLocalA_nil, execLocal_int rfl]
    exact (signedSetpGtFromReads (dst := dest) hRead hImmediate).trans
      (congrArg (fun b => Except.ok (next (setReg t dest (.pred b)))) hCmp)
  have hNext : At u (start + 1) [(dest, .pred value)] :=
    (ht.mono (show Holds t.regs [] from trivial)).set (by simp)
  exact ⟨u, run_local hCode rfl ht hExec, hNext⟩

private theorem signedPredicateOfInts {x y : BitVec 64} {a b : Int}
    (hx : toSigned 32 x = a) (hy : toSigned 32 y = b) :
    compare .gt .s 32 x y = decide (b < a) := by
  change decide (toSigned 32 y < toSigned 32 x) = _
  rewrite [hx, hy]
  rfl

private theorem remainingLengthCmp (len row off : Nat) :
    decide ((off : Int) < (len : Int) - (row : Int)) = decide (row + off < len) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem residualPredicate {off len row : Nat} (hLen : len < 2 ^ 31)
    (hRow : row < 2 ^ 31) (hOff : off < 2 ^ 31) :
    compare .gt .s 32 (BitVec.ofNat 64 ((len + 2 ^ 32 - row) % 2 ^ 32))
      (BitVec.ofNat 64 off) = decide (row + off < len) := by
  have hSignedResidual : toSigned 32 (BitVec.ofNat 64 ((len + 2 ^ 32 - row) % 2 ^ 32)) =
      (len : Int) - row := by
    rw [toSigned_eq_toInt32]
    unfold CeilDiv.toInt32 FastDivmod.W
    simp only [Nat.mod_mod]
    split <;> omega
  have hOff32 : off < 2 ^ 32 := by omega
  have hOff64 : off < 2 ^ 64 := by omega
  have hSignedOff : toSigned 32 (BitVec.ofNat 64 off) = (off : Int) := by
    simp only [toSigned, toNat_ofNat_lt hOff64, Nat.mod_eq_of_lt hOff32, ite_eq_left hOff]
  exact (signedPredicateOfInts hSignedResidual hSignedOff).trans (remainingLengthCmp len row off)

/-- Pair zero uses a different decoded setup. The other fifteen share a copy template. -/
def primingKLaterPair (j : Fin 15) : Fin 16 := ⟨j.val + 1, by omega⟩

def primingKBroadcastReg (j : Fin 15) : Nat :=
  1857 + 2 * j.val + if j.val < 7 then 0 else 2

def primingKBroadcastSlot (j : Fin 15) : Nat := (j.val + 1) % 8

def primingKPointerReg (j : Fin 15) : Nat := if j.val < 7 then 1853 else 1871

/-- The copy frame carries the two words of the pointer for this half and the
destination, column and remaining-length values shared by all pairs. -/
def primingKLaterFrame (p : Params) (l : Launch) (batch tile warp : Nat)
    (bases : Nat → Nat) (j : Fin 15) (lane : Nat) : List (Nat × Value) :=
  [(7547, b64 (2 * kvCopyColumn (32 * warp + lane) false)),
   (primingKPointerReg j, b32 (bases lane % 2 ^ 32)),
   (primingKPointerReg j + 1, b32 (bases lane / 2 ^ 32))] ++
    primingKSourceFrame p l batch tile warp lane

/-- Each later pair compares the same signed request residual with its actual row offset. -/
theorem primingKLaterMaskForAll {l : Launch} {g len tile tid : Nat}
    (hLen : len < 2 ^ 31) (hRow : kvCopyRow tile tid 0 < 2 ^ 31) (j : Fin 15) :
    let pair := primingKLaterPair j
    let start := primingKPredicatePc pair
    Seg kernel [] l g 1 start [(1852, b32 ((len + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32))]
      (start + 1) [(124 + pair.val, .pred (decide (kvCopyRow tile tid pair < len)))] := by
  dsimp only
  let pair := primingKLaterPair j
  have hShape : kvCopyRow tile tid 0 + 8 * pair.val = kvCopyRow tile tid pair := by
    simp [kvCopyRow]
  have hCode : kernel.code[primingKPredicatePc pair]? =
      some ⟨none, .int (primingPredicate (124 + pair.val) (8 * pair.val))⟩ := by
    fin_cases j <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hOff : 8 * pair.val < 2 ^ 31 := by have := pair.isLt; omega
  have hWord : (len + 2 ^ 32 - kvCopyRow tile tid 0) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  simpa only [hShape] using primingPredicateSegment (l := l) (g := g) hCode hWord
    (by omega : 8 * pair.val < 2 ^ 32) (residualPredicate hLen hRow hOff)

def primingKPairPredicate (p : Params) (batch tile warp : Nat) (j : Fin 15)
    (lane : Nat) : Nat × Value :=
  let pair := primingKLaterPair j
  (124 + pair.val, .pred (decide (kvCopyRow tile (32 * warp + lane) pair < p.kLength batch)))

theorem primingKLaterShuffleCode (j : Fin 15) (word : Fin 2) :
    kernel.code[kCopyPc (primingKLaterPair j) - 5 + word.val]? = some ⟨none, .warp {
      kind := .shfl .idx, ty := some (.int .b 32),
      dsts := [some (primingKBroadcastReg j + word.val)],
      srcs := [.reg (primingKPointerReg j + word.val), .imm (primingKBroadcastSlot j), .imm 6175],
      mask := some (.imm (-1)) }⟩ := by
  fin_cases j <;> fin_cases word <;> (set_option maxRecDepth 100000 in kernel_rfl)

theorem primingKLaterAddress (l : Launch) (g : Nat) {base tid : Nat}
    (hBase : base < 2 ^ 64) (j : Fin 15) (live : Bool) :
    let pair := primingKLaterPair j
    Seg kernel [] l g 3 (kCopyPc pair - 3)
      [(primingKBroadcastReg j, b32 (base % 2 ^ 32)),
       (primingKBroadcastReg j + 1, b32 (base / 2 ^ 32)),
       (7547, b64 (2 * kvCopyColumn tid false)), (124 + pair.val, .pred live)]
      (kCopyPc pair)
      [(kCopySrcReg pair, b64 ((base + 2 * kvCopyColumn tid false) % 2 ^ 64)),
       (kCopyByteReg pair, b32 (if live then 16 else 0))] := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  have hJoin : (base % 4294967296 ||| base / 4294967296 * 4294967296 %
      18446744073709551616) = base := by
    rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
    change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
    rw [← Nat.two_pow_add_eq_or_of_lt hLo]
    omega
  dsimp only
  fin_cases j <;> cases live <;> intro t ht <;> seg_fp ht using norm_bits [hJoin]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch tile warp shuffles votes : Nat}
    (hg : g < l.threads) (hLen : p.kLength batch < 2 ^ 31) (hTile : 128 * tile + 7 < 2 ^ 31)
    (bases : Nat → Nat) (hBases : ∀ lane < 32, bases lane < 2 ^ 64 ∧ bases lane % 16 = 0)
include hp hX hg hLen hTile bases hBases

end

/-- Decode the second-slot mask while keeping the first half's live packet operands. -/
theorem primingKSecondPointerDecode {p : Params} {l : Launch}
    {g batch tile warp lane : Nat}
    (hLen : p.kLength batch < 2^31) (hTile : 128*tile+7 < 2^31)
    (bases : Nat → Nat) {t : TState}
    (ht : At t 608 (primingKPacketFrame p l batch tile warp bases lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 609 ((132,.pred (decide (kvCopyRow tile (32*warp+lane) 8 < p.kLength batch))) ::
        primingKPacketFrame p l batch tile warp bases lane) := by
  let tid := 32 * warp + lane
  let row := kvCopyRow tile tid 0
  let F := primingKPacketFrame p l batch tile warp bases lane
  have hRow : row < 2 ^ 31 := by dsimp [row, kvCopyRow]; omega
  have hWord : (p.kLength batch + 2 ^ 32 - row) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hc : kernel.code[608]? = some ⟨none, .int (primingPredicate 132 64)⟩ := Flow.code_608
  obtain ⟨u, hu, hU⟩ := primingPredicateSegment (l := l) (g := g) hc hWord
    (by decide) (residualPredicate hLen hRow (by decide)) t
    (ht.mono ⟨holds_lookup ht.2.2.2.2 rfl, trivial⟩)
  obtain ⟨huA, keep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) (by simp) hu
  have hFrame := Epilogue.holdsSchedulerFrame ht.2.2.2.2 keep
    (fun _ hm => List.mem_map_of_mem hm)
  have hMask : row + 64 = kvCopyRow tile tid 8 := by simp [row, kvCopyRow]
  exact ⟨u, run_rtg huA, hU.mono ⟨by simpa only [hMask] using hU.2.2.2.2.1, hFrame⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
