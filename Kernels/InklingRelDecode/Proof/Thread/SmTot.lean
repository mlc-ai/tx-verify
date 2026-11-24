-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmFin
public import Lemmas.Flow.FmaPairCore
public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # The first half of the score stage on any S words

From the wait for the S tile (pc 1298) to the shuffle of the row maximum (pc 1838) the thread
computes, on the 32 pair registers `%rd499 …` that hold the S words, the scores
(`fma.rn.f32x2` with the bias and `1 / softmax_scale`, unless the block has no bias), the
visibility mask (`selp.f32` with the pattern of `-inf`, unless the block is fully visible) and
the row maximum (`mov.b64 {lo, hi}` unpacks and a tree of `max.f32`). This file defines what the
registers hold for any S words the load returned, as the outcomes of Core's rules
(`fma2E`, `unpackE`, `maxE`), and when none of them faults (`D.s1Ok`).

* `D.scP`: the pair register after the score's `fma` (`D.scE` its outcome).
* `D.scoredT`, `D.maskedT`: the states whose pair registers hold the scores of the first `m`
  pairs, and the masked scores of the first `m` groups. A pair register whose value is not the
  pack of two words is represented by the two four-byte slices of the value (`slW`), whose pack
  is the value (`joinValue` of the slices).
* `D.s1`: the state at the start of the row maximum (pc 1764), by the branches on `%p96` and
  `%p97`; `colW`: the word of a column as the unpack of its pair register gives it.
* `rvSt`: the registers of the tree of maxima on the words, as `maxE` outcomes; `ownV`: its
  root `%r1059`, the thread's maximum.
* `D.finT`: the 64 words of the columns at the shuffle (the machine's `Stg.fsv`).

Where the S words are `f32` numbers these are the numbers of `SmFin` (`SmTotRead`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

/-! ### The abstract instructions of the tree -/

/-- The instruction kinds of the segment: unpack the pair `%rd(499 + q)` into `a`, `b`; the
two- and three-operand maximum into `d`. Registers are decoder ids. -/
inductive RI where
  | unp (a b q : Nat)
  | mx2 (d a b : Nat)
  | mx3 (d a b c : Nat)

/-- The decoder id of `%rK`. -/
abbrev R (k : Nat) : Nat := 461 + k


/-- Unpack `%rd(499 + q)` into `%r a`, `%r b`. -/
abbrev uq (a b q : Nat) : RI := .unp (R a) (R b) q
abbrev m2 (d a b : Nat) : RI := .mx2 (R d) (R a) (R b)
abbrev m3 (d a b c : Nat) : RI := .mx3 (R d) (R a) (R b) (R c)

/-- The 74 instructions of pcs 1764 to 1837, in order. -/
def rmCode : List RI :=
  [ uq 954 955 0, uq 956 957 1, m2 958 956 957, uq 959 960 2, uq 961 962 3, m2 963 961 962,
    uq 964 965 4, m2 966 964 965, uq 967 968 5, m2 969 967 968, uq 970 971 6, uq 972 973 7,
    m2 974 972 973, uq 975 976 8, uq 977 978 9, m2 979 977 978, uq 980 981 10, uq 982 983 11,
    m2 984 982 983, uq 985 986 12, m2 987 985 986, uq 988 989 13, m2 990 988 989,
    uq 991 992 14, uq 993 994 15, m2 995 993 994, uq 996 997 16, m2 998 996 997,
    uq 999 1000 17, m2 1001 999 1000, uq 1002 1003 18, uq 1004 1005 19, m2 1006 1004 1005,
    uq 1007 1008 20, m2 1009 1007 1008, uq 1010 1011 21, m2 1012 1010 1011, uq 1013 1014 22,
    uq 1015 1016 23, m2 1017 1015 1016, uq 1018 1019 24, uq 1020 1021 25, m2 1022 1020 1021,
    uq 1023 1024 26, uq 1025 1026 27, m2 1027 1025 1026, uq 1028 1029 28, m2 1030 1028 1029,
    uq 1031 1032 29, m2 1033 1031 1032, uq 1034 1035 30, uq 1036 1037 31, m2 1038 1036 1037,
    m3 1039 954 955 958, m3 1040 959 960 963, m3 1041 970 971 974, m3 1042 975 976 979,
    m3 1043 980 981 984, m3 1044 991 992 995, m3 1045 1002 1003 1006, m3 1046 1013 1014 1017,
    m3 1047 1018 1019 1022, m3 1048 1023 1024 1027, m3 1049 1034 1035 1038,
    m3 1050 966 969 1041, m3 1051 987 990 1044, m3 1052 998 1001 1045, m3 1053 1009 1012 1046,
    m3 1054 1030 1033 1049, m3 1055 1039 1040 1050, m3 1056 1042 1043 1051,
    m3 1057 1047 1048 1054, m3 1058 1052 1053 1057, m3 1059 1055 1056 1058 ]

theorem rmCode_length : rmCode.length = 74 := by decide +kernel

/-! ### The scores -/

/-- The pair of the `f32` bias numbers of the columns `2 q` and `2 q + 1` (`%rd(358 - q)`). -/
def D.bP (d : D) (q : Nat) : Value :=
  joinValue (.float .f32 (d.bR (2 * q))) (.float .f32 (d.bR (2 * q + 1)))

/-- The pair of `1 / softmax_scale` (`%rd12`). -/
def invP (e : Ent) : Value := joinValue (.float .f32 (1 / e.sc)) (.float .f32 (1 / e.sc))

/-- The pair register of the words `2 q` and `2 q + 1` of a state (`%rd(499 + q)`): their pack. -/
def D.sP (d : D) (q : Nat) : Value := joinValue (d.sv (2 * q)).1 (d.sv (2 * q + 1)).1

/-- The outcome of the score's fused multiply-add of the pair `q`
(`fma.rn.f32x2 %rd(499 + q), %rd(358 - q), %rd12, %rd(499 + q)`). -/
def D.scE (d : D) (q : Nat) : Exec Value := fma2E (d.bP q) (invP d.e) (d.sP q)

/-- The value of the score's pair (the pair of two zero words where the `fma` faults). -/
def D.scP (d : D) (q : Nat) : Value := okVal (.pair (b32 0) (b32 0)) (d.scE q)

/-- The half `k % 2` of a 64-bit value, as `mov.b64 {lo, hi}` splits it. -/
def hW (v : Value) (k : Nat) : Value :=
  if k % 2 = 0 then (splitValue 64 v).1 else (splitValue 64 v).2

theorem scP_pair (d : D) (q : Nat) :
    ∃ a b, d.scP q = .pair a b ∧ a.bytes = 4 ∧ b.bytes = 4 :=
  okVal_pair (fma2E_pair4 _ _ _)

theorem scP_bytes (d : D) (q : Nat) : (d.scP q).bytes = 8 := by
  obtain ⟨a, b, h, ha, hb⟩ := scP_pair d q
  rw [h]
  simp [Value.bytes, ha, hb]

theorem hW_scP_bytes (d : D) (q k : Nat) : (hW (d.scP q) k).bytes = 4 := by
  obtain ⟨a, b, h, ha, hb⟩ := scP_pair d q
  unfold hW
  rw [h]
  split_ifs
  · exact ha
  · exact hb

/-- The slice `k % 2` of a 64-bit value: the pack of the two slices is the value. -/
def slW (v : Value) (k : Nat) : { w : Value // w.bytes = 4 } := ⟨.slice v (4 * (k % 2)) 4, rfl⟩

/-- The words of the state whose first `m` pairs are scored. -/
def scSvT (d : D) (m k : Nat) : { v : Value // v.bytes = 4 } :=
  if k / 2 < m then slW (d.scP (k / 2)) k else d.sv k

/-- The state whose pair registers `q < m` hold the scores. -/
def D.scoredT (d : D) (m : Nat) : D := { d with sv := scSvT d m }

/-! ### The mask -/

/-- `selp.f32 d, a, 0fFF800000, p`: the word where the predicate holds, else `-inf`. -/
def selV (b : Bool) (v : Value) : Value := if b then v else infB

theorem selV_bytes {b : Bool} {v : Value} (h : v.bytes = 4) : (selV b v).bytes = 4 := by
  unfold selV
  split_ifs
  · exact h
  · rfl

/-- The masked word of the column `k`. -/
def mwT (L : Launch) (g : Nat) (d : D) (k : Nat) : Value :=
  selV (visK d.e (g % L.block) d.n k) (hW (d.scP (k / 2)) k)

/-- The words of the state whose first `m` groups are masked (and all pairs scored). -/
def mSvT (L : Launch) (g : Nat) (d : D) (m k : Nat) : { v : Value // v.bytes = 4 } :=
  if msk m (k / 2) then ⟨mwT L g d k, selV_bytes (hW_scP_bytes d _ k)⟩ else scSvT d 32 k

/-- The state whose first `m` groups are masked. -/
def D.maskedT (L : Launch) (g : Nat) (d : D) (m : Nat) : D := { d with sv := mSvT L g d m }

/-- The state at the start of the row maximum (pc 1764): the S words where the block has no bias
(`%p96`), the scores where it is fully visible (`%p97`), else the masked scores. -/
def D.s1 (L : Launch) (g : Nat) (d : D) : D :=
  if pr96 d.e d.n then d else if pr97 d.e d.n then d.scoredT 32 else D.maskedT L g d 32

/-- The word of the column `k` as the unpack of its pair register gives it. -/
def colW (d : D) (k : Nat) : Value := hW (d.sP (k / 2)) k

/-! ### The row maximum -/

/-- The value of register `r` in a register-value list (`b32 0` for none). -/
def lkV (st : List (Nat × Value)) (r : Nat) : Value := (st.lookup r).getD (b32 0)

/-- The effect of an instruction of the tree on the register-value list, over the words `w` of
the columns (written registers in front). -/
def RI.updV (w : Nat → Value) : RI → List (Nat × Value) → List (Nat × Value)
  | .unp a b q, st => (b, w (2 * q + 1)) :: (a, w (2 * q)) :: st
  | .mx2 d a b, st => (d, okVal (b32 0) (maxE [lkV st a, lkV st b])) :: st
  | .mx3 d a b c, st => (d, okVal (b32 0) (maxE [lkV st a, lkV st b, lkV st c])) :: st

/-- The instruction has an outcome: the unpack of the pair `P q`, the maximum of the values. -/
def RI.okV (P : Nat → Value) (st : List (Nat × Value)) : RI → Bool
  | .unp _ _ q => (unpackE 64 (P q)).toBool
  | .mx2 _ a b => (maxE [lkV st a, lkV st b]).toBool
  | .mx3 _ a b c => (maxE [lkV st a, lkV st b, lkV st c]).toBool

/-- The register-value list after the first `c` instructions of the tree. -/
def rvSt (w : Nat → Value) (c : Nat) : List (Nat × Value) :=
  (rmCode.take c).foldl (fun st i => i.updV w st) []

/-- None of the tree's instructions faults, on the pair registers `P` and their words `w`. -/
def RvOk (P w : Nat → Value) : Prop :=
  ∀ c < 74, ∀ i, rmCode[c]? = some i → i.okV P (rvSt w c) = true

/-- The thread's maximum (`%r1059`, the root of the tree) on the words `w`. -/
def ownV (w : Nat → Value) : Value := lkV (rvSt w 74) (R 1059)

/-! ### The words at the shuffle and the condition -/

/-- The 64 words of the columns at the shuffle of the row maximum (the unpacks of the pair
registers of `D.s1`), and the S words above 64. -/
def D.finT (L : Launch) (g : Nat) (d : D) (k : Nat) : { v : Value // v.bytes = 4 } :=
  if k < 64 then
    if h : (colW (D.s1 L g d) k).bytes = 4 then ⟨_, h⟩ else ⟨b32 0, rfl⟩
  else d.sv k

/-- The state after the S tile's wait (`Sm.next` at `waitLd`): the words of the columns at the
shuffle of the row maximum. -/
def D.afterWaitT (L : Launch) (g : Nat) (d : D) : D :=
  { d with site := .shfl5, stg := { d.stg with fsv := D.finT L g d } }

/-- **No instruction of the stage's first half faults**: the scores' `fma` (where the block has
bias), the unpacks and the maxima of the tree. -/
def D.s1Ok (L : Launch) (g : Nat) (d : D) : Prop :=
  (pr96 d.e d.n = false → ∀ q < 32, (d.scE q).toBool = true) ∧
    RvOk (D.s1 L g d).sP (colW (D.s1 L g d))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
