-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Machine

@[expose] public section

/-! # The output warp's values

What the lanes of warp 13 of CTA `c` compute when every load returns the launch word and every
shuffle and ballot returns what its source lanes hold: the reference values of each scan round,
written in the machine's own arithmetic.

* Round `r` of pass `late` (`r = 0` the first round, `r ≥ 1` a loop round) reads the requests
  `req` (the lane, or the group start `G r` plus 31 plus the lane); a lane past the batch reads
  nothing (`reads`) and holds `0`. The lane's offset `wv`, the next lane's `dnv`, the tile count
  `tlv`, the five partial sums `psum k` of the warp's prefix scan (`psum 5` the inclusive
  prefix)
  and lane 31's prefix `T r` follow; `A r` is the work before the round's group.
* The scan continues past round `r` when `cont r` and ends at the round `R` with `End R`, with
  the last group's first request `gxv R` and the work through it `curv R`.
* The ballot's bit of lane `ℓ` is `predv ℓ`; the chosen request's prefix `pvv` and tile count
  `ntv` are read from the lanes the ballot's population count names.

`Fits L g d ns nv` says that state `d` of lane `g` holds these values at its site, with the
thread's shuffles and full-mask ballots before it (`ns`, `nv`, the thread machine's ghost
counts, three of the shuffles the startup's) at their positions in the warp's common
sequence. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The lane word of lane `ℓ` and the CTA word of CTA `c`. -/
abbrev lw (ℓ : Nat) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 ℓ)
abbrev kw (c : Nat) : BitVec 64 := BitVec.ofNat 64 c

/-- The launch word of the cumulative query offsets at index `i`. -/
def qv (p : Params) (i : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (p.qOffset (r32 i).toNat)

variable (p : Params) (c : Nat) (late : Bool)

/-- The group start a loop round `r ≥ 1` holds (`grp`). -/
def G : Nat → BitVec 64
  | 0 => 0
  | 1 => i32 0
  | r + 2 => min32 (addi (G (r + 1)) 31) (batchOf p late)

/-- The request lane `ℓ` reads in round `r`. -/
def req (r ℓ : Nat) : BitVec 64 :=
  if r = 0 then lw ℓ else add32 (addi (G p late r) 31) (lw ℓ)

/-- Whether lane `ℓ` reads its request in round `r`. -/
def reads (r ℓ : Nat) : Bool := !(scmp .gt .s (req p late r ℓ) (batchOf p late))

/-- Lane `ℓ`'s offset word, the next lane's, and its tile count in round `r`. -/
def wv (r ℓ : Nat) : BitVec 64 := if reads p late r ℓ then qv p (req p late r ℓ) else i32 0

def dnv (r ℓ : Nat) : BitVec 64 := if ℓ < 31 then wv p late r (ℓ + 1) else wv p late r ℓ

def skipv (r ℓ : Nat) : Bool :=
  if r = 0 then !(scmpi .ne .b (lw ℓ) 31 && scmp .lt .s (lw ℓ) (BitVec.ofNat 64 p.batch))
  else scmpi .eq .b (lw ℓ) 31 || scmp .ge .s (req p late r ℓ) (batchOf p late)

def tlv (r ℓ : Nat) : BitVec 64 := sel (skipv p late r ℓ) (i32 0) (tilesOf (dnv p late r ℓ)
  (wv p late r ℓ))

/-- The source lane of the `k`-th `up` shuffle (offset `2 ^ k`, clamp 0). -/
def upSrc (k ℓ : Nat) : Nat := if 2 ^ k ≤ ℓ then ℓ - 2 ^ k else ℓ

/-- One `up` step: the first adds the received count below lane 0's, the others add the received
sum on the lanes above the offset. -/
def upd (k : Nat) (lane prev recv : BitVec 64) : BitVec 64 :=
  if k = 0 then ps1 lane prev recv else psk lane prev recv (2 ^ k - 1)

/-- The partial sum of lane `ℓ` after `k` steps of the scan of round `r`. -/
def psum (r : Nat) : Nat → Nat → BitVec 64
  | 0, ℓ => tlv p late r ℓ
  | k + 1, ℓ => upd k (lw ℓ) (psum r k ℓ) (psum r k (upSrc k ℓ))

/-- Lane 31's prefix: the round's tiles. -/
def T (r : Nat) : BitVec 64 := psum p late r 5 31

/-- The heads word. -/
abbrev H : BitVec 64 := headsW p

/-- The work before loop round `r ≥ 1`'s group (`acc`). -/
def A : Nat → BitVec 64
  | 0 => 0
  | 1 => mul32 (T p late 0) (H p)
  | r + 2 => mad32 (T p late (r + 1)) (H p) (A (r + 1))

/-- The scan goes on from round `r` to round `r + 1`. -/
def cont : Nat → Bool
  | 0 => !(scmp .gt .s (mul32 (T p late 0) (H p)) (kw c)) &&
      !(scmp .ge .s (addi (G p late 1) 31) (batchOf p late))
  | r + 1 => scmp .le .s (mad32 (T p late (r + 1)) (H p) (A p late (r + 1))) (kw c) &&
      !(scmp .ge .s (addi (G p late (r + 2)) 31) (batchOf p late))

/-- Round `r` is reached. -/
def Reached (r : Nat) : Prop := ∀ r' < r, cont p c late r' = true

/-- The scan ends after round `R`. -/
def End (R : Nat) : Prop := Reached p c late R ∧ cont p c late R = false

/-- Whether the last round ended the scan at its total (the group holds the tile) rather than at
the next loop head. -/
def atTotal : Nat → Bool
  | 0 => scmp .gt .s (mul32 (T p late 0) (H p)) (kw c)
  | r + 1 => !(scmp .le .s (mad32 (T p late (r + 1)) (H p) (A p late (r + 1))) (kw c))

/-- The last group's first request when the scan ends after round `R`. -/
def gxv : Nat → BitVec 64
  | 0 => if atTotal p c late 0 then i32 0 else min32 (addi (G p late 1) 31) (batchOf p late)
  | r + 1 => if atTotal p c late (r + 1) then min32 (addi (G p late (r + 1)) 31) (batchOf p late)
      else min32 (addi (G p late (r + 2)) 31) (batchOf p late)

/-- The work through the last group when the scan ends after round `R`. -/
def curv : Nat → BitVec 64
  | 0 => if atTotal p c late 0 then mul32 (T p late 0) (H p) else addi (kw c) 1
  | r + 1 => if atTotal p c late (r + 1) then mad32 (T p late (r + 1)) (H p) (A p late (r + 1))
      else addi (kw c) 1

/-- Lane `ℓ`'s ballot predicate after round `R`. -/
def predv (R ℓ : Nat) : Bool :=
  scmp .le .s (mad32 (psum p late R 5 ℓ) (H p)
    (sub32 (curv p c late R) (mul32 (T p late R) (H p)))) (kw c)

/-- A ballot of the predicates after round `R`, as the machine holds it. -/
def BalOf (R : Nat) (bal : BitVec 64) : Prop :=
  ∃ b : BitVec 32, (∀ ℓ < 32, b.getLsbD ℓ = predv p c late R ℓ) ∧ bal = BitVec.ofNat 64 b.toNat

/-- The chosen request's prefix (times the heads), read from the lane before the ballot's
count. -/
def pvv (R : Nat) (bal : BitVec 64) : BitVec 64 :=
  if scmpi .eq .b bal 0 then i32 0
  else mul32 (psum p late R 5 ((addi (popc bal) (-1)).toNat % 32)) (H p)

/-- The chosen request's tile count, read from the lane the ballot's count names. -/
def ntv (R : Nat) (bal : BitVec 64) : BitVec 64 := tlv p late R ((popc bal).toNat % 32)

/-! ### The states that hold the reference values -/

/-- The shuffles of a selection: the prefix read (when the ballot is not empty) and the tile count
read. -/
def selN (bal : BitVec 64) : Nat := if scmpi .eq .b bal 0 then 1 else 2

/-- The reference state at the first pass's choice of a tile, after its scan ended at round `R`
with ballot `bal`. -/
def chosenD (R : Nat) (bal : BitVec 64) : D :=
  { site := .q0, tot := T p false R, gx := gxv p c false R, cur := curv p c false R, bal := bal,
    pv := pvv p false R bal, nt := ntv p false R bal }

/-- The first pass picked a tile: its scan ended at round `R` with ballot `bal`, the group is a
request of the batch and the chosen request is one. (That the divisions of the tile's coordinates
have a rule follows, `Select.lean`; the warps that share the scan compute different
coordinates.) -/
def Picked (L : Launch) (g R : Nat) (bal : BitVec 64) : Prop :=
  End p (g / L.block) false R ∧ BalOf p (g / L.block) false R bal ∧
    scmp .ge .s (gxv p (g / L.block) false R) (batchOf p false) = false ∧
    scmp .lt .s (chosen (chosenD p (g / L.block) R bal)) (paramW p.batch) = true

/-- The first three conjuncts of `Picked`: the scan ended at round `R` with ballot `bal` at a
group of the batch (that the chosen request is one follows, `Select.lean`, `picked_of_pre`). -/
def PickedPre (L : Launch) (g R : Nat) (bal : BitVec 64) : Prop :=
  End p (g / L.block) false R ∧ BalOf p (g / L.block) false R bal ∧
    scmp .ge .s (gxv p (g / L.block) false R) (batchOf p false) = false

theorem Picked.pre {L : Launch} {g R : Nat} {bal : BitVec 64} (h : Picked p L g R bal) :
    PickedPre p L g R bal := ⟨h.1, h.2.1, h.2.2.1⟩

/-- Pass `late` starts after `n0` shuffles and `v0` ballots: after the startup's three
shuffles, or after the first pass picked a tile. -/
def PassStart (L : Launch) (g : Nat) (late : Bool) (n0 v0 : Nat) : Prop :=
  if late then ∃ R bal, Picked p L g R bal ∧ n0 = 3 + 7 * (R + 1) + selN bal ∧ v0 = 1
  else n0 = 3 ∧ v0 = 0

/-- Round `r` of scan `k` is reached: the first round is round 0 of its pass. -/
def ScanRound (c : Nat) (k : Scan) (r : Nat) : Prop :=
  Reached p c k.late r ∧ (r = 0 ↔ (k = .first ∨ k = .second))

/-- The shuffles of a scan site past its round's first. -/
def scanOff : Site → Nat
  | .up _ j => 1 + j.val
  | .total _ => 6
  | _ => 0

/-- The `up` shuffle `i`'s received value as the state holds it. -/
def uAt (d : D) : Nat → BitVec 64
  | 0 => d.u1
  | 1 => d.u2
  | 2 => d.u4
  | 3 => d.u8
  | _ => d.u16

/-- The state holds round `r`'s tile count and the `up` values received before `up` step `j`. -/
def RoundVals (ℓ r : Nat) (j : Nat) (d : D) : Prop :=
  d.tl = tlv p late r ℓ ∧ ∀ i < j, uAt d i = psum p late r i (upSrc i ℓ)

/-- The scan state of round `r` (its group and work, for a loop round). -/
def LoopVals (r : Nat) (d : D) : Prop := r ≠ 0 → d.grp = G p late r ∧ d.acc = A p late r

/-- The state after the scan of pass `late` ended at round `R`. -/
def EndVals (c R : Nat) (d : D) : Prop :=
  End p c late R ∧ d.tot = T p late R ∧ d.gx = gxv p c late R ∧ d.cur = curv p c late R ∧
    scmp .ge .s (gxv p c late R) (batchOf p late) = false

/-- The state holds the first pass's choice. -/
def ChosenVals (L : Launch) (g R : Nat) (bal : BitVec 64) (d : D) (ns nv : Nat) : Prop :=
  Picked p L g R bal ∧ d.tot = T p false R ∧ d.gx = gxv p (g / L.block) false R ∧
    d.cur = curv p (g / L.block) false R ∧ d.bal = bal ∧ d.pv = pvv p false R bal ∧
    d.nt = ntv p false R bal ∧ ns = 3 + 7 * (R + 1) + selN bal ∧ nv = 1

/-- **The reference values at a state of lane `g`.** -/
def Fits (L : Launch) (g : Nat) (d : D) (ns nv : Nat) : Prop :=
  let ℓ := laneOf L g
  let c := g / L.block
  match d.site with
  | .start => ns = 3 ∧ nv = 0
  | .word k => ∃ r n0 v0, PassStart p L g k.late n0 v0 ∧ ScanRound p c k r ∧ ns = n0 + 7 * r ∧
      nv = v0 ∧ LoopVals p k.late r d ∧ reads p k.late r ℓ = true
  | .down k => ∃ r n0 v0, PassStart p L g k.late n0 v0 ∧ ScanRound p c k r ∧
      ns = n0 + 7 * r ∧ nv = v0 ∧ LoopVals p k.late r d ∧ d.w = wv p k.late r ℓ
  | .up k j => ∃ r n0 v0, PassStart p L g k.late n0 v0 ∧ ScanRound p c k r ∧
      ns = n0 + 7 * r + 1 + j.val ∧ nv = v0 ∧ LoopVals p k.late r d ∧
      RoundVals p k.late ℓ r j.val d
  | .total k => ∃ r n0 v0, PassStart p L g k.late n0 v0 ∧ ScanRound p c k r ∧
      ns = n0 + 7 * r + 6 ∧ nv = v0 ∧ LoopVals p k.late r d ∧ RoundVals p k.late ℓ r 5 d
  | .vote late => ∃ R n0 v0, PassStart p L g late n0 v0 ∧ EndVals p late c R d ∧
      ns = n0 + 7 * (R + 1) ∧ nv = v0 ∧ RoundVals p late ℓ R 5 d
  | .pre late => ∃ R n0 v0, PassStart p L g late n0 v0 ∧ EndVals p late c R d ∧
      ns = n0 + 7 * (R + 1) ∧ nv = v0 + 1 ∧ RoundVals p late ℓ R 5 d ∧
      BalOf p c late R d.bal ∧ scmpi .eq .b d.bal 0 = false
  | .tiles late => ∃ R n0 v0, PassStart p L g late n0 v0 ∧ EndVals p late c R d ∧
      ns = n0 + 7 * (R + 1) + (selN d.bal - 1) ∧ nv = v0 + 1 ∧ RoundVals p late ℓ R 5 d ∧
      BalOf p c late R d.bal ∧ (late = false → d.pv = pvv p false R d.bal)
  | .q0 => ∃ R bal, ChosenVals p L g R bal d ns nv
  | .q1 => ∃ R bal, ChosenVals p L g R bal d ns nv ∧ d.c0 = qv p (chosen d)
  | .exit late => ExitAt L g late ns nv
  | _ => ∃ R bal, ChosenVals p L g R bal d ns nv ∧ d.c0 = qv p (chosen d) ∧
      d.c1 = qv p (addi (chosen d) 1)
where
  /-- The return: of the first pass without a tile, or of the second pass. -/
  ExitAt (L : Launch) (g : Nat) (late : Bool) (ns nv : Nat) : Prop :=
    ∃ n0 v0, PassStart p L g late n0 v0 ∧ ∃ R, End p (g / L.block) late R ∧
      ((scmp .ge .s (gxv p (g / L.block) late R) (batchOf p late) = true ∧
          ns = n0 + 7 * (R + 1) ∧ nv = v0) ∨
        (∃ bal, BalOf p (g / L.block) late R bal ∧
          scmp .ge .s (gxv p (g / L.block) late R) (batchOf p late) = false ∧
          ns = n0 + 7 * (R + 1) + selN bal ∧ nv = v0 + 1 ∧
          (late = false → ¬ Picked p L g R bal)))

/-! ### The scan's end and the pass starts are unique -/

variable {p c late}

theorem Reached.mono {r r' : Nat} (h : Reached p c late r) (hr : r' ≤ r) :
    Reached p c late r' := fun r'' hr'' => h r'' (by omega)

theorem Reached.le_end {r R : Nat} (h : Reached p c late r) (hE : End p c late R) : r ≤ R := by
  by_contra hn
  have := h R (by omega)
  rw [hE.2] at this
  cases this

theorem End.unique {R R' : Nat} (h : End p c late R) (h' : End p c late R') : R = R' :=
  Nat.le_antisymm (h.1.le_end h') (h'.1.le_end h)

theorem BalOf.unique {R : Nat} {b b' : BitVec 64} (h : BalOf p c late R b)
    (h' : BalOf p c late R b') : b = b' := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := h'
  have : x = y := BitVec.eq_of_getLsbD_eq fun i hi => (hx i hi).trans (hy i hi).symm
  rw [this]

theorem Picked.unique {L : Launch} {g R R' : Nat} {b b' : BitVec 64} (h : Picked p L g R b)
    (h' : Picked p L g R' b') : R = R' ∧ b = b' := by
  obtain rfl := h.1.unique h'.1
  exact ⟨rfl, h.2.1.unique h'.2.1⟩

theorem PassStart.unique {L : Launch} {g n0 v0 n0' v0' : Nat}
    (h : PassStart p L g late n0 v0) (h' : PassStart p L g late n0' v0') :
    n0 = n0' ∧ v0 = v0' := by
  cases late
  · simp only [PassStart, Bool.false_eq_true, ↓reduceIte] at h h'
    omega
  · simp only [PassStart, ↓reduceIte] at h h'
    obtain ⟨R, b, hP, rfl, rfl⟩ := h
    obtain ⟨R', b', hP', rfl, rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := hP.unique hP'
    exact ⟨rfl, rfl⟩

theorem selN_pos (b : BitVec 64) : 1 ≤ selN b ∧ selN b ≤ 2 := by
  unfold selN; split <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
