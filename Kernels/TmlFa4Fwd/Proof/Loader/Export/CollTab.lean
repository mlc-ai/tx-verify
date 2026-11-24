-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollCount
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.Time

@[expose] public section

/-! # The loader blocks' collectives, by the sites

Inside a block the collectives before a site (`loc`) and the site's time (`off`) are in one
order. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A block site's time in its slot (the first block's: after the prime region's base). -/
def off (s : Site) : Nat :=
  match s with
  | .pgLd per _ | .pgSt per _ | .rwSt per _ =>
    (match per with | .prime => 8 | _ => 128) + Progress.Ld.pkOff s
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    (match per with | .prime => if v then 264 else 8 | _ => if v then 512 else 128) +
      Progress.Ld.pkOff s
  | .tw t | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then 136 + 16 * t.val + Progress.Ld.gOff s
    else if t.val < 6 then 384 + 16 * (t.val - 4) + Progress.Ld.gOff s
    else Progress.Ld.gOff s
  | _ => 0

/-- The collectives of the block before a site, on warp 14 (`b = false`) or 15. -/
def loc (b : Bool) (s : Site) : Nat :=
  32 * inBlk s + pktSh s + if b then 0 else blkEl s

/-- A TMA site. -/
def isT : Site → Bool
  | .tw _ | .te _ _ | .ta _ | .tc _ _ => true
  | _ => false

/-- The collectives of a block. -/
def size (b : Bool) : Option Blk → Nat
  | some .prime => if b then 64 else 76
  | some .warm => if b then 64 else 70
  | some .tma6 => if b then 0 else 3
  | some .steady => 64
  | none => 0

/-- The order of a block's sites. -/
def ordOk (b : Bool) (s s' : Site) : Bool :=
  !s.wcoll || (b && (isT s || isT s')) || bc s != bc s' || bc s == none ||
    decide (loc b s < loc b s') || decide (off s' < off s) || s == s'

/-- The sites. -/
def blkSites (o : Blk) : List Site :=
  let pks (per : Per) : List Site :=
    (List.finRange 2).flatMap (fun i => [.pgLd per i, .pgSt per i, .rwSt per i]) ++
    [false, true].flatMap fun v =>
      [.slot per v, .commit per v, .arrive per v] ++
      (List.finRange 2).flatMap (fun i => [.ptP per v i, .ptR per v i, .ptS per v i, .lw per v i])
      ++ (List.finRange 16).flatMap fun i =>
        [.xl per v i, .xh per v i, .cp per v i 0, .cp per v i 1]
  let grp (t : Fin 7) : List Site :=
    [.tw t, .ta t, .te t 0, .te t 1, .te t 2, .tc t 0, .tc t 1]
  match o with
  | .prime => pks .prime ++ grp 0 ++ grp 1 ++ grp 2 ++ grp 3
  | .warm => pks .warm ++ grp 4 ++ grp 5
  | .tma6 => grp 6
  | .steady => pks .steady

theorem mem_blkSites {s : Site} {o : Blk} (h : bc s = some o) : s ∈ blkSites o := by
  cases s <;> simp only [bc, reduceCtorEq, Option.some.injEq] at h
  case tw t | ta t =>
    subst h
    revert t; decide
  case te t e => subst h; revert t e; decide
  case tc t c => subst h; revert t c; decide
  case pgLd per i | pgSt per i | rwSt per i => subst h; cases per <;> revert i <;> decide
  case slot per v | commit per v | arrive per v =>
    subst h; cases per <;> cases v <;> simp [blkSites]
  case ptP per v i | ptR per v i | ptS per v i | lw per v i =>
    subst h; cases per <;> cases v <;> simp [blkSites]
  case xl per v i | xh per v i => subst h; cases per <;> cases v <;> simp [blkSites]
  case cp per v i c =>
    subst h
    have : c = 0 ∨ c = 1 := by omega
    rcases this with rfl | rfl <;> cases per <;> cases v <;> simp [blkSites]

/-- The check of a block. -/
def tabChk (b : Bool) (o : Blk) : Bool :=
  ((blkSites o).filter Site.wcoll).all fun s => (b && isT s) ||
    decide (loc b s < size b (some o)) && (blkSites o).all (ordOk b s)

theorem tab_prime : ∀ b : Bool, tabChk b .prime = true := by decide +kernel
theorem tab_warm : ∀ b : Bool, tabChk b .warm = true := by decide +kernel
theorem tab_rest : ∀ b : Bool, tabChk b .steady = true ∧ tabChk b .tma6 = true := by
  decide +kernel

theorem tab (b : Bool) (o : Blk) : tabChk b o = true := by
  cases o
  · exact tab_prime b
  · exact tab_warm b
  · exact (tab_rest b).1
  · exact (tab_rest b).2

/-- **A collective site of a block**: its collectives are within the block's. -/
theorem loc_lt {b : Bool} {s : Site} {o : Blk} (h : bc s = some o) (hw : s.wcoll = true)
    (ht : b = true → isT s = false) : loc b s < size b (some o) := by
  have := List.all_eq_true.mp (tab b o) s (List.mem_filter.mpr ⟨mem_blkSites h, hw⟩)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [ht h1] at h2; cases h2
  · exact h1

/-- **A site of the block with no more collectives before it is earlier, or the same.** -/
theorem off_lt {b : Bool} {s s' : Site} {o : Blk} (h : bc s = some o) (h' : bc s' = some o)
    (hw : s.wcoll = true) (ht : b = true → isT s = false ∧ isT s' = false)
    (hle : loc b s' ≤ loc b s) : off s' < off s ∨ s' = s := by
  have := List.all_eq_true.mp (tab b o) s (List.mem_filter.mpr ⟨mem_blkSites h, hw⟩)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at this
  rcases this with ⟨h1, h2⟩ | ⟨-, h1⟩
  · rw [(ht h1).1] at h2; cases h2
  · have := List.all_eq_true.mp h1 s' (mem_blkSites h')
    simp only [ordOk, hw, h, h', Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      bne_self_eq_false, beq_iff_eq, decide_eq_true_eq, reduceCtorEq, or_false, false_or,
      Bool.false_eq_true, Bool.true_eq_false] at this
    rcases this with ((⟨h2, h3⟩ | h2) | h2) | h2
    · obtain ⟨a1, a2⟩ := ht h2
      rw [a1, a2] at h3
      simp at h3
    · omega
    · exact .inl h2
    · exact .inr h2.symm

/-- The bounds of the block sites' times. -/
private def offChk (s : Site) : Bool :=
  (bc s != some .prime || (decide (8 ≤ off s) && decide (off s < 1000))) &&
  (decide (off s < 1000)) &&
  (bc s != some .tma6 || decide (off s < 128)) && (bc s != some .steady || decide (128 ≤ off s)) &&
  (bc s != some .tma6 || isT s) && (bc s != some .steady || !isT s)

private theorem off_chk : AllSites fun s => offChk s = true := by unfold AllSites; decide +kernel

theorem off_bound (s : Site) : off s < 1000 ∧ (bc s = some .prime → 8 ≤ off s) ∧
    (bc s = some .tma6 → off s < 128 ∧ isT s = true) ∧
    (bc s = some .steady → 128 ≤ off s ∧ isT s = false) := by
  have := off_chk.ok s
  simp only [offChk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_true'] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h2, fun h => (h1.resolve_left (· h)).1,
    fun h => ⟨h3.resolve_left (· h), h5.resolve_left (· h)⟩,
    fun h => ⟨h4.resolve_left (· h), h6.resolve_left (· h)⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
