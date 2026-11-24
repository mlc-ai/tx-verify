-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStage
public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats

@[expose] public section

/-! # The correction warps' shared-memory accesses

A correction thread reads shared memory only at its loads of a statistics word (`ldA st`, `ldL st`:
four bytes of its row's word of stage `st`, `corr_rd`) and writes it only at its staging stores
(`fst`: four bytes of its row's lines of the stage's staging buffer, `corr_wr`). The loads follow
one more sync of the stage's statistics barrier than credits of the stage (`Counts.sync`,
`Counts.credit`); the writes of an item follow one more successful poll of the stage's free
barrier than staged arrivals of the stage (`Counts.oFree`, `Counts.staged`), and the stage's
proxy fence follows them before its staged arrival. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A staging write lies in its row's line of half `j / 4` of its stage. -/
theorem fst_inLine {g : Nat} (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) {a : Acc}
    (hl : a.loc = ⟨.shared, ctaOf L g, Correction.stage L g st.val (2 * (j.val % 4) + h.val) +
        16384 * (j.val / 4) + 4 * el.val⟩) (hs : a.size = 4) :
    InLine L (ctaOf L g) st.val (j.val / 4) (rowOf L g) a := by
  have hx : Correction.lnOf L g % 8 ^^^ (2 * (j.val % 4) + h.val) < 2 ^ 3 :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by omega)
  have hk : Correction.kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hrow : rowOf L g = 32 * Correction.kOf L g + Correction.lnOf L g := by
    simp only [rowOf, Correction.kOf, Correction.lnOf, Correction.tidOf]; omega
  simp only [InLine, lineBase, hl, hs, hrow]
  unfold Correction.stage
  simp only [Correction.sb]
  refine ⟨trivial, trivial, by omega, by omega⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A correction thread's read** is its load of its row's statistics word of a stage, after
one more sync of the stage's statistics barrier than credits of the stage. -/
theorem corr_rd {g i pc : Nat} {a : Acc} {bs : List (Option Byte)} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, i) = some ⟨pc, .rd a bs⟩) :
    ∃ (d : Correction.D) (st : Fin 2),
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      (d.site = .ldA st ∨ d.site = .ldL st) ∧ CorrLoad L X g i a false st.val := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hc, hi, -, hcode, hf, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  have hkw := corr_kOf hw hw'
  have hT := corr_trips_pos hpre
  have hsize : (∃ st : Fin 2, d.site = .ldA st ∨ d.site = .ldL st) → a.size = 4 := by
    rintro ⟨st, hs | hs⟩ <;> rw [hs] at hcode hf <;> fin_cases st
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_1)
      exact fires_ld_size hf rfl
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_2)
      exact fires_ld_size hf rfl
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_3)
      exact fires_ld_size hf rfl
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_4)
      exact fires_ld_size hf rfl
  have hcl : ∀ st : Nat, st < 2 →
      (arrivals (statsBar L (ctaOf L g) st) ((X.tr g).take i) + 1 =
        barOrd X g i (warpOf L g - 5 + 4 * st) ↔
      (Correction.trips L + 1) * d.i + Correction.creditPos L st d + 1 =
        (Correction.trips L + 1) * d.i + Correction.syncPos L st d) := by
    intro st hst
    rw [corr_barOrd hpre hX ht hw hw' i (by omega),
      show warpOf L g - 5 + 4 * st = Correction.kOf L g + 3 + 4 * st by omega, hc.sync st hst,
      show statsBar L (ctaOf L g) st = Correction.ownLoc L g (240 + 8 * st) by
        simp only [statsBar, Correction.ownLoc, Correction.sb], hc.credit st hst]
  have hbo : ∀ st : Nat, st < 2 → barOrd X g i (warpOf L g - 5 + 4 * st) =
      (kvTiles L + 1) * d.i + Correction.syncPos L st d := by
    intro st hst
    rw [corr_barOrd hpre hX ht hw hw' i (by omega),
      show warpOf L g - 5 + 4 * st = Correction.kOf L g + 3 + 4 * st by omega, hc.sync st hst]
    rfl
  have hloc : ∀ st : Nat, Correction.ownLoc L g (332 + 512 * st + 4 * Correction.rowOf L g) =
      statsWord L (ctaOf L g) st (rowOf L g) := fun st => by
    simp only [Correction.ownLoc, statsWord, Correction.sb, Correction.rowOf, rowOf,
      Correction.tidOf]
  obtain ⟨site, i', tt, aw, aa, o⟩ := d
  cases site
  case ldA st =>
    obtain ⟨ac, bs', hk1, hl⟩ := hk
    injection hk1 with h1 h2
    subst h1 h2
    have htr : tt + 1 < Correction.trips L := hi.trip rfl
    refine ⟨_, st, hσ, hc, hi, .inl rfl, rfl, by rw [hl, hloc], hsize ⟨st, .inl rfl⟩,
      (hcl st.val st.isLt).mpr ?_, i', tt, by unfold kvTiles; exact Nat.lt_of_succ_lt htr, ?_⟩
    · fin_cases st <;> simp [Correction.creditPos, Correction.syncPos] <;> omega
    · rw [hbo st.val st.isLt]
      fin_cases st <;> simp [Correction.syncPos] <;> omega
  case ldL st =>
    obtain ⟨ac, bs', hk1, hl⟩ := hk
    injection hk1 with h1 h2
    subst h1 h2
    refine ⟨_, st, hσ, hc, hi, .inr rfl, rfl, by rw [hl, hloc], hsize ⟨st, .inr rfl⟩,
      (hcl st.val st.isLt).mpr ?_, i', Correction.trips L - 1, ?_, ?_⟩
    · fin_cases st <;> simp [Correction.creditPos, Correction.syncPos] <;> omega
    · unfold kvTiles; exact Nat.sub_lt hT Nat.one_pos
    · rw [hbo st.val st.isLt]
      have hk : kvTiles L = Correction.trips L := rfl
      fin_cases st <;> simp [Correction.syncPos, hk] <;> omega
  all_goals exfalso
  all_goals simp at hk

/-- **A correction thread's write** is a staging store: element `el` of store `h` of final chunk
`j` of stage `st` writes the word `fw d (4 h + el)` at its swizzled address. -/
theorem corr_wr {g i pc : Nat} {a : Acc} {bs : List Byte} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) :
    ∃ (d : Correction.D) (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4),
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      d.site = .fst st j h el ∧
      a.loc = ⟨.shared, ctaOf L g, Correction.stage L g st.val (2 * (j.val % 4) + h.val) +
        16384 * (j.val / 4) + 4 * el.val⟩ ∧
      a.size = 4 ∧ bs = (Correction.fw d (4 * h.val + el.val)).toBytes := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  obtain ⟨site, i', tt, aw, aa, o⟩ := d
  cases site <;> simp at hk
  case fst st j h el =>
    obtain ⟨h1, h2, h3⟩ := Correction.fst_write hpre rfl hat hcode hf rfl
    exact ⟨_, st, j, h, el, hσ, hc, hi, rfl, h1, h2, h3⟩


/-- **`FloatFacts.corr_rd`**: every `ld.shared` of a correction thread loads its row's statistics
word of a stage. -/
theorem FloatFacts_corr_rd {g i pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (_hg : g < L.threads) (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .rd a bs⟩) : ∃ st < 2, CorrLoad L X g i a false st := by
  obtain ⟨-, st, -, -, -, -, hl⟩ := corr_rd hpre hX ht hw hw' he
  exact ⟨st.val, st.isLt, hl⟩

/-- **`StatsFacts.stats_access`, correction part**: an access of a statistics byte by a correction
thread is its load of its row's statistics word of a stage. -/
theorem Facts.Corr.stats_access {g i : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hacc : X.Access (g, i) a w) (hcov : a.Covers l)
    (hin : InStatsArea L l) :
    (warpOf L g < 8 ∧ SoftStore L X g i a w) ∨
      (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ ∃ st < 2, CorrLoad L X g i a w st) := by
  rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨_, _, pc, he⟩
  rotate_right
  · exact (TmemFacts_no_rmw hX he).elim
  · obtain ⟨-, st, -, -, -, -, hl⟩ := corr_rd hpre hX ht hw hw' he
    exact .inr ⟨hw, hw', st.val, st.isLt, hl⟩
  · exfalso
    obtain ⟨-, st, j, h, el, -, -, -, -, hl, hs, -⟩ := corr_wr hpre hX ht hw hw' he
    have hline := fst_inLine st j h el hl hs
    obtain ⟨-, -, h1, -⟩ := hline
    obtain ⟨-, -, h3, -⟩ := hcov
    obtain ⟨-, -, h5⟩ := hin
    simp only [lineBase] at h1
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
