-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsBaseCausality
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Lemmas.Order.ReadLast
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # Every statistics load returns a single-precision float

Every `ld.shared` of a correction thread `h` loads its row's statistics word of a stage `st`
(`FloatFacts.corr_rd`), after its `bar.sync` number `G` on the row's statistics barrier (`CorrLoad`,
`G + 1` syncs before the load). That `bar.sync` passed, so the partner softmax thread `g` of the row
made its event number `G` on the barrier (`SoftArrives`), and before it its store of the word of
generation `G` (`FloatFacts.soft_arrive_store`), the bytes of a canonical single-precision word
(`FloatFacts.soft_store_f32`, `F32Word`). That store happens before the load
(`Stats.stats_baseCausality`), and it is the load's last write of each byte (`read_of_last_write`):
every write of a statistics byte is a softmax store of the word (`StatsFacts.stats_access`; no
asynchronous access reaches the statistics words, `hasync`), so a store of `g`
(`Stats.soft_unique`); an earlier one precedes the store in program order, a later one of the same
generation is the store itself (`FloatFacts.soft_store_one`), and one of a later generation happens
after the load (`Stats.stats_war`). So the load returns those bytes, which rebuild to that word
(`stats_floats`, `F32Read`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Floats
open Stats

variable {P : Params} {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption}
  {mem0 : Mem0}

/-- A thread's count of events on barrier `id` grows along its trace. -/
theorem barOrd_mono {g i i' id : Nat} (h : i ≤ i') : barOrd X g i id ≤ barOrd X g i' id :=
  (List.take_sublist_take_left (l := X.tr g) h).countP_le

/-- A byte of a statistics word is in the statistics area. -/
theorem statsWord_area {c st ρ k : Nat} (hst : st < 2) (hρ : ρ < 128) (hk : k < 4) :
    InStatsArea L ((statsWord L c st ρ).at k) := by
  simp only [InStatsArea, statsWord, Loc.at]
  refine ⟨by trivial, ?_, ?_⟩ <;> omega

/-- **Every `ld.shared` of a correction thread returns the bytes of a canonical single-precision
word**, given that the loads of the row's softmax thread before its store, which happens before
the read, returned single-precision floats (`hsl`). -/
theorem stats_floats (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (hf : FloatFacts L X) (htm : TmemFacts L X) (hU : StatsCredit L X)
    (hsoft : SoftArrives L X)
    (hasync : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStatsArea L l → False)
    {h j pc : Nat} {a : Acc} {bs : List (Option Byte)} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (he : X.get (h, j) = some ⟨pc, .rd a bs⟩)
    (hsl : ∀ {g i : Nat}, g < L.threads → warpOf L g < 8 → ctaOf L g = ctaOf L h →
      i < (X.tr g).length → baseCausality L X (g, i) (h, j) → ∀ k < i, ∀ pc a' (vals' : List Value),
        X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    ∃ x, F32Read bs x := by
  have hblk := hpre.block
  obtain ⟨st, hst, hcl⟩ := hf.corr_rd hh h8 h12 he
  obtain ⟨-, hla, hsa, harr, J, t, htn, hJ⟩ := hcl
  have hk : warpOf L h - 8 < 4 := by omega
  have hid : warpOf L h - 5 + 4 * st = statsId st (warpOf L h - 8) := by unfold statsId; omega
  rw [hid] at harr hJ
  -- the correction's `bar.sync` number `G`
  obtain ⟨y, pcy, cnty, my, hyj, hyget, hyo⟩ := exists_bar (X := X) (g := h) (x := j)
    (id := statsId st (warpOf L h - 8))
    (c := barOrd X h j (statsId st (warpOf L h - 8)) - 1) (by omega)
  obtain ⟨hcy, st', k', hst', hk', -, hw'⟩ := stats_of_bar ht hh hyget (by unfold statsId; omega)
  have hmy : my = .sync := by
    rcases hw' with ⟨h1, -⟩ | ⟨-, h1⟩
    · omega
    · exact h1
  subst hmy hcy
  -- the partner softmax thread of the row
  obtain ⟨g, hgdef⟩ : ∃ g,
      g = 32 * (warpOf L h - 8 + 4 * st) + laneOf L h + ctaOf L h * L.block := ⟨_, rfl⟩
  have hlane : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hr : 32 * (warpOf L h - 8 + 4 * st) + laneOf L h < L.block := by rw [hblk]; omega
  have hgm : g % L.block = 32 * (warpOf L h - 8 + 4 * st) + laneOf L h := by
    rw [hgdef, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hcg : ctaOf L g = ctaOf L h := by
    unfold ctaOf
    rw [hgdef, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
    rfl
  have hwg : warpOf L g = warpOf L h - 8 + 4 * st := by
    rw [show warpOf L g = g % L.block / 32 from rfl, hgm]
    omega
  have hρ : rowOf L g = rowOf L h := by
    have hx : h % L.block = 32 * warpOf L h + laneOf L h := by unfold warpOf laneOf; omega
    unfold rowOf
    rw [hgm, hx]
    omega
  have hg : g < L.threads := thread_lt_of_cta hh hcg
  have hpassed : y + 1 < (X.tr h).length := by
    have := len_of_get he
    simp only at this
    omega
  obtain ⟨i0, pc0, cnt0, md0, hi0, ho0⟩ := hsoft hst hk hyget hpassed hg hcg hwg
  -- its store of the word of generation `G`
  obtain ⟨i, -, pcw, a', ws, hwget, hss, hio⟩ :=
    hf.soft_arrive_store hg (by omega) hi0 (by unfold statsId; omega)
      ⟨J, t, htn, by rw [ho0, hyo, hJ]; omega⟩
  have hss0 := hss
  obtain ⟨-, hla', hsa', -⟩ := hss0
  have hloc : a'.loc = a.loc := by
    rw [hla', hla, hcg, hρ, show warpOf L g / 4 = st by omega]
  have hsize : a'.size = a.size := by rw [hsa', hsa]
  have hcov' : ∀ k < a.size, a'.Covers (a.loc.at k) := fun k hk' => by
    rw [← hloc]
    exact Acc.covers_at (by omega)
  have harea : ∀ k < a.size, InStatsArea L (a.loc.at k) := fun k hk' => by
    rw [hla]
    exact statsWord_area hst (rowOf_lt L h) (by omega)
  have hacc : X.Access (h, j) a false := .inl ⟨bs, ⟨pc, he⟩, rfl⟩
  have hacc' : X.Access (g, i) a' true := .inr (.inl ⟨_, ⟨pcw, hwget⟩, rfl⟩)
  have hcl : CorrLoad L X h j a false st :=
    ⟨rfl, hla, hsa, by rw [hid]; exact harr, J, t, htn, by rw [hid]; exact hJ⟩
  have hid3 : warpOf L g + 3 = statsId st (warpOf L h - 8) := by unfold statsId; omega
  have hov : a'.Overlap a := ⟨_, hcov' 0 (by omega), Acc.covers_at (by omega)⟩
  -- the store happens before the load
  have hhb : baseCausality L X (g, i) (h, j) :=
    stats_baseCausality hpre hX ht hg (by omega) hss hacc' hh h8 h12 hst hcl hacc hov
      (by rw [hid3, hid, hio, ho0, hyo]; omega)
  obtain ⟨x, v, rfl, hrb, hval⟩ :=
    hf.soft_store_f32 hg (by omega) hwget hss (hsl hg (by omega) hcg (len_of_get hwget) hhb)
  have hvb := hval.bytes_eq
  refine (read_of_last_write hX (e := .thread (h, j)) (w := .thread (g, i)) (.inl ⟨pc, he⟩)
    (.inl ⟨pcw, hwget⟩) hloc hsize (by simp [Value.toBytes, hvb, hsa])
    (fun _ _ => modelCausality.of_base L hhb) ?_) ▸
    (⟨x, v, hrb, hval⟩ : ∃ x, F32Read (v.toBytes.map some) x)
  -- every write of a byte of the word is the store, before it or after the load
  intro k hk' w' dst' bytes hw hcov
  cases w' with
  | async i' p => exact (hasync i' p dst' true _ hw.intent hcov (harea k hk')).elim
  | thread e' =>
  obtain ⟨g', i'⟩ := e'
  have hacc'' : X.Access (g', i') dst' true :=
    hw.elim (fun h => .inr (.inl ⟨bytes, h, rfl⟩)) fun ⟨o, h⟩ => .inr (.inr ⟨o, _, h⟩)
  have hg' := access_thread_lt hX hacc''
  rcases ht.stats_access hg' hacc'' hcov (harea k hk') with ⟨hwg', hse⟩ | ⟨-, -, st'', -, hle⟩
  · have hse0 := hse
    obtain ⟨-, hla'', hsa'', -⟩ := hse0
    obtain ⟨hc, hst', hρ'⟩ := word_eq hla'' hsa'' hla' hsa' hcov (hcov' k hk')
      (rowOf_lt L g') (rowOf_lt L g)
    obtain rfl := soft_unique hpre hc hwg' (by omega) hst' hρ'
    have hov' : dst'.Overlap a' := ⟨_, hcov, hcov' k hk'⟩
    rcases Nat.lt_trichotomy i' i with hlt | rfl | hlt
    · exact .inr (.inl (modelCausality.of_base L
        (.single (.inl (po_of_overlap hacc'' hacc' rfl hlt hov')))))
    · exact .inl rfl
    · right; right
      obtain ⟨pcw', hwget'⟩ :=
        (Execution.memWrites_thread_iff_of_not_rmw fun _ _ _ _ h => htm.no_rmw h).mp hw
      have hmono := barOrd_mono (X := X) (g := g') (id := warpOf L g' + 3) hlt.le
      have hne : barOrd X g' i (warpOf L g' + 3) ≠ barOrd X g' i' (warpOf L g' + 3) := by
        intro heq
        have := hf.soft_store_one hg (by omega) hwget hwget' hss hse heq
        omega
      have hov'' : dst'.Overlap a := ⟨_, hcov, Acc.covers_at hk'⟩
      apply modelCausality.of_base L
      exact stats_war hpre hU (g := g') (h := h) hg' hwg' hse hacc'' hh h8 h12 hst hcl hov''
        (by rw [hid3, hid] at *; rw [hio, ho0, hyo] at hmono hne; omega)
  · exact absurd hle.1 (by simp)

end Floats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
