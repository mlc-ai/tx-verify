-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Accesses
public import Lemmas.Kernel.Memory
public import Lemmas.Flow.Scalars
public import Kernels.RmsNorm.Proof.NoBarArrive
public import Kernels.RmsNorm.Proof.Readings

@[expose] public section

/-! # The values the threads read

No write covers an input or a weight, so a load of them returns the launch content: a pair of
halves (`ldx_bytes`, `ldw_bytes`). Every other read returns the bytes of its last visible write
(`ConflictsOrdered.read_of_last`): a reload of a staged input its thread's store of it in the
row (`lds_bytes`), a read of warp `w`'s sum the store of lane `0` of warp `w` before the row's
first barrier (`ldws_bytes`), a read of the total thread `0`'s store before the row's second
barrier (`ldts_bytes`). From the loads, the states hold the input words, the weight words and the
staged inputs of their row (`xa_eq`, `xb_eq`, `tile_data`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Input `m` of tile `t` of thread `g`'s row `i`. -/
def xin (P : Params) (g i t m : Nat) : ℝ := xe P (row g i) (2048 * t + 8 * (g % 256) + m)

/-- Weight `m` of tile `t` of thread `g`. -/
def win (P : Params) (g t m : Nat) : ℝ := P.w (2048 * t + 8 * (g % 256) + m)

theorem hpair_bytes (a b : ℝ) :
    (hpair a b).toBytes = [(h16 a, 0), (h16 a, 1), (h16 b, 0), (h16 b, 1)] := by
  simp [hpair, h16, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ]

theorem rebuild_hpair (a b : ℝ) : rebuild 3 ((hpair a b).toBytes.map some) = .ok (hpair a b) := by
  simp [hpair, rebuild, rebuild.halves, intByte, Value.toBytes, Value.byteAt, Value.bytes,
    FloatFmt.bytes, h16, List.range_succ, pure, Except.pure, bind, Except.bind]

theorem rebuild_fl (y : ℝ) : rebuild 3 ((fl y).toBytes.map some) = .ok (fl y) :=
  rebuild_scalar (by show 0 < 4; decide) rfl

theorem rdv_hpair {pc : Nat} {a : Acc} (x y : ℝ) :
    rdv (some ⟨pc, .rd a ((hpair x y).toBytes.map some)⟩) = hpair x y := by
  simp only [rdv, rebuild_hpair]

theorem rdv_fl {pc : Nat} {a : Acc} (y : ℝ) :
    rdv (some ⟨pc, .rd a ((fl y).toBytes.map some)⟩) = fl y := by
  simp only [rdv, rebuild_fl]

/-- The sites of loads. -/
def Site.isLoad : Site → Bool
  | .ldxa | .ldxb | .ldws | .ldts | .ldwa | .ldsa0 | .ldsa1 | .ldwb | .ldsb0 | .ldsb1 => true
  | _ => false

/-- The event of a load site is a read. -/
theorem rd_event {g : Nat} {d : D} {e : Event} (h : SiteEvent P g d e) (hs : d.site.isLoad = true) :
    ∃ pc a bs, e = ⟨pc, .rd a bs⟩ := by
  obtain ⟨t, o, hf⟩ := h
  rcases hsd : d.site <;> simp only [hsd, Site.isLoad, Bool.false_eq_true] at hs <;>
    simp only [siteTmpl, hsd, Fires] at hf <;> obtain ⟨bs, -, rfl, -⟩ := hf <;> exact ⟨_, _, _, rfl⟩

/-- The sites of stores. -/
def Site.isStore : Site → Bool
  | .stxa0 | .stxa1 | .stxb0 | .stxb1 | .stws | .stts | .stoa | .stob => true
  | _ => false

/-- The event of a store site is a write. -/
theorem wr_event {g : Nat} {d : D} {e : Event} (h : SiteEvent P g d e)
    (hs : d.site.isStore = true) :
    ∃ pc a bs, e = ⟨pc, .wr a bs⟩ := by
  obtain ⟨t, o, hf⟩ := h
  rcases hsd : d.site <;> simp only [hsd, Site.isStore, Bool.false_eq_true] at hs <;>
    simp only [siteTmpl, hsd, Fires] at hf <;> obtain ⟨rfl, -⟩ := hf <;> exact ⟨_, _, _, rfl⟩

theorem rowBase_lt {g i i' q q' : Nat} (hi : i < i') (hq : q < rowLen g) :
    rowBase g i + q < rowBase g i' + q' := by
  unfold rowBase
  have : rowLen g * i + rowLen g ≤ rowLen g * i' := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

theorem rv4_take (es : List Event) {k p : Nat} (h : p + 4 ≤ k) : rv4 (es.take k) p = rv4 es p := by
  simp only [rv4, List.getElem?_take]
  rw [ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'),
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'),
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'),
    ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]

theorem idx_of_row {g : Nat} {d : D} (hr : d.site.inRow = true) : d.idx g =
    rowBase g d.i + d.pos g := by
  unfold D.idx; split <;> simp_all [Site.inRow]

theorem overlap_self {a : Acc} (h : a.size = 4) : a.Overlap a :=
  ⟨a.loc, ⟨rfl, rfl, le_rfl, by omega⟩, ⟨rfl, rfl, le_rfl, by omega⟩⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A read of global memory returns the launch content**: no write covers an input or a
weight. -/
theorem launch_read {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hg : a.loc.space = .global) {j : Nat} (hj : j < 4)
    {c : Byte} (hm : mem0 (a.loc.at j) = some (some c)) : bs[j]? = some (some c) := by
  obtain ⟨-, d, ev, hev, hA, hsh, -⟩ := access_facts hpre hX ht (e := (g, k))
    (.inl ⟨bs, ⟨pc, he⟩, rfl⟩)
  rw [he] at hev
  cases Option.some.inj hev
  have hR := (hsh.global hg).2.2 rfl
  have h4 := hsh.align
  have hI := hpre.hyp.inAlign
  have hW := hpre.hyp.wAlign
  have hIO := hpre.disjIO
  have hWO := hpre.disjWO
  refine hX.launch_byte (e := .thread (g, k)) (.inl ⟨pc, he⟩) (by rw [hsh.size]; exact hj) ?_ hm
  intro w a' bs' hw hc
  obtain ⟨w, rfl, hw⟩ := Execution.NoTma.memWrites_thread
    ((noTma_of_consistent noTma hX).emptyAsync hX) hw
  obtain ⟨-, dw, ew, -, -, hshw, -⟩ := access_facts hpre hX ht
    (.inr (.inl ⟨bs', writes_of_memWrites hpre hX ht hw, rfl⟩))
  obtain ⟨h1, h2, h3, h4'⟩ := hc
  simp only [Loc.at] at h1 h2 h3 h4'
  rcases hshw.space with hgw | hsw
  · obtain ⟨-, hO, -⟩ := hshw.global hgw
    obtain ⟨hO1, hO2, -⟩ := hO rfl
    have := hshw.align
    have := hpre.hyp.outAlign
    rw [hshw.size] at h4'
    omega
  · rw [hsw, hg] at h1
    cases h1

/-- **An input load reads two halves of the row**: element `sub` of tile `t`'s load reads inputs
`2 sub` and `2 sub + 1` of the tile. -/
theorem ldx_bytes {g k pc t : Nat} {d : D} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hA : At P L X g k d ⟨pc, .rd a bs⟩)
    (hs : (d.site = .ldxa ∧ t = 0) ∨ (d.site = .ldxb ∧ t = 1)) :
    bs = (hpair (xin P g d.i t (2 * d.sub)) (xin P g d.i t (2 * d.sub + 1))).toBytes.map some := by
  have hr := hA.inv.row (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.inRow])
  have hsub := hA.inv.sub.1 (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.vec])
  have ha : a = vacc .global 0 (P.I + off g d.i + 4096 * t) d.sub := by
    rcases rd_site hA.event with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases hs with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;> rw [h1] at h2 <;> first | (simp; done) | cases h2
  subst ha
  have hlen := hX.read_length (e := .thread (g, k)) (.inl ⟨pc, he⟩)
  simp only [row] at hr
  have key : ∀ j < 4, bs[j]? = some (some (h16 (P.x ((off g d.i + 4096 * t + 4 * d.sub + j) / 2)),
      (off g d.i + 4096 * t + 4 * d.sub + j) % 2)) := by
    intro j hj
    refine launch_read hpre hX ht he rfl hj ?_
    have h := hpre.input (off g d.i + 4096 * t + 4 * d.sub + j) (by
      simp only [off, row]; rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega)
    simp only [vacc, Loc.at]
    rw [← h]
    congr 2
    omega
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · rw [key j hj, List.getElem?_map, hpair_bytes]
    simp only [xin, xe, h16, row]
    interval_cases j <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] <;>
      refine ⟨by congr 2; simp only [off, row]; omega, by simp only [off, row]; omega⟩
  · rw [List.getElem?_eq_none (by simp only [vacc] at hlen; omega), List.getElem?_eq_none]
    simp only [List.length_map, hpair_bytes, List.length_cons, List.length_nil]
    omega

/-- **A weight load reads two halves of the weights**: element `sub` of tile `t`'s load reads
weights `2 sub` and `2 sub + 1` of the tile. -/
theorem ldw_bytes {g k pc t : Nat} {d : D} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hA : At P L X g k d ⟨pc, .rd a bs⟩)
    (hs : (d.site = .ldwa ∧ t = 0) ∨ (d.site = .ldwb ∧ t = 1)) :
    bs = (hpair (win P g t (2 * d.sub)) (win P g t (2 * d.sub + 1))).toBytes.map some := by
  have hsub := hA.inv.sub.1 (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.vec])
  have ha : a = vacc .global 0 (P.W + 16 * (g % 256) + 4096 * t) d.sub := by
    rcases rd_site hA.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases hs with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;> rw [h1] at h2 <;> first | (simp; done) | cases h2
  subst ha
  have hlen := hX.read_length (e := .thread (g, k)) (.inl ⟨pc, he⟩)
  have key : ∀ j < 4, bs[j]? = some (some (h16
      (P.w ((16 * (g % 256) + 4096 * t + 4 * d.sub + j) / 2)),
      (16 * (g % 256) + 4096 * t + 4 * d.sub + j) % 2)) := by
    intro j hj
    refine launch_read hpre hX ht he rfl hj ?_
    have h := hpre.weight (16 * (g % 256) + 4096 * t + 4 * d.sub + j) (by
      rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega)
    simp only [vacc, Loc.at]
    rw [← h]
    congr 2
    omega
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · rw [key j hj, List.getElem?_map, hpair_bytes]
    simp only [win, h16]
    interval_cases j <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] <;>
      refine ⟨by congr 2; omega, by omega⟩
  · rw [List.getElem?_eq_none (by simp only [vacc] at hlen; omega), List.getElem?_eq_none]
    simp only [List.length_map, hpair_bytes, List.length_cons, List.length_nil]
    omega

omit hpre in
/-- The event of a followed state is not undefined behaviour. -/
theorem At.not_ub {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  have hg := Frame.lt_of_get hX he
  exact not_ub_of_followed ht hg hA.state he

/-- The values a vector load of a row read, from their bytes. -/
theorem load_vals {g k q : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) (hr : d.site.inRow = true) (hq : q + 3 ≤ d.pos g) (v : Nat → Value)
    (hld : ∀ j < 4, ∀ d' : D, Inv P g d' → d'.site.inRow = true → d'.pos g = q + j →
      d'.site.isLoad = true)
    (hv : ∀ j < 4, ∀ k' d' pc a bs, X.get (g, k') = some ⟨pc, .rd a bs⟩ →
      At P L X g k' d' ⟨pc, .rd a bs⟩ → d'.i = d.i → d'.pos g = q + j → d'.site.inRow = true →
      rdv (some ⟨pc, .rd a bs⟩) = v j) :
    rv4 (X.tr g) (rowBase g d.i + q) = [v 0, v 1, v 2, v 3] := by
  have hub := At.not_ub hX ht he hA
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  have hlt := pos_lt hA.inv hr
  have hj : ∀ j < 4, rdv (X.tr g)[rowBase g d.i + q + j]? = v j := by
    intro j hj
    have hk' : rowBase g d.i + (q + j) < k ∨
        (rowBase g d.i + (q + j) = k ∧ ∀ pc, e ≠ ⟨pc, .exit⟩) := by
      rcases Nat.lt_or_eq_of_le (show rowBase g d.i + (q + j) ≤ k by omega) with h | h
      · exact .inl h
      · refine .inr ⟨h, fun pc hx => ?_⟩
        subst hx
        have := exit_site hA.event
        simp [this, Site.inRow] at hr
    obtain ⟨d', e', he', hA', hi', hp', hr'⟩ := row_state hpre hX ht he hub (i := d.i) (q := q + j)
      (by omega) hk'
    obtain ⟨pc, a, bs, rfl⟩ := rd_event hA'.event (hld j hj d' hA'.inv hr' hp')
    rw [← Nat.add_assoc] at he'
    change rdv (X.get (g, _)) = _
    rw [he']
    exact hv j hj _ d' pc a bs he' (by rw [Nat.add_assoc]; exact hA') hi' hp' hr'
  simp only [rv4]
  have h0 := hj 0 (by decide)
  have h1 := hj 1 (by decide)
  have h2 := hj 2 (by decide)
  have h3 := hj 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

/-- **A read returns its last write**: a write of its word before it, such that every write of
the word before the read is it, before it, or after the read. -/
theorem read_last {r w : EvId} {a a0 : Acc} {bs : List (Option Byte)} {ws : List Byte}
    (hr : X.Reads r a bs) (hw : X.Writes w a0 ws) (ha : a0 = a) (hlen : ws.length = 4)
    (hv : baseCausality L X w r)
    (hlast : ∀ w' a' ws', X.Writes w' a' ws' → a'.loc = a.loc → baseCausality L X w' r →
      w' = w ∨ baseCausality L X w' w ∨ baseCausality L X r w') : bs = ws.map some := by
  subst ha
  obtain ⟨-, _, _, -, -, hsr, -⟩ := access_facts hpre hX ht (.inl ⟨bs, hr, rfl⟩)
  refine (conflicts_ordered hpre hX ht).read_of_last hX (e := .thread r) (w := .thread w)
    (.inl hr) (fun _ _ _ _ ⟨he', _, hp⟩ => by cases he'; exact no_rmw hpre hX ht hp) (.inl hw)
    (by rw [hlen, hsr.size])
    (fun _ _ => .inl hv) ?_
  intro k hk w' a' ws' hw' hc hvis
  obtain ⟨w', rfl, hw'⟩ := Execution.NoTma.memWrites_thread
    ((noTma_of_consistent noTma hX).emptyAsync hX) hw'
  have hw' := writes_of_memWrites hpre hX ht hw'
  obtain ⟨-, _, _, -, -, hsw, -⟩ := access_facts hpre hX ht (.inr (.inl ⟨ws', hw', rfl⟩))
  have hl := loc_eq_of_overlap hsw.size hsr.size hsw.align hsr.align
    ⟨a0.loc.at k, hc, Acc.covers_at hk⟩
  rcases hvis with hvis | halloc
  swap
  · obtain ⟨_, _, _, _, halloc, _, _, _, _⟩ := halloc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hget, _, _, _⟩ := halloc
    cases (noTma_of_consistent noTma hX) _ _ _ hget
  rcases hlast w' a' ws' hw' hl hvis with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inl h)
  · exact absurd (Relation.TransGen.trans hvis h) (baseCausality_irrefl hX.object.cause)

/-- The four words of tile `t`'s input load of thread `g`'s row `i`. -/
def xwords (P : Params) (g i t : Nat) : List Value :=
  [hpair (xin P g i t 0) (xin P g i t 1), hpair (xin P g i t 2) (xin P g i t 3),
    hpair (xin P g i t 4) (xin P g i t 5), hpair (xin P g i t 6) (xin P g i t 7)]

/-- The four words of tile `t`'s weight load of thread `g`. -/
def wwords (P : Params) (g t : Nat) : List Value :=
  [hpair (win P g t 0) (win P g t 1), hpair (win P g t 2) (win P g t 3),
    hpair (win P g t 4) (win P g t 5), hpair (win P g t 6) (win P g t 7)]

/-- **The words a row's input load read.** -/
theorem xwords_eq {g k t q : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) (hr : d.site.inRow = true) (htq : (t = 0 ∧ q = 0) ∨ (t = 1 ∧ q = 12))
    (hp : q + 3 ≤ d.pos g) : rv4 (X.tr g) (rowBase g d.i + q) = xwords P g d.i t := by
  have h := load_vals hpre hX ht he hA hr hp
    (fun j => hpair (xin P g d.i t (2 * j)) (xin P g d.i t (2 * j + 1))) ?_ ?_
  · rw [h]; rfl
  · intro j hj d' hi' hr' hp'
    rcases htq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(ldxa_of_pos hi' hr' hj (by omega)).1]; rfl
    · rw [(ldxb_of_pos hi' hr' hj (by omega)).1]; rfl
  · intro j hj k' d' pc a bs he' hA' hi' hp' hr'
    have hsub : d'.sub = j ∧ ((d'.site = .ldxa ∧ t = 0) ∨ (d'.site = .ldxb ∧ t = 1)) := by
      rcases htq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := ldxa_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inl ⟨h1, rfl⟩⟩
      · obtain ⟨h1, h2⟩ := ldxb_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inr ⟨h1, rfl⟩⟩
    rw [ldx_bytes hpre hX ht he' hA' hsub.2, rdv_hpair, hsub.1, hi']

/-- **The words a weight load read.** -/
theorem wwords_eq {g k t q : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) (hr : d.site.inRow = true)
    (htq : (t = 0 ∧ q = p1 g + 2) ∨ (t = 1 ∧ q = p1 g + 18))
    (hp : q + 3 ≤ d.pos g) : rv4 (X.tr g) (rowBase g d.i + q) = wwords P g t := by
  have h := load_vals hpre hX ht he hA hr hp
    (fun j => hpair (win P g t (2 * j)) (win P g t (2 * j + 1))) ?_ ?_
  · rw [h]; rfl
  · intro j hj d' hi' hr' hp'
    rcases htq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(ldwa_of_pos hi' hr' hj (by omega)).1]; rfl
    · rw [(ldwb_of_pos hi' hr' hj (by omega)).1]; rfl
  · intro j hj k' d' pc a bs he' hA' hi' hp' hr'
    have hsub : d'.sub = j ∧ ((d'.site = .ldwa ∧ t = 0) ∨ (d'.site = .ldwb ∧ t = 1)) := by
      rcases htq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := ldwa_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inl ⟨h1, rfl⟩⟩
      · obtain ⟨h1, h2⟩ := ldwb_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inr ⟨h1, rfl⟩⟩
    rw [ldw_bytes hpre hX ht he' hA' hsub.2, rdv_hpair, hsub.1]

omit hpre hX ht in
theorem xwords_hwords (P : Params) (g i t : Nat) : xwords P g i t = hwords (xin P g i t) := rfl

omit hpre hX ht in
theorem wwords_hwords (P : Params) (g t : Nat) : wwords P g t = hwords (win P g t) := rfl

omit hpre hX ht in
/-- A widened input half of a row is its number. -/
theorem xw_xwords (P : Params) (g i t : Nat) {m : Nat} (hm : m < 8) :
    xw (xwords P g i t) m = fl (xin P g i t m) :=
  xw_hwords (xin P g i t) hm

/-- **A state past a row's first input load holds its input words.** -/
theorem xa_eq {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e) (hA : At P L X g k d e)
    (hr : d.site.inRow = true) (hp : 4 ≤ d.pos g) : d.xa = xwords P g d.i 0 := by
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  have h := xwords_eq hpre hX ht he hA hr (.inl ⟨rfl, rfl⟩) (by omega)
  rw [Nat.add_zero] at h
  rw [hA.data.xa hr hp, rv4_take _ (by omega), h]

/-- **A state past a row's second input load holds its input words.** -/
theorem xb_eq {g k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e) (hA : At P L X g k d e)
    (hr : d.site.inRow = true) (hp : 16 ≤ d.pos g) : d.xb = xwords P g d.i 1 := by
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  have h := xwords_eq hpre hX ht he hA hr (.inr ⟨rfl, rfl⟩) (by omega)
  rw [hA.data.xb hr hp, rv4_take _ (by omega), h]

/-- **A staging store writes the thread's input** of its row. -/
theorem stx_word {g kw pcw t h : Nat} {dw : D} {aw : Acc} {ws : List Byte}
    (hew : X.get (g, kw) = some ⟨pcw, .wr aw ws⟩) (hAw : At P L X g kw dw ⟨pcw, .wr aw ws⟩)
    (hsw : (dw.site = .stxa0 ∧ t = 0 ∧ h = 0) ∨ (dw.site = .stxa1 ∧ t = 0 ∧ h = 1) ∨
      (dw.site = .stxb0 ∧ t = 1 ∧ h = 0) ∨ (dw.site = .stxb1 ∧ t = 1 ∧ h = 1)) :
    aw = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192 * t + 16 * h) dw.sub ∧
      ws = (fl (xin P g dw.i t (4 * h + dw.sub))).toBytes := by
  have hr : dw.site.inRow = true := by
    rcases hsw with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.inRow]
  have hsub := hAw.inv.sub.1 (by
    rcases hsw with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.vec])
  rcases wr_site hAw.event with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases hsw with ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ <;>
    rw [h1] at h2 <;> (try cases h2)
  · refine ⟨by simp, ?_⟩
    rw [xa_eq hpre hX ht hew hAw hr (by simp only [D.pos, h1]; omega),
      xw_xwords P g _ _ (by omega)]
    simp
  · refine ⟨by simp [vacc], ?_⟩
    rw [xa_eq hpre hX ht hew hAw hr (by simp only [D.pos, h1]; omega),
      xw_xwords P g _ _ (by omega)]
  · refine ⟨by simp [vacc], ?_⟩
    rw [xb_eq hpre hX ht hew hAw hr (by simp only [D.pos, h1]; omega),
      xw_xwords P g _ _ (by omega)]
    simp
  · refine ⟨by simp [vacc], ?_⟩
    rw [xb_eq hpre hX ht hew hAw hr (by simp only [D.pos, h1]; omega),
      xw_xwords P g _ _ (by omega)]

/-- **A reload of a staged input reads its thread's store of it in the row.** -/
theorem lds_bytes {g k pc t h : Nat} {d : D} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hA : At P L X g k d ⟨pc, .rd a bs⟩)
    (hs : (d.site = .ldsa0 ∧ t = 0 ∧ h = 0) ∨ (d.site = .ldsa1 ∧ t = 0 ∧ h = 1) ∨
      (d.site = .ldsb0 ∧ t = 1 ∧ h = 0) ∨ (d.site = .ldsb1 ∧ t = 1 ∧ h = 1)) :
    bs = (fl (xin P g d.i t (4 * h + d.sub))).toBytes.map some := by
  have hr : d.site.inRow = true := by
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.inRow]
  have hsub := hA.inv.sub.1 (by
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.vec])
  have hpos : d.pos g = p1 g + 6 + 4 * h + 16 * t + d.sub := by
    rcases hs with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ <;>
      simp [D.pos, h1]
  have ha : a = vacc .shared (g / 256) (P.S + 32 * (g % 256) + 8192 * t + 16 * h) d.sub := by
    rcases rd_site hA.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, rfl⟩ |
      ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      rcases hs with ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩ <;>
      rw [h1] at h2 <;> first | (simp [vacc]; done) | (simp [vacc]; omega) | cases h2
  subst ha
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  have hlt := pos_lt hA.inv hr
  have hub := At.not_ub hX ht he hA
  -- the store of the word in the row
  obtain ⟨dw, ew, hew, hAw, hiw, hpw, hrw⟩ := row_state hpre hX ht he hub (i := d.i)
    (q := 4 + 4 * h + 12 * t + d.sub) (by unfold rowLen; omega) (.inl (by omega))
  have hsw : ((dw.site = .stxa0 ∧ t = 0 ∧ h = 0) ∨ (dw.site = .stxa1 ∧ t = 0 ∧ h = 1) ∨
      (dw.site = .stxb0 ∧ t = 1 ∧ h = 0) ∨ (dw.site = .stxb1 ∧ t = 1 ∧ h = 1)) ∧
      dw.sub = d.sub := by
    rcases hs with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := stxa0_of_pos hAw.inv hrw hsub (by omega); exact ⟨.inl ⟨h1, rfl, rfl⟩, h2⟩
    · obtain ⟨h1, h2⟩ := stxa1_of_pos hAw.inv hrw hsub (by omega)
      exact ⟨.inr (.inl ⟨h1, rfl, rfl⟩), h2⟩
    · obtain ⟨h1, h2⟩ := stxb0_of_pos hAw.inv hrw hsub (by omega)
      exact ⟨.inr (.inr (.inl ⟨h1, rfl, rfl⟩)), h2⟩
    · obtain ⟨h1, h2⟩ := stxb1_of_pos hAw.inv hrw hsub (by omega)
      exact ⟨.inr (.inr (.inr ⟨h1, rfl, rfl⟩)), h2⟩
  obtain ⟨pcw, aw, ws, rfl⟩ := wr_event hAw.event (by
    rcases hsw.1 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.isStore])
  obtain ⟨haw, hws⟩ := stx_word hpre hX ht hew hAw hsw.1
  rw [hsw.2] at haw hws
  rw [hiw] at hws
  subst haw hws
  have hkw : rowBase g d.i + (4 + 4 * h + 12 * t + d.sub) < k := by omega
  refine read_last hpre hX ht (r := (g, k)) (w := (g, _)) ⟨pc, he⟩ ⟨pcw, hew⟩ rfl rfl
    (po_baseCausality (.inr (.inl ⟨_, ⟨pcw, hew⟩, rfl⟩)) (.inl ⟨_, ⟨pc, he⟩, rfl⟩) hkw
        (overlap_self rfl)) ?_
  rintro ⟨x, kx⟩ a' ws' ⟨pcx, hx⟩ hl hvis
  obtain ⟨-, dx, ex, hex, hAx, hsx, -⟩ := access_facts hpre hX ht (e := (x, kx))
    (.inr (.inl ⟨ws', ⟨pcx, hx⟩, rfl⟩))
  rw [hx] at hex
  cases Option.some.inj hex
  have hsp : a'.loc.space = .shared := by rw [hl]; rfl
  obtain ⟨hc, -, -, hst, -⟩ := hsx.shared hsp
  have hxg : x = g := by
    have h1 := hst (by rw [hl]; simp only [vacc]; omega)
    rw [hl] at hc h1
    simp only [vacc] at hc h1
    omega
  subst hxg
  have hrx : dx.site.inRow = true := by
    rcases wr_site hAx.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.inRow]
  have hkx : kx = rowBase x dx.i + (4 + 4 * h + 12 * t + d.sub) := by
    rw [show kx = dx.idx x from hAx.index, idx_of_row hrx]
    have hsx' := hAx.inv.sub.1
    have h0 := hAx.inv.stws
    have h00 := hAx.inv.stts
    rcases wr_site hAx.event with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ |
      ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ <;>
      simp only [vacc, Loc.mk.injEq, reduceCtorEq, false_and] at hl <;>
      simp only [h1, D.pos, Site.vec, forall_const, reduceCtorEq,
        false_implies] at hsx' h0 h00 ⊢ <;>
      rcases hs with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> omega
  rcases Nat.lt_trichotomy dx.i d.i with hlt | heq | hgt
  · refine .inr
      (.inl (po_baseCausality (.inr (.inl ⟨_, ⟨pcx, hx⟩, rfl⟩))
        (.inr (.inl ⟨_, ⟨pcw, hew⟩, rfl⟩)) ?_ ?_))
    · rw [hkx]; exact rowBase_lt hlt (by unfold rowLen; omega)
    · exact ⟨a'.loc, ⟨rfl, rfl, le_rfl, by rw [hsx.size]; omega⟩, by
        rw [hl]; exact ⟨rfl, rfl, le_rfl, by simp [vacc]⟩⟩
  · left; rw [hkx, heq]
  · refine .inr (.inr (po_baseCausality (.inl ⟨_, ⟨pc, he⟩, rfl⟩)
      (.inr (.inl ⟨_, ⟨pcx, hx⟩, rfl⟩)) ?_ ?_))
    · rw [hkx, hk]; exact rowBase_lt hgt hlt
    · exact ⟨a'.loc, by rw [hl]; exact ⟨rfl, rfl, le_rfl, by simp [vacc]⟩,
        ⟨rfl, rfl, le_rfl, by rw [hsx.size]; omega⟩⟩

/-- **A thread reached the barriers of its CTA's peers**: when a thread's state has passed the
arrival on barrier `0` of number `2 i + b`, every thread of its CTA has its arrival `b` of row `i`
(the row's first barrier for `b = 0`, its second for `b = 1`). -/
theorem peer_reached {y k x i b : Nat} {dy : D} {e : Event} (he : X.get (y, k) = some e)
    (hA : At P L X y k dy e) (hx : x < L.threads) (hc : x / 256 = y / 256) (hb : b < 2)
    (hn : 2 * i + b < dy.bc0) :
    ∃ pc, X.get (x, rowBase x i + barPos x b) = some ⟨pc, .bar 0 none⟩ := by
  have hB := hpre.hyp.block
  have hyl := len_of_get he
  have hcnt : 2 * i + b + 1 ≤ ((X.tr y).take k).countP (Execution.isBarId 0) := by
    rw [hA.bc0]; omega
  obtain ⟨iy, ev, hget, hbar, hcy⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0) hcnt
  have hiy : iy < k := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h' => absurd hiy h')] at hget
  rw [List.take_take, Nat.min_eq_left hiy.le] at hcy
  obtain ⟨pcy, kd⟩ := ev
  cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true] at hbar
  rename_i id cnt mode
  simp only [beq_iff_eq] at hbar
  subst hbar
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (y, iy) _ _ _ hget).elim
  have hyb : X.IsBarrier (y, iy) 0 cnt pcy := hget
  obtain ⟨-, rfl, -⟩ := bar_facts hpre hX ht hyb
  have hd := released hpre hX ht hyb (by simp only at hyl; omega)
  obtain ⟨j, pcj, hxb, hord⟩ := arrival_exists hpre hX ht hd hx (by rw [hB]; omega) hyb rfl rfl
  rw [hcy] at hord
  obtain ⟨-, -, dj, hAj, hsj⟩ := bar_facts hpre hX ht hxb
  have hbc := hAj.bc0
  rw [hord] at hbc
  have hidx := hAj.index
  refine ⟨pcj, ?_⟩
  rcases hsj with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, h1⟩
  · simp only [D.bc0, hs] at hbc
    have : b = 0 := by omega
    subst this
    have : dj.i = i := by omega
    simp only [D.idx, hs, D.pos, this] at hidx
    rw [show rowBase x i + barPos x 0 = j by simp only [barPos]; omega]
    exact hxb
  · simp only [D.bc0, hs] at hbc
    have : b = 1 := by omega
    subst this
    have : dj.i = i := by omega
    simp only [D.idx, hs, D.pos, this] at hidx
    rw [show rowBase x i + barPos x 1 = j by simp only [barPos]; omega]
    exact hxb
  · cases h1

/-- The word of warp `w`'s sum. -/
def wsAcc (c w : Nat) (P : Params) : Acc := { loc := ⟨.shared, c, P.S + 4 * w + 16384⟩, size := 4 }

/-- **A write of a reduction word**: lane `0` of a warp stores the warp's sum to its word, thread
`0` the total to the first word. -/
theorem red_write {x kx pc : Nat} {a : Acc} {ws : List Byte} {dx : D}
    (he : X.get (x, kx) = some ⟨pc, .wr a ws⟩) (hA : At P L X x kx dx ⟨pc, .wr a ws⟩)
    (hsp : a.loc.space = .shared) (hge : P.S + 16384 ≤ a.loc.addr) :
    a.loc.cta = x / 256 ∧ dx.site.inRow = true ∧
      ((dx.site = .stws ∧ x % 256 % 32 = 0 ∧ a.loc.addr = P.S + 16384 + 4 * (x % 256 / 32) ∧
          kx = rowBase x dx.i + 29) ∨
        (dx.site = .stts ∧ x % 256 = 0 ∧ a.loc.addr = P.S + 16384 ∧ kx = rowBase x dx.i + 37)) := by
  obtain ⟨hg, d', ev, hev, hA', hsh, -⟩ := access_facts hpre hX ht (e := (x, kx))
    (.inr (.inl ⟨ws, ⟨pc, he⟩, rfl⟩))
  rw [he] at hev
  cases Option.some.inj hev
  have hdd : d' = dx := by
    have := hA'.state.symm.trans hA.state
    exact Option.some.inj (Option.some.inj this)
  subst hdd
  obtain ⟨hc, -, -, -, hred⟩ := hsh.shared hsp
  have hidx : kx = d'.idx x := hA.index
  rcases hred hge with ⟨h1, -, h2, h3⟩ | ⟨h1, -, h2, h3⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · refine ⟨hc, by simp [h1, Site.inRow], .inl ⟨h1, h3, h2, ?_⟩⟩
    simp only [hidx, D.idx, D.pos, h1]
  · refine ⟨hc, by simp [h1, Site.inRow], .inr ⟨h1, h3, h2, ?_⟩⟩
    simp only [hidx, D.idx, D.pos, h1, l0, l8, h3]; simp
  · cases h2
  · cases h2

omit hX ht in
theorem lt_threads {y x : Nat} (hy : y < L.threads) (hxy : x / 256 = y / 256) :
    x < L.threads := by
  have hB := hpre.hyp.block
  have hG := hpre.hyp.grid
  simp only [Launch.threads, hB, hG] at hy ⊢
  omega

/-- **A read of a warp's sum reads the store of lane `0` of the warp** in the row. -/
theorem ldws_bytes {y k pc : Nat} {a : Acc} {bs : List (Option Byte)} {dy : D}
    (he : X.get (y, k) = some ⟨pc, .rd a bs⟩) (hA : At P L X y k dy ⟨pc, .rd a bs⟩)
    (hs : dy.site = .ldws) :
    ∃ kx dx pcx, X.get (256 * (y / 256) + 32 * (y % 256), kx) = some ⟨pcx,
        .wr (wsAcc (y / 256) (y % 256) P) (bsumV (ssqV dx) dx.ra 5).toBytes⟩ ∧
      At P L X (256 * (y / 256) + 32 * (y % 256)) kx dx ⟨pcx,
        .wr (wsAcc (y / 256) (y % 256) P) (bsumV (ssqV dx) dx.ra 5).toBytes⟩ ∧
      dx.site = .stws ∧ dx.i = dy.i ∧ bs = (bsumV (ssqV dx) dx.ra 5).toBytes.map some := by
  have h8 := hA.inv.ldws hs
  have hr : dy.site.inRow = true := by simp [hs, Site.inRow]
  have hyg := Frame.lt_of_get hX he
  have ha : a = wsAcc (y / 256) (y % 256) P := by
    rcases rd_site hA.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hs] at h1 <;> try cases h1
    simp only [wsAcc, Acc.mk.injEq, Loc.mk.injEq, and_true, true_and]
    omega
  subst ha
  set x := 256 * (y / 256) + 32 * (y % 256) with hxdef
  have hxc : x / 256 = y / 256 := by omega
  have hxl : x % 256 % 32 = 0 := by omega
  have hxw : x % 256 / 32 = y % 256 := by omega
  have hxg : x < L.threads := lt_threads hpre hyg hxc
  have hk : k = rowBase y dy.i + dy.pos y := hA.index.trans (idx_of_row hr)
  -- lane 0 of warp `y % 256` reached the row's first barrier
  obtain ⟨pcb, hxb⟩ := peer_reached hpre hX ht he hA hxg hxc (b := 0) (i := dy.i) (by decide)
    (by simp [D.bc0, hs])
  have hl0 : l0 x = 1 := by simp [l0, hxl]
  obtain ⟨dx, ex, hex, hAx, hix, hpx, hrx⟩ := row_state hpre hX ht hxb (by intro _ _ h; cases h)
    (i := dy.i) (q := 29) (by unfold rowLen p1; omega) (.inl (by simp only [barPos, hl0]; omega))
  have hsx := stws_of_pos hAx.inv hrx hxl hpx
  obtain ⟨pcx, aw, ws, rfl⟩ := wr_event hAx.event (by simp [hsx, Site.isStore])
  have hww : aw = wsAcc (y / 256) (y % 256) P ∧ ws = (bsumV (ssqV dx) dx.ra 5).toBytes := by
    rcases wr_site hAx.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, rfl, rfl⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hsx] at h1 <;> try cases h1
    refine ⟨?_, rfl⟩
    simp only [wsAcc, Acc.mk.injEq, Loc.mk.injEq, and_true, true_and]
    omega
  obtain ⟨rfl, rfl⟩ := hww
  refine ⟨_, dx, pcx, hex, hAx, hsx, hix, ?_⟩
  have hnb : ∀ (pc : Nat) id c, (⟨pcx, .wr (wsAcc (y / 256) (y % 256) P)
      (bsumV (ssqV dx) dx.ra 5).toBytes⟩ : Event) ≠ ⟨pc, .bar id c⟩ := by
    intro _ _ _ h; cases h
  have hnr : ∀ (pc' : Nat) id c, (⟨pc, .rd (wsAcc (y / 256) (y % 256) P) bs⟩ : Event) ≠
      ⟨pc', .bar id c⟩ := by intro _ _ _ h; cases h
  refine read_last hpre hX ht (r := (y, k)) (w := (x, _)) ⟨pc, he⟩ ⟨pcx, hex⟩ rfl
    (by simp only [Value.toBytes, List.length_map, List.length_range]; exact addV_bytes _ _)
    (baseCausality_of_counts hpre hX ht hex hAx he hA hnb hxc
        (.inl (by simp [D.bc0, hs, hsx, hix]))) ?_
  rintro ⟨x', kx'⟩ a' ws' ⟨pcx', hx'⟩ hl hvis
  obtain ⟨-, dx', ex', hex', hAx', hsh', -⟩ := access_facts hpre hX ht (e := (x', kx'))
    (.inr (.inl ⟨ws', ⟨pcx', hx'⟩, rfl⟩))
  rw [hx'] at hex'
  cases Option.some.inj hex'
  have hov : a'.Overlap (wsAcc (y / 256) (y % 256) P) :=
    ⟨a'.loc, ⟨rfl, rfl, le_rfl, by rw [hsh'.size]; omega⟩,
      by rw [hl]; exact ⟨rfl, rfl, le_rfl, by simp [wsAcc]⟩⟩
  obtain ⟨hc', hr', hw'⟩ := red_write hpre hX ht hx' hAx' (by rw [hl]; rfl)
    (by rw [hl]; simp [wsAcc])
  have hcta : x' / 256 = y / 256 := by rw [← hc', hl]; rfl
  have haddr : a'.loc.addr = P.S + 4 * (y % 256) + 16384 := by rw [hl]; rfl
  rcases hw' with ⟨hs', hl', ha', hk'⟩ | ⟨hs', hl', ha', hk'⟩
  · -- another store of the warp's lane 0
    have hxx : x' = x := by omega
    subst hxx
    rcases Nat.lt_trichotomy dx'.i dy.i with hlt | heq | hgt
    · refine .inr
        (.inl (po_baseCausality (.inr (.inl ⟨_, ⟨pcx', hx'⟩, rfl⟩))
          (.inr (.inl ⟨_, ⟨pcx, hex⟩, rfl⟩)) ?_ hov))
      rw [hk']; exact rowBase_lt hlt (by unfold rowLen p1; omega)
    · left; rw [hk', heq]
    · exact .inr (.inr (baseCausality_of_counts hpre hX ht he hA hx' hAx' hnr hcta.symm
        (.inr (by simp [D.bc1, hs, hs', hgt]))))
  · -- thread 0's store of the total: the reader is thread 0
    have hy0 : y % 256 = 0 := by omega
    have hxx : x' = x := by omega
    have hyx : y = x := by omega
    subst hxx
    rcases Nat.lt_trichotomy dx'.i dy.i with hlt | heq | hgt
    · refine .inr
        (.inl (po_baseCausality (.inr (.inl ⟨_, ⟨pcx', hx'⟩, rfl⟩))
          (.inr (.inl ⟨_, ⟨pcx, hex⟩, rfl⟩)) ?_ hov))
      rw [hk']; exact rowBase_lt hlt (by unfold rowLen p1; omega)
    · have hx'' : X.get (y, kx') = some ⟨pcx', .wr a' ws'⟩ := by rw [hyx]; exact hx'
      have := po_baseCausality (L := L) (.inl ⟨_, ⟨pc, he⟩, rfl⟩)
        (.inr (.inl ⟨_, ⟨pcx', hx''⟩, rfl⟩))
          (j := kx') ?_
        hov.symm
      · rw [← hyx]; exact .inr (.inr this)
      rw [hk', hk, heq, hyx]
      simp only [D.pos, hs, l0, hxl, ↓reduceIte]
      omega
    · exact .inr (.inr (baseCausality_of_counts hpre hX ht he hA hx' hAx' hnr hcta.symm
        (.inr (by simp [D.bc1, hs, hs', hgt]))))

/-- **A read of the total reads thread `0`'s store of it** in the row. -/
theorem ldts_bytes {y k pc : Nat} {a : Acc} {bs : List (Option Byte)} {dy : D}
    (he : X.get (y, k) = some ⟨pc, .rd a bs⟩) (hA : At P L X y k dy ⟨pc, .rd a bs⟩)
    (hs : dy.site = .ldts) :
    ∃ kx dx pcx, X.get (256 * (y / 256), kx) = some ⟨pcx,
        .wr (wsAcc (y / 256) 0 P) (bsumV dx.u dx.rb 5).toBytes⟩ ∧
      At P L X (256 * (y / 256)) kx dx
        ⟨pcx, .wr (wsAcc (y / 256) 0 P) (bsumV dx.u dx.rb 5).toBytes⟩ ∧
      dx.site = .stts ∧ dx.i = dy.i ∧ bs = (bsumV dx.u dx.rb 5).toBytes.map some := by
  have hr : dy.site.inRow = true := by simp [hs, Site.inRow]
  have hyg := Frame.lt_of_get hX he
  have ha : a = wsAcc (y / 256) 0 P := by
    rcases rd_site hA.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hs] at h1 <;> try cases h1
    simp [wsAcc]
  subst ha
  set x := 256 * (y / 256) with hxdef
  have hxc : x / 256 = y / 256 := by omega
  have hx0 : x % 256 = 0 := by omega
  have hxg : x < L.threads := lt_threads hpre hyg hxc
  have hk : k = rowBase y dy.i + dy.pos y := hA.index.trans (idx_of_row hr)
  obtain ⟨pcb, hxb⟩ := peer_reached hpre hX ht he hA hxg hxc (b := 1) (i := dy.i) (by decide)
    (by simp [D.bc0, hs])
  have hl0 : l0 x = 1 := by simp [l0, hx0]
  have hl8 : l8 x = 1 := by simp [l8, hx0]
  have hw0 : w0 x = 1 := by simp [w0, hx0]
  have ht0 : t0 x = 1 := by simp [t0, hx0]
  obtain ⟨dx, ex, hex, hAx, hix, hpx, hrx⟩ := row_state hpre hX ht hxb (by intro _ _ h; cases h)
    (i := dy.i) (q := 37) (by unfold rowLen p1; omega)
    (.inl (by simp only [barPos, p1, hl0, hl8, hw0, ht0]; omega))
  have hsx := stts_of_pos hAx.inv hrx hx0 (by rw [hpx, hl0, hl8])
  obtain ⟨pcx, aw, ws, rfl⟩ := wr_event hAx.event (by simp [hsx, Site.isStore])
  have hww : aw = wsAcc (y / 256) 0 P ∧ ws = (bsumV dx.u dx.rb 5).toBytes := by
    rcases wr_site hAx.event with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hsx] at h1 <;> try cases h1
    refine ⟨?_, rfl⟩
    simp only [wsAcc, Acc.mk.injEq, Loc.mk.injEq, and_true, true_and]
    omega
  obtain ⟨rfl, rfl⟩ := hww
  refine ⟨_, dx, pcx, hex, hAx, hsx, hix, ?_⟩
  have hnb : ∀ (pc : Nat) id c, (⟨pcx, .wr (wsAcc (y / 256) 0 P)
      (bsumV dx.u dx.rb 5).toBytes⟩ : Event) ≠ ⟨pc, .bar id c⟩ := by
    intro _ _ _ h; cases h
  have hnr : ∀ (pc' : Nat) id c, (⟨pc, .rd (wsAcc (y / 256) 0 P) bs⟩ : Event) ≠
      ⟨pc', .bar id c⟩ := by intro _ _ _ h; cases h
  refine read_last hpre hX ht (r := (y, k)) (w := (x, _)) ⟨pc, he⟩ ⟨pcx, hex⟩ rfl
    (by simp only [Value.toBytes, List.length_map, List.length_range]; exact addV_bytes _ _)
    (baseCausality_of_counts hpre hX ht hex hAx he hA hnb hxc
        (.inl (by simp [D.bc0, hs, hsx, hix]))) ?_
  rintro ⟨x', kx'⟩ a' ws' ⟨pcx', hx'⟩ hl hvis
  obtain ⟨-, dx', ex', hex', hAx', hsh', -⟩ := access_facts hpre hX ht (e := (x', kx'))
    (.inr (.inl ⟨ws', ⟨pcx', hx'⟩, rfl⟩))
  rw [hx'] at hex'
  cases Option.some.inj hex'
  have hov : a'.Overlap (wsAcc (y / 256) 0 P) :=
    ⟨a'.loc, ⟨rfl, rfl, le_rfl, by rw [hsh'.size]; omega⟩,
      by rw [hl]; exact ⟨rfl, rfl, le_rfl, by simp [wsAcc]⟩⟩
  obtain ⟨hc', hr', hw'⟩ := red_write hpre hX ht hx' hAx' (by rw [hl]; rfl)
    (by rw [hl]; simp [wsAcc])
  have hcta : x' / 256 = y / 256 := by rw [← hc', hl]; rfl
  have haddr : a'.loc.addr = P.S + 4 * 0 + 16384 := by rw [hl]; rfl
  have hxx : x' = x := by
    rcases hw' with ⟨-, h1, h2, -⟩ | ⟨-, h1, -, -⟩ <;> omega
  subst hxx
  rcases hw' with ⟨hs', -, -, hk'⟩ | ⟨hs', -, -, hk'⟩
  · rcases Nat.lt_or_ge dy.i dx'.i with hgt | hle
    · exact .inr (.inr (baseCausality_of_counts hpre hX ht he hA hx' hAx' hnr hcta.symm
        (.inr (by simp [D.bc1, hs, hs', hgt]))))
    · refine .inr
        (.inl (po_baseCausality (.inr (.inl ⟨_, ⟨pcx', hx'⟩, rfl⟩))
          (.inr (.inl ⟨_, ⟨pcx, hex⟩, rfl⟩)) ?_ hov))
      rw [hk']
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact rowBase_lt hlt (by unfold rowLen p1; omega)
      · rw [heq]; omega
  · rcases Nat.lt_trichotomy dx'.i dy.i with hlt | heq | hgt
    · refine .inr
        (.inl (po_baseCausality (.inr (.inl ⟨_, ⟨pcx', hx'⟩, rfl⟩))
          (.inr (.inl ⟨_, ⟨pcx, hex⟩, rfl⟩)) ?_ hov))
      rw [hk']; exact rowBase_lt hlt (by unfold rowLen p1; omega)
    · left; rw [hk', heq]
    · exact .inr (.inr (baseCausality_of_counts hpre hX ht he hA hx' hAx' hnr hcta.symm
        (.inr (by simp [D.bc1, hs, hs', hgt]))))

/-- **The staged inputs a state reloaded**: the inputs of tile `t` of its row. -/
theorem lds_vals {g k t q : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) (hr : d.site.inRow = true) {h : Nat}
    (htq : (t = 0 ∧ h = 0 ∧ q = p1 g + 6) ∨ (t = 0 ∧ h = 1 ∧ q = p1 g + 10) ∨
      (t = 1 ∧ h = 0 ∧ q = p1 g + 22) ∨ (t = 1 ∧ h = 1 ∧ q = p1 g + 26))
    (hp : q + 3 ≤ d.pos g) :
    rv4 (X.tr g) (rowBase g d.i + q) = [fl (xin P g d.i t (4 * h)), fl (xin P g d.i t (4 * h + 1)),
      fl (xin P g d.i t (4 * h + 2)), fl (xin P g d.i t (4 * h + 3))] := by
  refine load_vals hpre hX ht he hA hr hp (fun j => fl (xin P g d.i t (4 * h + j))) ?_ ?_
  · intro j hj d' hi' hr' hp'
    rcases htq with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [(ldsa0_of_pos hi' hr' hj (by omega)).1]; rfl
    · rw [(ldsa1_of_pos hi' hr' hj (by omega)).1]; rfl
    · rw [(ldsb0_of_pos hi' hr' hj (by omega)).1]; rfl
    · rw [(ldsb1_of_pos hi' hr' hj (by omega)).1]; rfl
  · intro j hj k' d' pc a bs he' hA' hi' hp' hr'
    have hsub : d'.sub = j ∧ ((d'.site = .ldsa0 ∧ t = 0 ∧ h = 0) ∨
        (d'.site = .ldsa1 ∧ t = 0 ∧ h = 1) ∨
        (d'.site = .ldsb0 ∧ t = 1 ∧ h = 0) ∨ (d'.site = .ldsb1 ∧ t = 1 ∧ h = 1)) := by
      rcases htq with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := ldsa0_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inl ⟨h1, rfl, rfl⟩⟩
      · obtain ⟨h1, h2⟩ := ldsa1_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inr (.inl ⟨h1, rfl, rfl⟩)⟩
      · obtain ⟨h1, h2⟩ := ldsb0_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inr (.inr (.inl ⟨h1, rfl, rfl⟩))⟩
      · obtain ⟨h1, h2⟩ := ldsb1_of_pos hA'.inv hr' hj (by omega)
        exact ⟨h2, .inr (.inr (.inr ⟨h1, rfl, rfl⟩))⟩
    rw [lds_bytes hpre hX ht he' hA' hsub.2, rdv_fl, hsub.1, hi']

/-- **A state at a tile's output stores holds its raw values**: the weight words and the
staged inputs of tile `t` of its row. -/
theorem tile_data {g k t : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hA : At P L X g k d e) (hr : d.site.inRow = true)
    (ht' : (t = 0 ∧ p1 g + 14 ≤ d.pos g ∧ d.pos g < p1 g + 18) ∨ (t = 1 ∧ p1 g + 30 ≤ d.pos g)) :
    d.raw = hwords (win P g t) ∧ d.rs0 = fwords (xin P g d.i t) 0 ∧
      d.rs1 = fwords (xin P g d.i t) 4 := by
  have hk : k = rowBase g d.i + d.pos g := hA.index.trans (idx_of_row hr)
  rcases ht' with ⟨rfl, hp, hq⟩ | ⟨rfl, hp⟩
  · have h1 := wwords_eq hpre hX ht he hA hr (t := 0) (.inl ⟨rfl, rfl⟩) (by omega)
    have h2 := lds_vals hpre hX ht he hA hr (t := 0) (h := 0) (.inl ⟨rfl, rfl, rfl⟩) (by omega)
    have h3 := lds_vals hpre hX ht he hA hr (t := 0) (h := 1) (.inr (.inl ⟨rfl, rfl, rfl⟩))
      (by omega)
    simp only [← Nat.add_assoc] at h1 h2 h3
    rw [hA.data.rawa hr (by omega) hq, hA.data.rs0a hr (by omega) (by omega),
      hA.data.rs1a hr hp hq, rv4_take _ (by omega), rv4_take _ (by omega),
      rv4_take _ (by omega), h1, h2, h3]
    exact ⟨rfl, rfl, rfl⟩
  · have h1 := wwords_eq hpre hX ht he hA hr (t := 1) (.inr ⟨rfl, rfl⟩) (by omega)
    have h2 := lds_vals hpre hX ht he hA hr (t := 1) (h := 0) (.inr (.inr (.inl ⟨rfl, rfl, rfl⟩)))
      (by omega)
    have h3 := lds_vals hpre hX ht he hA hr (t := 1) (h := 1) (.inr (.inr (.inr ⟨rfl, rfl, rfl⟩)))
      (by omega)
    simp only [← Nat.add_assoc] at h1 h2 h3
    rw [hA.data.rawb hr (by omega), hA.data.rs0b hr (by omega), hA.data.rs1b hr hp,
      rv4_take _ (by omega), rv4_take _ (by omega), rv4_take _ (by omega), h1, h2, h3]
    exact ⟨rfl, rfl, rfl⟩

end
end PTX.Kernels.RmsNorm.Proof
