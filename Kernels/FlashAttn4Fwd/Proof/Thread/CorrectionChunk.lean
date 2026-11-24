-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionLoadValue

@[expose] public section

/-! # The products of a chunk

After the implicit wait of a load of sixteen words `o` into `base … base + 15`, every chunk of
the rescale and of the final normalization packs the pairs `(o[2k], o[2k+1])` into
`P + 7 - k` (`packsOf`), the rescale's first chunk also packs `α` twice into `P + 8`, and then
multiplies each packed pair by one pair `c` into `M + k` (`mulsOf`, `mul.rn.f32x2`).
`chunk_run`: when no pack or multiplication faults (`chunkOk`), local steps write each `M + k`
with the outcome `prodV o c k` and keep every other register but the pack destinations;
otherwise the thread is dead. The rescale then unpacks each product into two registers
(`unpacksOf`, `rchunk_run`); the final normalization unpacks each product and converts it to a
pair of halves (`ucvtsOf`, `fchunk_run`), and is dead where a conversion faults (`finOk`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The packs of a chunk: pair `7 - k` of the loaded words into `P + k`. -/
def packsOf (P base : Nat) : List (Nat × Nat × Nat) :=
  (List.range 8).map fun k => (P + k, base + 14 - 2 * k, base + 15 - 2 * k)

/-- The multiplications of a chunk: the pair packed in `P + 7 - k` into `M + k`. -/
def mulsOf (M P : Nat) : List (Nat × Nat) :=
  (List.range 8).map fun k => (M + k, P + 7 - k)

/-- The unpacks of the rescale: product `7 - k` into `U + 2k` and `U + 2k + 1`. -/
def unpacksOf (M U : Nat) : List (Nat × Nat × Nat) :=
  (List.range 8).map fun k => (M + 7 - k, U + 2 * k, U + 2 * k + 1)

/-- The unpacks and conversions of the final normalization: product `7 - k` into `V + 3k` and
`V + 3k + 1`, converted into `V + 3k + 2`. -/
def ucvtsOf (M V : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range 8).map fun k => (M + 7 - k, V + 3 * k, V + 3 * k + 1, V + 3 * k + 2)

/-- The registers the rescale chunk writes. -/
def rchunkW (P base : Nat) (ex : List (Nat × Nat × Nat)) (M U : Nat) : List Nat :=
  (packsOf P base ++ ex).map Prod.fst ++ (mulsOf M P).map Prod.fst ++
    (unpacksOf M U).flatMap fun u => [u.2.1, u.2.2]

/-- The registers the final chunk writes. -/
def fchunkW (P base M V : Nat) : List Nat :=
  (packsOf P base).map Prod.fst ++ (mulsOf M P).map Prod.fst ++
    (ucvtsOf M V).flatMap fun u => [u.2.1, u.2.2.1, u.2.2.2]

/-- The packs and multiplications of a chunk are accepted exactly when the chunk is. -/
theorem chunk_ok_iff {P base M : Nat} {o : List Value} {vc : Value} {v v1 : Nat → Value}
    (hv : ∀ i < 16, v (base + i) = o.getD i (b32 0))
    (hv1 : ∀ k < 8, v1 (P + 7 - k) = joinValue (o.getD (2 * k) (b32 0))
      (o.getD (2 * k + 1) (b32 0))) :
    (packsOk v (packsOf P base) = true ∧ mulsEOk .rn false v1 vc (mulsOf M P) = true) ↔
      chunkOk o vc = true := by
  have e := fun i (h : i < 16) => hv i h
  have e1 := fun k (h : k < 8) => hv1 k h
  simp only [packsOf, mulsOf, packsOk, mulsEOk, chunkOk, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq] at *
  simp only [show base + 14 - 2 * 0 = base + 14 by omega,
      show base + 15 - 2 * 0 = base + 15 by omega,
    show base + 14 - 2 * 1 = base + 12 by omega, show base + 15 - 2 * 1 = base + 13 by omega,
    show base + 14 - 2 * 2 = base + 10 by omega, show base + 15 - 2 * 2 = base + 11 by omega,
    show base + 14 - 2 * 3 = base + 8 by omega, show base + 15 - 2 * 3 = base + 9 by omega,
    show base + 14 - 2 * 4 = base + 6 by omega, show base + 15 - 2 * 4 = base + 7 by omega,
    show base + 14 - 2 * 5 = base + 4 by omega, show base + 15 - 2 * 5 = base + 5 by omega,
    show base + 14 - 2 * 6 = base + 2 by omega, show base + 15 - 2 * 6 = base + 3 by omega,
    show base + 14 - 2 * 7 = base + 0 by omega, show base + 15 - 2 * 7 = base + 1 by omega,
    e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    e 15 (by omega), e1 0 (by omega), e1 1 (by omega), e1 2 (by omega), e1 3 (by omega),
    e1 4 (by omega), e1 5 (by omega), e1 6 (by omega), e1 7 (by omega)]
  tauto

theorem mem_packsOf {P base k : Nat} (hk : k < 8) :
    (P + 7 - k, base + 2 * k, base + 2 * k + 1) ∈ packsOf P base := by
  refine List.mem_map.mpr ⟨7 - k, List.mem_range.mpr (by omega), ?_⟩
  simp only [Prod.mk.injEq]
  omega

theorem mem_mulsOf {M P k : Nat} (hk : k < 8) : (M + k, P + 7 - k) ∈ mulsOf M P :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem packsOf_length (P base : Nat) : (packsOf P base).length = 8 := rfl

theorem mulsOf_length (M P : Nat) : (mulsOf M P).length = 8 := rfl

/-- Every product is a pair of four-byte values. -/
theorem prodV_pair (o : List Value) (c : Value) (q : Nat) :
    ∃ x y, prodV o c q = .pair x y ∧ x.bytes = 4 ∧ y.bytes = 4 :=
  okVal_pair (floatE_mul2_pair4 .rn false _)

variable {L : Launch}

/-- **The packs and multiplications of a chunk** (and the extra packs `ex` after the chunk's
packs, `α` twice in the rescale's first chunk): the products `prodV` when no step faults, else
a dead thread. -/
theorem chunk_run {g P base M c : Nat} {ex : List (Nat × Nat × Nat)} {t : TState} {o : List Value}
    {vc : Value} (hpk : PackCode kernel t.pc (packsOf P base ++ ex))
    (hml : MulCodeE kernel .rn false c (t.pc + (8 + ex.length)) (mulsOf M P)) (hf : t.fault = none)
    (hpc : 3700 ≤ t.pc) (hv : ∀ i < 16, t.regs (base + i) = some (o.getD i (b32 0)))
    (hex : ∀ p ∈ ex, ∃ x, t.regs p.2.1 = some x ∧ t.regs p.2.2 = some x ∧ x.bytes = 4)
    (hfr : ∀ p ∈ packsOf P base ++ ex, ∀ q ∈ packsOf P base ++ ex, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2)
    (hnd : ((packsOf P base ++ ex).map Prod.fst).Nodup) (hndm : ((mulsOf M P).map Prod.fst).Nodup)
    (hfm : ∀ m ∈ mulsOf M P, m.1 ≠ c ∧ ∀ m' ∈ mulsOf M P, m.1 ≠ m'.2)
    (hc : (packRun (fun r => (t.regs r).getD (b32 0)) t (packsOf P base ++ ex)).regs c = some vc) :
    (chunkOk o vc = true → ∃ t', run kernel asms L g (8 + ex.length + 8) t = some t' ∧
        t'.pc = t.pc + (8 + ex.length + 8) ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧
        t'.fault = none ∧
        (∀ k < 8, t'.regs (M + k) = some (prodV o vc k)) ∧
        t'.regs c = some vc ∧
        ∀ r, (∀ p ∈ packsOf P base ++ ex, p.1 ≠ r) → (∀ m ∈ mulsOf M P, m.1 ≠ r) →
          t'.regs r = t.regs r) ∧
    (chunkOk o vc = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  set v : Nat → Value := fun r => (t.regs r).getD (b32 0)
  set ps := packsOf P base ++ ex
  have hlen : ps.length = 8 + ex.length := by simp [ps, packsOf_length]
  have hvo : ∀ i < 16, v (base + i) = o.getD i (b32 0) := fun i hi => by simp [v, hv i hi]
  have hsrc : ∀ p ∈ ps, t.regs p.2.1 = some (v p.2.1) ∧ t.regs p.2.2 = some (v p.2.2) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      have hk := List.mem_range.mp hk
      have hreg : ∀ r x, t.regs r = some x → t.regs r = some (v r) := fun r x h => by
        simp [v, h]
      exact ⟨hreg _ _ (by rw [show base + 14 - 2 * k = base + (14 - 2 * k) by omega,
          hv _ (by omega)]),
        hreg _ _ (by rw [show base + 15 - 2 * k = base + (15 - 2 * k) by omega,
          hv _ (by omega)])⟩
    · obtain ⟨x, h1, h2, -⟩ := hex p hp
      exact ⟨by simp [v, h1], by simp [v, h2]⟩
  have hP := packs_run (K := kernel) (A := asms) (L := L) (g := g)
    (fun _ _ _ _ _ _ => asms_localRule_none) v ps t hpk hf hsrc hfr
    (fun i _ => segFree (by omega))
  set t1 := packRun v t ps
  obtain ⟨h1pc, h1sub, h1acc, h1f⟩ := packRun_skel v ps t
  set v1 : Nat → Value := fun r => (t1.regs r).getD (b32 0)
  have hj : ∀ k < 8, t1.regs (P + 7 - k) =
      some (joinValue (o.getD (2 * k) (b32 0)) (o.getD (2 * k + 1) (b32 0))) := by
    intro k hk
    rw [packRun_val v ps t hnd (List.mem_append_left _ (mem_packsOf hk)), hvo _ (by omega),
      Nat.add_assoc, hvo _ (by omega)]
  have hv1 : ∀ k < 8, v1 (P + 7 - k) =
      joinValue (o.getD (2 * k) (b32 0)) (o.getD (2 * k + 1) (b32 0)) := fun k hk => by
    simp [v1, hj k hk]
  have hmsrc : ∀ m ∈ mulsOf M P, t1.regs m.2 = some (v1 m.2) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
    simp [v1, hj k (List.mem_range.mp hk)]
  have hM := mulsE_run (K := kernel) (A := asms) (L := L) (g := g) (rnd := .rn) (fz := false)
    v1 (mulsOf M P) t1 (by rw [h1pc, hlen]; exact hml) (h1f.trans hf) hc hmsrc hfm
    (fun i hi s hs => by
      have h37 : 3700 ≤ s.pc := by rw [hs, h1pc]; omega
      exact ⟨idealAt (.inl rfl) h37, declineAt h37⟩)
  have hexok : packsOk v ex = true := by
    simp only [packsOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
    intro p hp
    obtain ⟨x, h1, h2, hb⟩ := hex p hp
    simp [v, h1, h2, hb]
  have hiff := chunk_ok_iff (M := M) (vc := vc) hvo hv1
  have hpsok : packsOk v ps = packsOk v (packsOf P base) := by
    simp [ps, packsOk, List.all_append] at hexok ⊢
    exact fun _ => hexok
  constructor
  · intro hok
    obtain ⟨hp1, hm1⟩ := hiff.mpr hok
    refine ⟨mulRunE .rn false v1 vc t1 (mulsOf M P), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 8 + ex.length + 8 = ps.length + (mulsOf M P).length by
        rw [hlen, mulsOf_length]]
      exact run_comp (hP.1 (hpsok ▸ hp1)) (hM.1 hm1)
    · rw [(mulRunE_skel .rn false v1 vc _ t1).1, h1pc, hlen, mulsOf_length]
      omega
    · exact (mulRunE_skel .rn false v1 vc _ t1).2.1.trans h1sub
    · exact (mulRunE_skel .rn false v1 vc _ t1).2.2.1.trans h1acc
    · exact (mulRunE_skel .rn false v1 vc _ t1).2.2.2.trans (h1f.trans hf)
    · intro k hk
      rw [mulRunE_val .rn false v1 vc _ t1 hndm (mem_mulsOf hk), hv1 k hk]
      rfl
    · rw [mulRunE_other .rn false v1 vc _ t1 (fun m hm => (hfm m hm).1)]
      exact hc
    · intro r hp hm
      rw [mulRunE_other .rn false v1 vc _ t1 hm, packRun_other v ps t hp]
  · intro hbad
    by_cases hp1 : packsOk v ps = true
    · have hm1 : mulsEOk .rn false v1 vc (mulsOf M P) = false := by
        by_contra hc'
        have := hiff.mp ⟨hpsok ▸ hp1, by simpa using hc'⟩
        rw [hbad] at this
        cases this
      exact dead_of_run (hP.1 hp1) (hM.2 hm1)
    · exact hP.2 (by simpa using hp1)

/-- Facts by a table over a list hold over a sublist. -/
theorem holds_sub {R : Nat → Option Value} {big small : List Nat} {w : Nat → Value}
    (h : Holds R (Flow.factsFrom big w)) (hs : ∀ r ∈ small, r ∈ big) :
    Holds R (Flow.factsFrom small w) :=
  holds_of_pointwise fun r hr => holds_mem h (mem_factsFrom (hs r hr))

/-- **A rescale chunk**: its packs and multiplications (`chunk_run`), then the unpacks of the
products; the destinations of the unpacks and `c` hold the values a table `w` gives them. -/
theorem rchunk_run {g P base M c U : Nat} {ex : List (Nat × Nat × Nat)} {t : TState}
    {o : List Value} {vc : Value} {w : Nat → Value}
    (hpk : PackCode kernel t.pc (packsOf P base ++ ex))
    (hml : MulCodeE kernel .rn false c (t.pc + (8 + ex.length)) (mulsOf M P))
    (hup : UnpackCode kernel (t.pc + (8 + ex.length + 8)) (unpacksOf M U)) (hf : t.fault = none)
    (hpc : 3700 ≤ t.pc) (hv : ∀ i < 16, t.regs (base + i) = some (o.getD i (b32 0)))
    (hex : ∀ p ∈ ex, ∃ x, t.regs p.2.1 = some x ∧ t.regs p.2.2 = some x ∧ x.bytes = 4)
    (hfr : ∀ p ∈ packsOf P base ++ ex, ∀ q ∈ packsOf P base ++ ex, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2)
    (hnd : ((packsOf P base ++ ex).map Prod.fst).Nodup) (hndm : ((mulsOf M P).map Prod.fst).Nodup)
    (hfm : ∀ m ∈ mulsOf M P, m.1 ≠ c ∧ ∀ m' ∈ mulsOf M P, m.1 ≠ m'.2)
    (hc : (packRun (fun r => (t.regs r).getD (b32 0)) t (packsOf P base ++ ex)).regs c = some vc)
    (hud : ∀ u ∈ unpacksOf M U, ∀ u' ∈ unpacksOf M U, u'.2.1 ≠ u.1 ∧ u'.2.2 ≠ u.1)
    (hudc : ∀ u ∈ unpacksOf M U, u.2.1 ≠ c ∧ u.2.2 ≠ c)
    (hund : ((unpacksOf M U).flatMap fun u => [u.2.1, u.2.2]).Nodup)
    (hw : ∀ k < 8, w (U + 2 * k) = (splitValue 64 (prodV o vc (7 - k))).1 ∧
      w (U + 2 * k + 1) = (splitValue 64 (prodV o vc (7 - k))).2) (hwc : w c = vc) :
    (chunkOk o vc = true → ∃ t', run kernel asms L g (8 + ex.length + 8 + 8) t = some t' ∧
        t'.pc = t.pc + (8 + ex.length + 8 + 8) ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧
        t'.fault = none ∧
        Holds t'.regs (Flow.factsFrom
          (c :: (unpacksOf M U).flatMap fun u => [u.2.1, u.2.2]) w) ∧
        ∀ r, r ∉ rchunkW P base ex M U → t'.regs r = t.regs r) ∧
    (chunkOk o vc = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  obtain ⟨hok, hdead⟩ := chunk_run (L := L) (g := g) hpk hml hf hpc hv hex hfr hnd hndm hfm hc
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t1, hr1, h1pc, h1sub, h1acc, h1f, hM, hc1, hoth⟩ := hok hok'
  set v2 : Nat → Value := fun r => (t1.regs r).getD (b32 0)
  have hmem : ∀ u ∈ unpacksOf M U, ∃ k < 8, u = (M + 7 - k, U + 2 * k, U + 2 * k + 1) := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  have hsrc : ∀ k < 8, t1.regs (M + 7 - k) = some (prodV o vc (7 - k)) := fun k hk => by
    rw [show M + 7 - k = M + (7 - k) by omega]; exact hM _ (by omega)
  have hun := unpacks_run (K := kernel) (A := asms) (L := L) (g := g)
    (fun _ _ _ _ => asms_localRule_none) v2 (unpacksOf M U) t1
    (by rw [h1pc]; exact hup) h1f
    (fun u hu => by
      obtain ⟨k, hk, rfl⟩ := hmem u hu
      simp [v2, hsrc k hk])
    (fun u hu => by
      obtain ⟨k, hk, rfl⟩ := hmem u hu
      simpa [v2, hsrc k hk] using prodV_pair o vc (7 - k))
    hud (fun i _ => segFree (by omega))
  obtain ⟨h2pc, h2sub, h2acc, h2f⟩ := unpackRun_skel v2 (unpacksOf M U) t1
  refine ⟨unpackRun v2 t1 (unpacksOf M U), run_comp hr1 hun, ?_, h2sub.trans h1sub,
    h2acc.trans h1acc, h2f.trans h1f, holds_of_pointwise fun r hr => ?_, fun r hr => ?_⟩
  · rw [h2pc, h1pc]; rfl
  · rcases List.mem_cons.mp hr with rfl | hr
    · rw [unpackRun_other v2 _ t1 hudc, hc1, hwc]
    · obtain ⟨u, hu, hr⟩ := List.mem_flatMap.mp hr
      have hval := unpackRun_val v2 (unpacksOf M U) t1 hund u hu
      obtain ⟨k, hk, rfl⟩ := hmem u hu
      have hv2 : v2 (M + 7 - k) = prodV o vc (7 - k) := by simp [v2, hsrc k hk]
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [hval.1, hv2, (hw k hk).1]
      · rw [List.mem_singleton.mp hr, hval.2, hv2, (hw k hk).2]
  · simp only [rchunkW, List.mem_append, List.mem_map, not_or, not_exists, not_and] at hr
    rw [unpackRun_other v2 _ t1 (fun u hu => ⟨fun h => hr.2 (by
      exact List.mem_flatMap.mpr ⟨u, hu, by simp [h]⟩), fun h => hr.2 (by
      exact List.mem_flatMap.mpr ⟨u, hu, by simp [h]⟩)⟩)]
    exact hoth r (fun p hp h => hr.1.1 p (List.mem_append.mp hp) h) (fun m hm h => hr.1.2 m hm h)

/-- **A final chunk**: its packs and multiplications (`chunk_run`), then the unpacks and the
conversions of the products to halves; the conversions' destinations hold the values a table
`w` gives them, and the thread is dead where a step faults (`finOk`). -/
theorem fchunk_run {g P base M c V : Nat} {t : TState} {o : List Value} {vc : Value}
    {w : Nat → Value} (hpk : PackCode kernel t.pc (packsOf P base ++ []))
    (hml : MulCodeE kernel .rn false c (t.pc + 8) (mulsOf M P))
    (hup : UnpackCvtCode kernel (t.pc + 16) (ucvtsOf M V)) (hf : t.fault = none) (hpc : 3700 ≤ t.pc)
    (hv : ∀ i < 16, t.regs (base + i) = some (o.getD i (b32 0)))
    (hfr : ∀ p ∈ packsOf P base ++ [], ∀ q ∈ packsOf P base ++ [], q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2)
    (hnd : ((packsOf P base ++ []).map Prod.fst).Nodup) (hndm : ((mulsOf M P).map Prod.fst).Nodup)
    (hfm : ∀ m ∈ mulsOf M P, m.1 ≠ c ∧ ∀ m' ∈ mulsOf M P, m.1 ≠ m'.2)
    (hc : (packRun (fun r => (t.regs r).getD (b32 0)) t (packsOf P base ++ [])).regs c = some vc)
    (hud : ∀ u ∈ ucvtsOf M V, ∀ u' ∈ ucvtsOf M V, u'.2.1 ≠ u.1 ∧ u'.2.2.1 ≠ u.1 ∧ u'.2.2.2 ≠ u.1)
    (hlh : ∀ u ∈ ucvtsOf M V, u.2.1 ≠ u.2.2.1)
    (hdd : ∀ u ∈ ucvtsOf M V, ∀ u' ∈ ucvtsOf M V, u' ≠ u →
      u'.2.1 ≠ u.2.2.2 ∧ u'.2.2.1 ≠ u.2.2.2 ∧ u'.2.2.2 ≠ u.2.2.2) (hund : (ucvtsOf M V).Nodup)
    (hw : ∀ k < 8, w (V + 3 * k + 2) = cvtOfPair (prodV o vc (7 - k))) :
    (finOk o vc = true → ∃ t', run kernel asms L g (8 + 8 + 16) t = some t' ∧
        t'.pc = t.pc + (8 + 8 + 16) ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧
        t'.fault = none ∧
        Holds t'.regs (Flow.factsFrom ((ucvtsOf M V).map fun u => u.2.2.2) w) ∧
        ∀ r, r ∉ fchunkW P base M V → t'.regs r = t.regs r) ∧
    (finOk o vc = false → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  obtain ⟨hok, hdead⟩ := chunk_run (L := L) (g := g) (ex := []) hpk hml hf hpc hv
    (fun p hp => by simp at hp) hfr hnd hndm hfm hc
  have hmem : ∀ u ∈ ucvtsOf M V, ∃ k < 8,
      u = (M + 7 - k, V + 3 * k, V + 3 * k + 1, V + 3 * k + 2) := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  by_cases hck : chunkOk o vc = true
  · obtain ⟨t1, hr1, h1pc, h1sub, h1acc, h1f, hM, -, hoth⟩ := hok hck
    set v2 : Nat → Value := fun r => (t1.regs r).getD (b32 0)
    have hsrc : ∀ k < 8, t1.regs (M + 7 - k) = some (prodV o vc (7 - k)) := fun k hk => by
      rw [show M + 7 - k = M + (7 - k) by omega]; exact hM _ (by omega)
    have hv2 : ∀ k < 8, v2 (M + 7 - k) = prodV o vc (7 - k) := fun k hk => by
      simp [v2, hsrc k hk]
    have hun := unpackCvts_run (K := kernel) (A := asms) (L := L) (g := g)
      (fun _ _ _ _ => asms_localRule_none) v2 (ucvtsOf M V) t1
      (by rw [h1pc]; exact hup) h1f
      (fun u hu => by
        obtain ⟨k, hk, rfl⟩ := hmem u hu
        simp [v2, hsrc k hk])
      (fun u hu => by
        obtain ⟨k, hk, rfl⟩ := hmem u hu
        simpa [hv2 k hk] using prodV_pair o vc (7 - k))
      hlh hud (fun i _ => segFree (by omega))
      (fun i _ s hs => by
        have h37 : 3700 ≤ s.pc := by rw [hs, h1pc]; omega
        exact ⟨idealAt (.inr (.inr rfl)) h37, declineAt h37⟩)
    have hcv : cvtsOk v2 (ucvtsOf M V) = finOk o vc := by
      have e := fun k (h : k < 8) => hv2 k h
      simp only [cvtsOk, finOk, hck, Bool.true_and, ucvtsOf, List.range_succ, List.range_zero,
        List.nil_append, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, List.map_append, List.all_append]
      simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
        e 5 (by omega), e 6 (by omega), e 7 (by omega)]
      simp only [Nat.reduceSub]
      cases (cvtPairE (splitValue 64 (prodV o vc 0)).2 (splitValue 64 (prodV o vc 0)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 1)).2 (splitValue 64 (prodV o vc 1)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 2)).2 (splitValue 64 (prodV o vc 2)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 3)).2 (splitValue 64 (prodV o vc 3)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 4)).2 (splitValue 64 (prodV o vc 4)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 5)).2 (splitValue 64 (prodV o vc 5)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 6)).2 (splitValue 64 (prodV o vc 6)).1).toBool <;>
      cases (cvtPairE (splitValue 64 (prodV o vc 7)).2 (splitValue 64 (prodV o vc 7)).1).toBool <;>
      rfl
    obtain ⟨h2pc, h2sub, h2acc, h2f⟩ := unpackCvtRun_skel v2 (ucvtsOf M V) t1
    refine ⟨fun hfo => ?_, fun hfo => dead_of_run hr1 (hun.2 (hcv.trans hfo))⟩
    refine ⟨unpackCvtRun v2 t1 (ucvtsOf M V), run_comp hr1 (hun.1 (hcv.trans hfo)), ?_,
      h2sub.trans h1sub, h2acc.trans h1acc, h2f.trans h1f,
      holds_of_pointwise fun r hr => ?_, fun r hr => ?_⟩
    · rw [h2pc, h1pc]; rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      rw [unpackCvtRun_val v2 _ t1 hdd hund u hu]
      obtain ⟨k, hk, rfl⟩ := hmem u hu
      rw [hv2 k hk, hw k hk]
    · simp only [fchunkW, List.mem_append, List.mem_map, not_or, not_exists, not_and] at hr
      rw [unpackCvtRun_other v2 _ t1 (fun u hu => ⟨fun h => hr.2 (by
        exact List.mem_flatMap.mpr ⟨u, hu, by simp [h]⟩), fun h => hr.2 (by
        exact List.mem_flatMap.mpr ⟨u, hu, by simp [h]⟩), fun h => hr.2 (by
        exact List.mem_flatMap.mpr ⟨u, hu, by simp [h]⟩)⟩)]
      exact hoth r (fun p hp h => hr.1.1 p (by simpa using hp) h) (fun m hm h => hr.1.2 m hm h)
  · have hf' : chunkOk o vc = false := by simpa using hck
    refine ⟨fun hfo => ?_, fun _ => hdead hf'⟩
    simp [finOk, hf'] at hfo

/-- The loaded registers at the wait of a load hold the chunk. -/
theorem rldW_reg {g : Nat} {d : D} {st : Fin 2} {j : Fin 8} {R : Nat → Option Value} {base : Nat}
    (hs : d.site = .rldW st j) (h : Holds R (facts L g d))
    (hb : rldRegs (8 * st.val + j.val) = List.range' base 16) :
    ∀ k < 16, R (base + k) = some (d.o.getD k (b32 0)) := by
  intro k hk
  have hm : base + k ∈ Flow.live d.site.pc ++ d.site.extra := by
    rw [hs]
    exact List.mem_append_right _
      (by simp only [Site.extra, hb, List.mem_range']; exact ⟨k, hk, by omega⟩)
  rw [holds_mem h (mem_factsFrom hm)]
  have := rld_value L g d ⟨8 * st.val + j.val, by omega⟩ k hk
  rw [hb] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_range', hk] using this

/-- The loaded registers at the wait of a final load hold the chunk. -/
theorem fldW_reg {g : Nat} {d : D} {st : Fin 2} {j : Fin 8} {R : Nat → Option Value} {base : Nat}
    (hs : d.site = .fldW st j) (h : Holds R (facts L g d))
    (hb : fldRegs (8 * st.val + j.val) = List.range' base 16) :
    ∀ k < 16, R (base + k) = some (d.o.getD k (b32 0)) := by
  intro k hk
  have hm : base + k ∈ Flow.live d.site.pc ++ d.site.extra := by
    rw [hs]
    exact List.mem_append_right _
      (by simp only [Site.extra, hb, List.mem_range']; exact ⟨k, hk, by omega⟩)
  rw [holds_mem h (mem_factsFrom hm)]
  have := fld_value L g d ⟨8 * st.val + j.val, by omega⟩ k hk
  rw [hb] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_range', hk] using this

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
