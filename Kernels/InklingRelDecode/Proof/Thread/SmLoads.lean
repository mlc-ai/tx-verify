-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSegB
public import Lemmas.Flow.Machine
public import Lemmas.Flow.Async
public import Lemmas.Flow.Code

@[expose] public section

/-! # The bias loads of the softmax region

The region's 64 preloads (pcs 680, 682, …, 806) and 64 loop bias loads (pcs 1124, …, 1250) are
guarded `ld.global.b16` instructions that alternate with `mov.u16 %rs, %rs18` (the zero fill of
the next destination). Both groups are handled by lemmas indexed by the position in the group:
that the instruction at the pc of index `j` is a load guarded by the group's mask
(`loadAt_pre`, `loadAt_nxt`) is decided on the code (`decide +kernel` over the index range), the
guard's fact is the state's mask, and the step of the load writes the destination of index `j`
(`valueOf_pre`, `valueOf_frame`: the table's lookup at a symbolic register).

`Cont` and `Step` state the obligation of one event of the machine. `step_pre` proves it for
the preload `j` with `j + 1 < 64`: the load's event, the zero fill of the next destination, and
the arrival at the next load. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event}

/-! ### The obligation of one event -/

/-- The continuation of a step: the machine stops following (`some none`), or steps to `d'` at
`t'` by a run of `Tau`. -/
def Cont (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
      Inv L g d'

/-- A step of the machine: the thread continues to the successor state, or the event faults (the
machine records an unreadable value as `none`). -/
def Step (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  Cont L g d e u ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-! ### The code of the two groups, decided -/

/-- The instruction at `pc` is a global load of one destination guarded by `@p`. -/
def loadAt (pc p dst : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (q, false), .mem a⟩ =>
    q == p && a.kind == .load && !a.nc && a.ext == .same && a.regs == [dst] &&
      !(Op.mem a).isLocal
  | _ => false

theorem loadAt_spec {pc p dst : Nat} (h : loadAt pc p dst = true) :
    ∃ a : MemAccess, kernel.code[pc]? = some ⟨some (p, false), .mem a⟩ ∧ a.kind = .load ∧
      a.nc = false ∧ a.ext = .same ∧ a.regs = [dst] ∧ (Op.mem a).isLocal = false := by
  unfold loadAt at h
  split at h
  · rename_i q a hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hq, hk⟩, hn⟩, he⟩, hr⟩, hl⟩ := h
    subst hq
    exact ⟨a, hc, hk, hn, he, hr, hl⟩
  · cases h

theorem loadAt_pre : ∀ j < 64, loadAt (680 + 2 * j) 85 (263 + j) = true := by decide +kernel
theorem loadAt_nxt : ∀ j < 64,
    loadAt (1124 + 2 * j) 92 (if j = 0 then 332 else 333 + j) = true := by decide +kernel
theorem live_pre : ∀ j < 64, 85 ∈ Flow.live (680 + 2 * j) := by decide +kernel
theorem live_nxt : ∀ j < 64, 92 ∈ Flow.live (1124 + 2 * j) := by decide +kernel

/-- The instruction at `pc` is `mov.u16 d, a`. -/
def movAt (pc d a : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m⟩ => m == ⟨.scalar, .int .u 16, [some d], [.reg a]⟩
  | _ => false

theorem movAt_spec {pc d a : Nat} (h : movAt pc d a = true) :
    kernel.code[pc]? = some ⟨none, .move ⟨.scalar, .int .u 16, [some d], [.reg a]⟩⟩ := by
  unfold movAt at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

theorem movAt_pre : ∀ j < 63, movAt (681 + 2 * j) (264 + j) 199 = true := by decide +kernel
theorem emu_pre : ∀ j < 63, Assumptions.emuSites.contains (681 + 2 * j) = false := by
  decide +kernel
theorem live_mov : ∀ j < 63, 199 ∈ Flow.live (681 + 2 * j) ∧
    ∀ r ∈ Flow.live (681 + 2 * j + 1), r = 264 + j ∨ r ∈ Flow.live (681 + 2 * j) := by
  decide +kernel
theorem live_after : ∀ j < 63, ∀ r ∈ Flow.live (680 + 2 * (j + 1)),
    r ∈ Flow.live (681 + 2 * j + 1) := by decide +kernel
theorem live_load : ∀ j < 64, ∀ r ∈ Flow.live (681 + 2 * j),
    r = 263 + j ∨ r ∈ Flow.live (680 + 2 * j) := by decide +kernel

/-- A bias word the machine follows is a half-word. -/
theorem isBf16_bytes {x : Value} (h : isBf16 x = true) : x.bytes = 2 := by
  cases x with
  | float f r => cases f <;> first | rfl | simp [isBf16] at h
  | _ => simp [isBf16] at h

/-- A bias word the machine follows is a `bf16` number. -/
theorem bfOk_of_isBf16 {x : Value} (h : isBf16 x = true) : BfOk x := by
  cases x with
  | float f r => cases f <;> first | exact Or.inl ⟨r, rfl⟩ | simp [isBf16] at h
  | _ => simp [isBf16] at h

theorem bfOk_z16 : BfOk z16 := Or.inr rfl

/-- A new bias word that is `BfOk` keeps every word `BfOk`. -/
theorem bfOk_setW {w : Nat → Value} (hw : ∀ k, BfOk (w k)) {j : Nat} {x : Value}
    (hx : BfOk x) : ∀ k, BfOk (setW w j x k) := by
  intro k
  by_cases hk : k = j
  · subst hk; simpa [setW] using hx
  · simpa [setW, Function.update_of_ne hk] using hw k

/-! ### The table at the bias words -/

theorem lookup_append' (l₁ l₂ : List (Nat × Value)) (r : Nat) :
    (l₁ ++ l₂).lookup r = (l₁.lookup r).or (l₂.lookup r) := by
  induction l₁ with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, List.lookup]
    cases r == k <;> simp [ih]

/-- A table of consecutive registers `a + k` holding `f k`, looked up. -/
theorem lookup_range_map (a : Nat) (f : Nat → Value) (n r : Nat) :
    ((List.range n).map (fun k => (a + k, f k))).lookup r =
      if a ≤ r ∧ r < a + n then some (f (r - a)) else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, lookup_append', ih]
    by_cases h1 : a ≤ r ∧ r < a + n
    · have h2 : a ≤ r ∧ r < a + (n + 1) := ⟨h1.1, by omega⟩
      simp [h1, h2]
    · by_cases h3 : r = a + n
      · subst h3
        simp
      · have h4 : ¬ (a ≤ r ∧ r < a + (n + 1)) := by omega
        have h5 : (r == a + n) = false := by simpa using h3
        simp [h1, h4, List.lookup, h5]

theorem lookup_none_of_not_mem (l : List (Nat × Value)) {r : Nat} (h : r ∉ l.map Prod.fst) :
    l.lookup r = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (r == k) = false := by simpa using h.1
    simp only [List.lookup, this]
    exact ih h.2

/-- The registers of the bias words: the destinations of the preloads, of the loop loads and the
packed words. -/
def WordKey (r : Nat) : Prop :=
  (263 ≤ r ∧ r < 327) ∨ (332 ≤ r ∧ r < 397) ∨ (1916 ≤ r ∧ r < 1948)

/-- The scalar, 64-bit, pair and pointer sections hold no register of the bias words. -/
theorem keys_off_words (d : D) {r : Nat} (hr : WordKey r) :
    r ∉ (valuesS L g d).map Prod.fst ∧ r ∉ (valuesP L g d).map Prod.fst ∧
      r ∉ (valuesQ L g d).map Prod.fst ∧ r ∉ (valuesR L g d).map Prod.fst := by
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · simp only [valuesS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    simp only [WordKey] at hr
    omega
  · simp only [valuesP, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    simp only [WordKey] at hr
    omega
  · simp only [valuesQ, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    simp only [WordKey] at hr
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega
  · simp only [valuesR, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    simp only [WordKey] at hr
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> omega

/-- The registers of the section that changes with the iteration (`valuesI`). -/
def IKey (r : Nat) : Prop :=
  (91 ≤ r ∧ r ≤ 95) ∨ (502 ≤ r ∧ r ≤ 505) ∨ r = 874 ∨ r = 875 ∨ r = 940 ∨ r = 941 ∨ r = 943 ∨
    r = 1676 ∨ r = 1709 ∨ r = 1912 ∨ r = 1913 ∨ r = 1993 ∨ r = 2446 ∨ r = 169 ∨ r = 1532 ∨
    r = 179 ∨ r = 180

theorem keys_I (d : D) : ∀ r ∈ (valuesI L g d).map Prod.fst, IKey r := by
  intro r hr
  simp only [valuesI, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  unfold IKey
  omega

/-- A register that is no register of `valuesI` is not looked up in it. -/
theorem notI (d : D) {r : Nat} (hr : ¬ IKey r) : r ∉ (valuesI L g d).map Prod.fst :=
  fun hm => hr (keys_I d r hm)

/-- The S-tile and P-store section holds no register of the bias words, the sums or the pairs. -/
theorem keys_off_X (d : D) {r : Nat}
    (hr : (263 ≤ r ∧ r < 327) ∨ (332 ≤ r ∧ r < 397) ∨ (1916 ≤ r ∧ r < 1948) ∨
      (812 ≤ r ∧ r < 874) ∨ (1962 ≤ r ∧ r < 1993)) :
    r ∉ (valuesX L g d).map Prod.fst := by
  intro hm
  simp only [valuesX, List.map_append, List.mem_append] at hm
  rcases hm with hm | hm | hm
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · simp only [valuesXt, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    omega
  · have := keys_Xs _ _ _ r hm
    omega

/-- The keys of the bias-word section are bias-word registers. -/
theorem keys_words (d : D) : ∀ r ∈ (valuesW d).map Prod.fst, WordKey r := by
  intro r hr
  simp only [valuesW, valuesWf, List.map_append, List.map_cons, List.map_map, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_range, Function.comp_apply] at hr
  simp only [WordKey]
  rcases hr with (⟨k, hk, rfl⟩ | (rfl | rfl | ⟨k, hk, rfl⟩)) | ⟨k, hk, rfl⟩ <;> omega

/-- A register that is no bias word has the same value in two states that agree on everything but
the bias words and the site. -/
theorem valueOf_frame {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf) {r : Nat} (hr : ¬ WordKey r)
    (hx : d'.stg = d.stg := by rfl) : valueOf L g d' r = valueOf L g d r := by
  obtain ⟨s, e, i, m, l, cw, cv, w, v, sv, pf, x⟩ := d
  obtain ⟨s', e', i', m', l', cw', cv', w', v', sv', pf', x'⟩ := d'
  simp only at h1 h2 h3 h4 h5 h6 hx
  subst h1 h2 h3 h4 h5 h6 hx
  have hw : ∀ x : D, (valuesW x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hr (keys_words _ r hm))
  simp only [valueOf, values, lookup_append', hw]
  rfl

/-- Destination `264 + k` of a preload at a state in which `c` words are loaded. -/
theorem valueOf_pre (d : D) {k : Nat} (hk : k < 64) :
    valueOf L g d (263 + k) = if k < d.cw then d.w k else z16 := by
  obtain ⟨hS, hP, hQ, hR⟩ := keys_off_words (L := L) (g := g) d (r := 263 + k)
    (Or.inl ⟨by omega, by omega⟩)
  have hX := keys_off_X (L := L) (g := g) d (r := 263 + k) (Or.inl ⟨by omega, by omega⟩)
  have hI := notI (L := L) (g := g) d (r := 263 + k) (by unfold IKey; omega)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS,
    lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ, lookup_none_of_not_mem _ hR,
    lookup_none_of_not_mem _ hX, Option.none_or, Option.or_none, valuesW, valuesWf,
    lookup_range_map]
  have h1 : 263 ≤ 263 + k ∧ 263 + k < 263 + 64 := by omega
  simp [h1]

/-! ### The guards -/

/-- The preload's mask register reads as the state's `act0`. -/
theorem valueOf_p85 (d : D) : valueOf L g d 85 = .pred (act0 d.e (g % L.block)) := by
  sm_vals

/-- **Every preload's guard holds**: the instruction is a load guarded by `%p85`, whose fact is
the state's mask, true by the invariant. -/
theorem site_ok_pre (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨a, hc, -, -, -, -, hl⟩ := loadAt_spec (loadAt_pre j.val j.isLt)
  have hpc : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  refine ⟨_, by rw [hpc]; exact hc, hl, ?_⟩
  show (85, Value.pred (!false)) ∈ factsAt L g d.site.pc d
  have hact := (hi.cwPre j hs).2
  have := Flow.mem_factsFrom (val := valueOf L g d) (live_pre j.val j.isLt)
  rw [valueOf_p85, hact] at this
  rw [hpc]
  exact this

/-- No preload site has a loop load's destination or a packed word live. -/
theorem live_no_nxt : ∀ j < 64, ∀ r ∈ Flow.live (680 + 2 * j),
    ¬ ((332 ≤ r ∧ r < 397) ∨ (1916 ≤ r ∧ r < 1948)) := by decide +kernel

/-- The state after preload `j` returns `x`. -/
def D.afterPre (d : D) (j : Nat) (x : Value) : D :=
  { d with site := if h : j + 1 < 64 then .pre ⟨j + 1, h⟩ else d.site, cw := j + 1,
           w := setW d.w j x }

/-- The facts at the zero fill after preload `j` (pc `681 + 2 j`): the loaded word is in its
destination, every other register is as before. -/
theorem holds_afterLoad {R : Nat → Option Value} (hi : Inv L g d) {j : Fin 64}
    (hs : d.site = .pre j) {x : Value}
    (hR : ∀ r ∈ Flow.live (680 + 2 * j.val), r ≠ 263 + j.val → R r = some (valueOf L g d r))
    (hx : R (263 + j.val) = some x) :
    Holds R (factsAt L g (681 + 2 * j.val) (d.afterPre j.val x)) := by
  have hcw := (hi.cwPre j hs).1
  refine Flow.holds_of_pointwise fun r hr => ?_
  by_cases hrj : r = 263 + j.val
  · subst hrj
    rw [valueOf_pre _ j.isLt]
    simpa [D.afterPre, setW] using hx
  rcases live_load j.val j.isLt r hr with h | hl
  · exact absurd h hrj
  have hR' := hR r hl hrj
  have hn := live_no_nxt j.val j.isLt r hl
  by_cases hw : 263 ≤ r ∧ r < 327
  · obtain ⟨k, rfl⟩ : ∃ k, r = 263 + k := ⟨r - 263, by omega⟩
    rw [valueOf_pre _ (by omega : k < 64)] at hR' ⊢
    have hkj : k ≠ j.val := fun h => hrj (by omega)
    simp only [D.afterPre, setW, hcw] at hR' ⊢
    by_cases hk : k < j.val
    · have hk1 : k < j.val + 1 := by omega
      simp only [hk, hk1, ↓reduceIte, Function.update_of_ne hkj] at hR' ⊢
      exact hR'
    · have hk1 : ¬ k < j.val + 1 := by omega
      simp only [hk, hk1, ↓reduceIte] at hR' ⊢
      exact hR'
  · have hr' : ¬ WordKey r := by
      intro h
      simp only [WordKey] at h
      omega
    rw [valueOf_frame (d := d) (d' := d.afterPre j.val x) rfl rfl rfl rfl rfl rfl hr']
    exact hR'

/-- The invariant after preload `j` (`j + 1 < 64`) returned a word. -/
theorem inv_afterPre (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j) (hj : j.val + 1 < 64)
    (x : Value) (hx : x.bytes = 2) (hxf : BfOk x) :
    Inv L g { d with site := .pre ⟨j.val + 1, hj⟩, cw := j.val + 1, w := setW d.w j.val x } := by
  obtain ⟨hcw, hact⟩ := hi.cwPre j hs
  obtain ⟨hi0, hcv, hm, hl⟩ := hi.loop.1 j hs
  refine ⟨hi.tid, hi.ok, hi.i, ?_, fun k hk => absurd hk (by simp), ?_, ?_, hi.vb,
    fun h => absurd h (by simp), fun h => absurd h (by simp [LateSite]),
    fun h => absurd h (by simp), hi.re, hi.lb, hi.four, hi.bw, bfOk_setW hi.wf hxf, hi.vf⟩
  · intro k hk
    have : (⟨j.val + 1, hj⟩ : Fin 64) = k := by injection hk
    subst this
    exact ⟨rfl, hact⟩
  · refine ⟨fun k hk => ⟨hi0, hcv, hm, hl⟩, fun hk => absurd hk (by simp)⟩
  · intro k
    by_cases hk : k = j.val
    · subst hk; simpa [setW] using hx
    · simpa [setW, Function.update_of_ne hk] using hi.wb k

/-- `mov.u16 %rs(265 + j), %rs18` (pc `681 + 2 j`), the zero fill of the next destination. -/
theorem seg_fill (d : D) {j : Nat} (hj : j < 63) (hcw : d.cw = j + 1) :
    Seg kernel asms L g 1 (681 + 2 * j) (factsAt L g (681 + 2 * j) d) (681 + 2 * j + 1)
      (factsAt L g (681 + 2 * j + 1) d) := by
  obtain ⟨hl0, hl1⟩ := live_mov j hj
  refine seg_one (r := 264 + j) (v := z16) (movAt_spec (movAt_pre j hj)) rfl ?_ ?_ hl1
  · intro t h
    have h0 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hl0)
    have e0 : valueOf L g d 199 = z16 := by sm_vals
    rw [e0] at h0
    exact exec_mov16 (segFree (by rw [h.1]; exact emu_pre j hj)) h0
  · rw [show 264 + j = 263 + (j + 1) by omega, valueOf_pre d (by omega : j + 1 < 64)]
    simp [hcw]

/-- **A preload** (`j + 1 < 64`): the load's event writes the destination of index `j`; the zero
fill of the next destination follows and the thread arrives at the next preload. -/
theorem step_pre (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j) (hj : j.val + 1 < 64)
    (h : At t d.site.pc (facts L g d)) {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨a, hca, hk, hnc, hext, hregs, -⟩ := loadAt_spec (loadAt_pre j.val j.isLt)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hca)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hv], Machine.dead_of_fault (f := f)
      (by simp [afterLoad, hv])⟩
  | ok x =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    by_cases hb : isBf16 x = true
    · have hxb := hb
      have hn : next L g d ⟨680 + 2 * j.val, .rd r bs⟩ = some (some
          { d with
            site := .pre ⟨j.val + 1, hj⟩
            cw := j.val + 1
            w := setW d.w j.val x }) := by
        simp [next, hs, hv, hb, hj]
      have hAt : At (have __src := setReg t (263 + j.val) x
          { pc := t.pc + 1, regs := __src.regs, cf := __src.cf, fault := __src.fault : TState })
          (681 + 2 * j.val)
          (factsAt L g (681 + 2 * j.val) (D.afterPre d j.val x)) := by
        refine ⟨by simp [h.1, hpc]; omega, rfl, rfl, h.2.2.2.1, ?_⟩
        refine holds_afterLoad hi hs (fun r hr hne => ?_) (by simp [setReg])
        have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
          (show r ∈ Flow.live d.site.pc by rw [hpc]; exact hr))
        simpa [setReg, Function.update_of_ne hne] using this
      have hseg := seg_fill (L := L) (g := g) (D.afterPre d j.val x) (j := j.val) (by omega)
        (by simp [D.afterPre])
      obtain ⟨t', hr', ht'⟩ := hseg.rtg hAt
      refine .inl (.inr ⟨_, t', hn, hr', ?_, inv_afterPre hi hs hj x (isBf16_bytes hb)
        (bfOk_of_isBf16 hb)⟩)
      have hpc' : (Site.pre ⟨j.val + 1, hj⟩).pc = 680 + 2 * (j.val + 1) := rfl
      refine ⟨by simp only [hpc', ht'.1]; omega, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ?_⟩
      refine Flow.holds_factsFrom_mono ht'.2.2.2.2 (fun r hr => ?_)
      exact live_after j.val (by omega) r hr
    · exact .inl (.inl (by simp [next, hs, hv, hb]))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
