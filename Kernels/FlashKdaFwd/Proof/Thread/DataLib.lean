-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MatrixStep
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.RunFrame
public import Lemmas.Flow.Step.Combinators
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # Generic pieces of the data path that the library does not have

Nothing in this file names the kernel; every lemma is a candidate for `Lemmas/Flow/`.

A site machine that keeps loaded data as opaque values has, after most events, a local run that
continues only under a condition on those values (each floating outcome is no fault) and kills
the thread otherwise. The library's step combinators take the successor as `Code.Lands` (an
unconditional segment), with a dead branch only for scalar loads and shuffles. Here:

* `across P d'`: the successor across such a run, `some (some d')` under `P` and `none` (the
  thread is dead) otherwise; `cont_across` discharges `Code.Cont` from a conditional piece
  (`SegD`), `cont_seg` from a segment, `cont_at` where the thread is already at the successor.
* `SegD.run_land` (from `SegD.cross`): a generated run (`Tools/out_gen.py`, stated on its own
  registers) between the facts of a value function `W` on a live list and the facts of
  `valueEx W G0` (`G0` the run's end facts) on the successor's live list: the run's start facts
  are among the start's, the registers it does not write are carried (`SegD.frame`), and the
  successor's values are the run's end values or the carried ones. Every side condition is a
  Boolean check on literal register lists, written so that the kernel evaluates it in one pass
  (`subAsc`, `frameW`).
* `holds_vec`, `holds_after`: the facts after an event that wrote the registers `ds` with `vs`
  (`vecFacts ds vs (factsFrom live W)`) are facts of the value function `valueEx W (ds.zip vs)`.
* Step combinators in continuation form (the caller receives the state after the event with its
  facts and owes `Code.Cont`): `step_load_x` (a scalar load with or without extension:
  `fires_load_any`, `loadedValue`), `step_store_x`, `step_matrix_x` (`mma.sync`, `movmatrix`),
  `step_ldmatrix_mx_x`, `step_stmatrix_wr_x`.
* `unpack_piece`: `mov.b<w> {lo, hi}, a` as a one-instruction piece checked against stated
  values (the run items of `Lemmas/Flow/OutRun.lean` write one register, or are the 64-bit
  unpack). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

/-! ### Value functions with explicit entries -/

theorem valueEx_nil (x : Nat → Value) : valueEx x [] = x := rfl

theorem lookup_of_mem : ∀ {E : List (Nat × Value)}, (E.map Prod.fst).Nodup →
    ∀ {q : Nat × Value}, q ∈ E → E.lookup q.1 = some q.2
  | [], _, _, hq => by cases hq
  | (r, v) :: E, hnd, q, hq => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hq with rfl | hm
    · simp
    · have hne : q.1 ≠ r := fun e => hnd.1 ⟨q, hm, e⟩
      have hb : (q.1 == r) = false := by simpa using hne
      simp only [List.lookup, hb]
      exact lookup_of_mem hnd.2 hm

theorem lookup_of_not_mem : ∀ {E : List (Nat × Value)} {r : Nat}, r ∉ E.map Prod.fst →
    E.lookup r = none
  | [], _, _ => rfl
  | (k, v) :: E, r, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hb : (r == k) = false := by simpa using h.1
    simp only [List.lookup, hb]
    exact lookup_of_not_mem h.2

/-- A listed register has its listed value. -/
theorem valueEx_of_mem {E : List (Nat × Value)} (hnd : (E.map Prod.fst).Nodup) {q : Nat × Value}
    (hq : q ∈ E) (x : Nat → Value) : valueEx x E q.1 = q.2 := by
  simp only [valueEx, lookup_of_mem hnd hq, Option.getD_some]

/-- An unlisted register keeps its value. -/
theorem valueEx_of_not_mem {E : List (Nat × Value)} {r : Nat} (h : r ∉ E.map Prod.fst)
    (x : Nat → Value) : valueEx x E r = x r := by
  simp only [valueEx, lookup_of_not_mem h, Option.getD_none]

/-- Explicit entries on disjoint registers commute. -/
theorem valueEx_comm {E C : List (Nat × Value)} (h : ∀ r ∈ E.map Prod.fst, r ∉ C.map Prod.fst)
    (x : Nat → Value) : valueEx (valueEx x E) C = valueEx (valueEx x C) E := by
  funext r
  by_cases hC : r ∈ C.map Prod.fst
  · have hE : r ∉ E.map Prod.fst := fun hE => h r hE hC
    rw [valueEx_of_not_mem hE]
    simp only [valueEx]
    obtain ⟨v, hv⟩ := lookup_of_mem_keys hC
    simp [hv]
  · rw [valueEx_of_not_mem hC]
    simp only [valueEx, lookup_of_not_mem hC, Option.getD_none]

theorem map_fst_factsFrom (live : List Nat) (V : Nat → Value) :
    (factsFrom live V).map Prod.fst = live := by
  simp [factsFrom, Function.comp_def]

/-- `keys ⊆ live` in one pass over `live`, for lists in the same (ascending) order: the checks
of this file compare live lists of about 200 registers, and the quadratic
`keys.all (live.contains ·)` costs the kernel 0.7 s where this costs 0.02 s. -/
def subAsc : List Nat → List Nat → Bool
  | keys, [] => keys.isEmpty
  | keys, b :: bs =>
    match keys with
    | [] => true
    | a :: as => bif Nat.beq a b then subAsc as bs else subAsc (a :: as) bs

theorem mem_of_subAsc : ∀ {live keys : List Nat}, subAsc keys live = true →
    ∀ r ∈ keys, r ∈ live
  | [], keys, h, r, hr => by
    cases keys with
    | nil => cases hr
    | cons a as => simp [subAsc] at h
  | b :: bs, [], _, r, hr => by cases hr
  | b :: bs, a :: as, h, r, hr => by
    simp only [subAsc] at h
    cases hab : Nat.beq a b with
    | true =>
      rw [hab] at h
      obtain rfl := Nat.eq_of_beq_eq_true hab
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_subAsc h r hr)
    | false =>
      rw [hab] at h
      exact List.mem_cons_of_mem _ (mem_of_subAsc h r hr)

/-- Facts of a value function on fewer registers. -/
theorem holds_sub {R : Nat → Option Value} {live keys : List Nat} {V : Nat → Value}
    (h : Holds R (factsFrom live V)) (hs : subAsc keys live = true) :
    Holds R (factsFrom keys V) :=
  holds_of_pointwise fun r hr => holds_mem h (mem_factsFrom (mem_of_subAsc hs r hr))

/-- `frameB` with each instruction's written registers computed once: the instructions are
local, no jump, and none writes a register of `rs`. (`frameB` asks, for each register of `rs`,
whether the instruction writes it, and so evaluates the instruction's writes once per register:
0.8 s in the kernel for 20 instructions and 176 registers, against 0.03 s here.) -/
def frameW (ins : List Instr) (rs : List Nat) : Bool :=
  ins.all fun i => i.op.isLocal && noJump i.op && (writesRegs i.op).all fun w => !rs.contains w

theorem frameB_of_frameW {ins : List Instr} {rs : List Nat} (h : frameW ins rs = true) :
    frameB ins rs = true := by
  unfold frameW at h
  unfold frameB
  refine List.all_eq_true.mpr fun i hi => ?_
  have hi' := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hi' ⊢
  refine ⟨hi'.1, fun r hr => ?_⟩
  cases hc : (writesRegs i.op).contains r with
  | false => rfl
  | true =>
    have := hi'.2 r (List.contains_iff_mem.mp hc)
    rw [List.contains_iff_mem.mpr hr] at this
    cases this

/-! ### The facts after an event -/

/-- **The facts after an event that wrote `ds` with `vs`**, register by register: a written
register has the value written (the first, if listed twice), another its fact. -/
theorem holds_vec {R : Nat → Option Value} {W : Nat → Value} :
    ∀ {ds : List Nat} {vs : List Value} {live : List Nat}, ds.length = vs.length →
      Holds R (vecFacts ds vs (factsFrom live W)) →
      ∀ r, r ∈ ds ∨ r ∈ live → R r = some (valueEx W (ds.zip vs) r)
  | [], _, live, _, h, r, hr => by
    rcases hr with hr | hr
    · cases hr
    · exact holds_mem h (mem_factsFrom hr)
  | d :: ds, [], _, hl, _, _, _ => by cases hl
  | d :: ds, v :: vs, live, hl, h, r, hr => by
    have h' : Holds R ((d, v) :: vecFacts ds vs (factsFrom (live.filter fun x => x != d) W)) := by
      rw [← dropReg_factsFrom]; exact h
    by_cases e : r = d
    · subst e
      simp only [List.zip_cons_cons, valueEx, List.lookup, beq_self_eq_true, Option.getD_some]
      exact h'.1
    · have hb : (r == d) = false := by simpa using e
      have hv : valueEx W ((d :: ds).zip (v :: vs)) r = valueEx W (ds.zip vs) r := by
        simp only [List.zip_cons_cons, valueEx, List.lookup, hb]
      rw [hv]
      refine holds_vec (by simpa using hl) h'.2 r ?_
      rcases hr with hr | hr
      · exact .inl ((List.mem_cons.mp hr).resolve_left e)
      · exact .inr (List.mem_filter.mpr ⟨hr, by simpa using e⟩)

/-- The facts after an event, as facts of the updated value function on registers the event
wrote or the state has. -/
theorem holds_vec_keys {R : Nat → Option Value} {W : Nat → Value} {ds : List Nat}
    {vs : List Value} {live keys : List Nat} (hl : ds.length = vs.length)
    (h : Holds R (vecFacts ds vs (factsFrom live W)))
    (hk : keys.all (fun r => ds.contains r || live.contains r) = true) :
    Holds R (factsFrom keys (valueEx W (ds.zip vs))) :=
  holds_of_pointwise fun r hr => holds_vec hl h r (by
    have := List.all_eq_true.mp hk r hr
    simpa [Bool.or_eq_true] using this)

/-! ### Across a local run -/

/-- **The successor across a local run that may kill the thread**: the state `d'` when the
run's condition `P` holds, the end of the thread (`none`) otherwise. Never `some none`. -/
def across {D : Type} (P : Prop) (d' : D) : Option (Option D) :=
  haveI := Classical.propDecidable P
  if P then some (some d') else none

theorem across_pos {D : Type} {P : Prop} {d' : D} (h : P) : across P d' = some (some d') := by
  simp [across, h]

theorem across_neg {D : Type} {P : Prop} {d' : D} (h : ¬ P) : across P d' = none := by
  simp [across, h]

theorem across_ne {D : Type} (P : Prop) (d' : D) : across P d' ≠ some none := by
  by_cases hP : P
  · rw [across_pos hP]; simp
  · rw [across_neg hP]; simp

theorem across_eq_some {D : Type} {P : Prop} {d' d'' : D} (h : across P d' = some (some d'')) :
    P ∧ d'' = d' := by
  by_cases hP : P
  · rw [across_pos hP] at h
    exact ⟨hP, by simpa using h.symm⟩
  · rw [across_neg hP] at h
    cases h

theorem across_eq_none {D : Type} {P : Prop} {d' : D} (h : across P d' = none) : ¬ P := by
  intro hP
  rw [across_pos hP] at h
  cases h

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A generated run between the facts after an event and a successor's facts.** The event
wrote `ds` with `vs` on a state with the facts `factsFrom liveS W`; `V := valueEx W (ds.zip vs)`
are the values after it. The run `hrun` goes from `F0` to `G0` on its own registers; `F0` is
facts of `V` (`hF0`, by `rfl`) on registers the event wrote or the state has (`hk0`). The
registers `keysH` are carried over the run, whose code does not write them (`hB`); they are
among those the event wrote or the state has (`hkH`). The successor's facts
`factsFrom liveT Vt` are covered by the run's end facts and the carried ones (`hkT`), where
`Vt` has the run's end values (`hG`) and `V`'s on the carried registers (`hc`). -/
theorem SegD.cross (hA : RulesFrame A) {n s b : Nat} {F0 G0 : List (Nat × Value)} {P : Prop}
    {ins : List Instr} {ds : List Nat} {vs : List Value} {liveS liveT keysH : List Nat}
    {W Vt : Nat → Value}
    (hrun : SegD K A L g n s F0 b G0 P)
    (hcode : (K.code.drop s).take n = ins) (hlen : ins.length = n)
    (hS : ∀ i < n, Assumption.SegFreePc A (s + i))
    (hdv : ds.length = vs.length)
    (hF0 : factsFrom (F0.map Prod.fst) (valueEx W (ds.zip vs)) = F0)
    (hk0 : (F0.map Prod.fst).all (fun r => ds.contains r || liveS.contains r) = true)
    (hB : frameB ins keysH = true)
    (hkH : keysH.all (fun r => ds.contains r || liveS.contains r) = true)
    (hG : ∀ q ∈ G0, Vt q.1 = q.2) (hc : ∀ r ∈ keysH, Vt r = valueEx W (ds.zip vs) r)
    (hkT : liveT.all (fun r => (G0.map Prod.fst).contains r || keysH.contains r) = true) :
    SegD K A L g n s (vecFacts ds vs (factsFrom liveS W)) b (factsFrom liveT Vt) P := by
  have hfr := SegD.frame (H := factsFrom keysH (valueEx W (ds.zip vs))) hA hrun hcode hlen
    (by rw [map_fst_factsFrom]; exact hB) hS
  refine (hfr.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_
  · refine (holds_append _ _ _).mpr ⟨?_, holds_vec_keys hdv hR hkH⟩
    rw [← hF0]
    exact holds_vec_keys hdv hR hk0
  · obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine holds_of_pointwise fun r hr => ?_
    have h := List.all_eq_true.mp hkT r hr
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
    rcases h with ⟨q, hq, rfl⟩ | hc'
    · rw [hG q hq]; exact holds_mem h1 hq
    · rw [hc r hc']; exact holds_mem h2 (mem_factsFrom hc')

/-- A piece without a run of its own registers: the facts after an event, restated as facts of
the updated value function on a live list they cover (for a successor reached by control code
only, or the checkpoint before it). -/
theorem holds_after {R : Nat → Option Value} {W Vt : Nat → Value} {ds : List Nat}
    {vs : List Value} {liveS liveT : List Nat} (hdv : ds.length = vs.length)
    (h : Holds R (vecFacts ds vs (factsFrom liveS W)))
    (hk : subAsc (liveT.filter fun r => !ds.contains r) liveS = true)
    (hV : ∀ r ∈ liveT, Vt r = valueEx W (ds.zip vs) r) : Holds R (factsFrom liveT Vt) := by
  refine holds_of_pointwise fun r hr => ?_
  rw [hV r hr]
  refine holds_vec hdv h r ?_
  by_cases hd : r ∈ ds
  · exact .inl hd
  · exact .inr (mem_of_subAsc hk r (List.mem_filter.mpr ⟨hr, by simpa using hd⟩))

variable {C : Code K A L g}

/-- **The step obligation across a conditional piece**: the thread is at `s` with facts `F`
after the event, the piece leads to the successor `d'` under `P` and kills the thread otherwise,
and the machine's transition is `across P d'`. -/
theorem cont_across {d d' : C.D} {e : Event} {u : TState} {s n : Nat}
    {F : List (Nat × Value)} {P : Prop} (hu : At u s F)
    (hseg : SegD K A L g n s F (C.pc d') (C.facts d') P)
    (hsub : C.sub d' = 0) (hacc : C.acc d' = []) (hinv : C.inv d')
    (hn : C.next d e = across P d') : C.Cont d e u := by
  by_cases hP : P
  · obtain ⟨t', hr, ht⟩ := (hseg u hu).1 hP
    exact .inl (.inr ⟨d', t', hn.trans (across_pos hP), run_rtg hr,
      ⟨⟨ht.1, ht.2.1.trans hsub.symm, ht.2.2.1.trans hacc.symm, ht.2.2.2.1, ht.2.2.2.2⟩, hinv⟩⟩)
  · exact .inr ⟨hn.trans (across_neg hP), (hseg u hu).2 hP⟩

/-- The step obligation across an unconditional segment. -/
theorem cont_seg {d d' : C.D} {e : Event} {u : TState} {s n : Nat}
    {F : List (Nat × Value)} (hu : At u s F)
    (hseg : Seg K A L g n s F (C.pc d') (C.facts d'))
    (hsub : C.sub d' = 0) (hacc : C.acc d' = []) (hinv : C.inv d')
    (hn : C.next d e = some (some d')) : C.Cont d e u := by
  obtain ⟨t', hr, ht⟩ := hseg u hu
  exact .inl (.inr ⟨d', t', hn, run_rtg hr,
    ⟨⟨ht.1, ht.2.1.trans hsub.symm, ht.2.2.1.trans hacc.symm, ht.2.2.2.1, ht.2.2.2.2⟩, hinv⟩⟩)

/-- The step obligation where the thread is already at the successor's site. -/
theorem cont_at {d d' : C.D} {e : Event} {u : TState}
    (hu : At u (C.pc d') (C.facts d')) (hsub : C.sub d' = 0) (hacc : C.acc d' = [])
    (hinv : C.inv d') (hn : C.next d e = some (some d')) : C.Cont d e u :=
  .inl (.inr ⟨d', u, hn, .refl,
    ⟨⟨hu.1, hu.2.1.trans hsub.symm, hu.2.2.1.trans hacc.symm, hu.2.2.2.1, hu.2.2.2.2⟩, hinv⟩⟩)

/-- **A generated run from the facts of a value function to the facts of the function with the
run's end values**, both on live lists: `SegD.cross` without an event, with the carried
registers computed (the target's live registers the run's end facts do not list). The side
conditions are Boolean checks on literal lists: the run's start registers are live at the start
(`hk0`), its end registers are distinct (`hnd`, decided), its code writes no carried register
(`hB`), and the carried registers are live at the start (`hkH`); `hk0` and `hkH` are one-pass
checks (`subAsc`), for which the lists are in ascending order, as the generators write them. -/
theorem SegD.run_land (hA : RulesFrame A) {n s b : Nat} {F0 G0 : List (Nat × Value)} {P : Prop}
    {ins : List Instr} {liveS liveT : List Nat} {W : Nat → Value}
    (hrun : SegD K A L g n s F0 b G0 P)
    (hcode : (K.code.drop s).take n = ins) (hlen : ins.length = n)
    (hS : ∀ i < n, Assumption.SegFreePc A (s + i))
    (hF0 : factsFrom (F0.map Prod.fst) W = F0)
    (hk0 : subAsc (F0.map Prod.fst) liveS = true)
    (hnd : decide (G0.map Prod.fst).Nodup = true)
    (hB : frameW ins (liveT.filter fun r => !(G0.map Prod.fst).contains r) = true)
    (hkH : subAsc (liveT.filter fun r => !(G0.map Prod.fst).contains r) liveS = true) :
    SegD K A L g n s (factsFrom liveS W) b (factsFrom liveT (valueEx W G0)) P := by
  refine SegD.cross (ds := []) (vs := []) (keysH := liveT.filter fun r =>
    !(G0.map Prod.fst).contains r) hA hrun hcode hlen hS rfl hF0 ?_ (frameB_of_frameW hB) ?_ ?_ ?_
    ?_
  · exact List.all_eq_true.mpr fun r hr => by simpa using mem_of_subAsc hk0 r hr
  · exact List.all_eq_true.mpr fun r hr => by simpa using mem_of_subAsc hkH r hr
  · exact fun q hq => valueEx_of_mem (of_decide_eq_true hnd) hq W
  · intro r hr
    have : r ∉ G0.map Prod.fst := by simpa using (List.mem_filter.mp hr).2
    rw [valueEx_of_not_mem this]
    rfl
  · refine List.all_eq_true.mpr fun r hr => ?_
    by_cases hG : r ∈ G0.map Prod.fst
    · exact Bool.or_eq_true_iff.mpr (.inl (List.contains_iff_mem.mpr hG))
    · have : r ∈ liveT.filter fun r => !(G0.map Prod.fst).contains r :=
        List.mem_filter.mpr ⟨hr, by simpa using hG⟩
      exact Bool.or_eq_true_iff.mpr (.inr (List.contains_iff_mem.mpr this))

/-! ### Scalar loads, with or without extension -/

/-- The value a scalar load of the bytes `bs` writes to its register: what the bytes rebuild to,
zero- or sign-extended when the register is wider than the element (then always an integer:
the bit pattern of what was read). -/
def loadedValue (a : MemAccess) (bs : List (Option Byte)) : Exec Value :=
  rebuild 3 bs >>= extendLoaded a.ext a.elem.width

theorem loadedValue_same {a : MemAccess} (he : a.ext = .same) (bs : List (Option Byte)) :
    loadedValue a bs = rebuild 3 bs := by
  unfold loadedValue
  rw [he]
  cases rebuild 3 bs <;> rfl

/-- After a load without `.nc` the thread is in `afterAccessLoad` for the bytes read, whatever
its extension (`fires_load` is the case without extension). -/
theorem fires_load_any {t u : TState} {a : MemAccess} {pc : Nat} {e : Event}
    (hk : a.kind = .load) (hnc : a.nc = false)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
  by_cases he : a.ext = .same
  · obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf he
    exact ⟨r, bs, rfl, by rw [he, afterAccessLoad_same]⟩
  · have hloc : a.locSpace? = none := by
      simp [MemAccess.locSpace?, he]
    have hnotAtomic : a.rule ≠ some .threadAtomic := by
      rw [MemAccess.rule, hk]
      repeat' split
      all_goals simp_all
    have hacc : Fires pc (accessTmpl A L g t a) e (some u) → ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧
        u = afterAccessLoad t a.ext a.elem.width a.regs bs := by
      intro hf
      rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
        ⟨r, k, hn, -⟩
      · rw [h] at hf
        exact absurd hf.2 (by simp)
      · rw [h] at hf
        obtain ⟨bs, -, rfl, hu⟩ := hf
        exact ⟨_, bs, rfl, Option.some.inj hu⟩
      · simp [hnc] at hn
    simp only [eventTmpl, memTmpl] at hf
    split at hf
    · rename_i hl _
      rw [hloc] at hl
      cases hl
    · rename_i hrule
      exact absurd hrule hnotAtomic
    · split at hf
      · exact hacc hf
      · exact absurd hf.2 (by simp)

/-- **A scalar load**, in continuation form: for bytes whose value is `v` (`loadedValue`) the
caller gets the state after the load with `v` at the destination and the other facts; bytes
without a value fault the thread, where the machine stops. -/
theorem step_load_x {d : C.D} {gd : Option (Nat × Bool)} {a : MemAccess} {r : Nat}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .load) (hnc : a.nc = false)
    (hregs : a.regs = [r]) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hok : ∀ x bs v, loadedValue a bs = .ok v → C.inv d →
      ∀ u, At u (C.pc d + 1) (vecFacts [r] [v] (C.facts d)) → C.Cont d ⟨C.pc d, .rd x bs⟩ u)
    (herr : ∀ x bs f, loadedValue a bs = .error f → C.next d ⟨C.pc d, .rd x bs⟩ = none) :
    C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load_any hk hnc hf
  rw [hregs]
  cases hv : loadedValue a bs with
  | error f =>
    refine .inr ⟨herr x bs f hv, Machine.dead_of_fault (f := f) ?_⟩
    have hv' : (rebuild 3 bs >>= extendLoaded a.ext a.elem.width) = .error f := hv
    simp only [afterAccessLoad, hv']
  | ok v =>
    have hv' : (rebuild 3 bs >>= extendLoaded a.ext a.elem.width) = .ok v := hv
    have hst : afterAccessLoad t a.ext a.elem.width [r] bs = PTX.next (setReg t r v) := by
      have hs0 := h0.2.1
      have ha0 := h0.2.2.1
      simp only [afterAccessLoad, hv']
      cases t
      simp_all [PTX.next, setReg, setRegs]
    rw [hst]
    have h1 : At t (C.pc d) (dropReg r (C.facts d)) := h0.mono (holds_dropReg r h0.2.2.2.2)
    have hr : ∀ q ∈ dropReg r (C.facts d), q.1 ≠ r := fun q hq => by
      simpa using (List.mem_filter.mp hq).2
    exact hok x bs v hv hi _ (At.set h1 hr)

/-! ### Stores -/

/-- **A scalar store (or the last element of a vector store)**, in continuation form. -/
theorem step_store_x {d : C.D} {gd : Option (Nat × Bool)} {a : MemAccess}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hk : a.kind = .store)
    (hsub : ¬ C.sub d + 1 < a.srcs.length) (ha : C.acc d = [])
    (hok : ∀ x bs, C.inv d → ∀ u, At u (C.pc d + 1) (C.facts d) →
      C.Cont d ⟨C.pc d, .wr x bs⟩ u) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨x, bs, rfl, rfl⟩ := fires_st hk hf
  rw [afterStore_last (by rw [h.2.1]; exact hsub)]
  exact hok x bs hi _ ⟨by simp [h.1], rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩

/-! ### Warp matrix instructions -/

/-- The common part of `step_matrix_x` and `step_ldmatrix_mx_x`: a matrix event that continues
as `afterMatrix t w ds`, in continuation form. Received bytes that do not rebuild fault the
thread, where the machine stops. -/
theorem step_afterMatrix_x {d : C.D} {ins0 : Instr} {op : MatrixOp} {w : Nat} {ds : List Nat}
    (hc0 : K.code[C.pc d]? = some ins0)
    (hfire : ∀ {t e u}, C.AtD d t → Fires (C.pc d) (eventTmpl A L g t ins0.op) e (some u) →
      ∃ own recv, e = ⟨C.pc d, .matrix op own recv⟩ ∧ u = afterMatrix t w ds recv)
    (hnd : ds.Nodup)
    (hok : ∀ own recv vs, matrixVals w ds.length recv = .ok vs → C.inv d →
      ∀ u, At u (C.pc d + 1) (vecFacts ds vs (C.facts d)) →
        C.Cont d ⟨C.pc d, .matrix op own recv⟩ u)
    (herr : ∀ own recv f, matrixVals w ds.length recv = .error f →
      C.next d ⟨C.pc d, .matrix op own recv⟩ = none) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨own, recv, rfl, rfl⟩ := hfire h hf
  cases hv : matrixVals w ds.length recv with
  | error f =>
    rw [afterMatrix_fault hv]
    exact .inr ⟨herr own recv f hv, Machine.dead_of_fault (f := f) rfl⟩
  | ok vs =>
    rw [afterMatrix_ok hv]
    exact hok own recv vs hv hi _ (at_afterMatrix h.1 h.2.2.2.1 h.2.2.2.2 hnd)

/-- **`mma.sync` and `movmatrix`** (one event), in continuation form: the caller gets the state
after the event with the rebuilt values `vs` at the destinations. -/
theorem step_matrix_x {d : C.D} {gd : Option (Nat × Bool)} {i : MatrixInstr} {w : Nat}
    (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : ∀ m, i.op ≠ .move m)
    (hw : matrixDstBits i.op = w) (hnd : i.dsts.Nodup)
    (hok : ∀ own recv vs, matrixVals w i.dsts.length recv = .ok vs → C.inv d →
      ∀ u, At u (C.pc d + 1) (vecFacts i.dsts vs (C.facts d)) →
        C.Cont d ⟨C.pc d, .matrix i.op own recv⟩ u)
    (herr : ∀ own recv f, matrixVals w i.dsts.length recv = .error f →
      C.next d ⟨C.pc d, .matrix i.op own recv⟩ = none) : C.StepOk d :=
  step_afterMatrix_x hc0 (fun _ hf => hw ▸ fires_matrix_recv hop hf) hnd hok herr

/-- **`ldmatrix`, second sub-step** (the matrix event), in continuation form. -/
theorem step_ldmatrix_mx_x {d : C.D} {gd : Option (Nat × Bool)} {i : MatrixInstr}
    {m : MatrixMove} (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = false) (hsub : C.sub d ≠ 0) (hnd : i.dsts.Nodup)
    (hok : ∀ own recv vs, matrixVals 32 i.dsts.length recv = .ok vs → C.inv d →
      ∀ u, At u (C.pc d + 1) (vecFacts i.dsts vs (C.facts d)) →
        C.Cont d ⟨C.pc d, .matrix (.move m) own recv⟩ u)
    (herr : ∀ own recv f, matrixVals 32 i.dsts.length recv = .error f →
      C.next d ⟨C.pc d, .matrix (.move m) own recv⟩ = none) : C.StepOk d :=
  step_afterMatrix_x hc0 (fun {t} _ _ h hf => by
    obtain ⟨recv, he, hu⟩ := fires_ldmatrix_mx hop hst
      (fun hc => hsub (h.2.1.symm.trans hc.2)) hf
    exact ⟨_, recv, he, hu⟩) hnd hok herr

/-- **`stmatrix`, second sub-step** (the row write), in continuation form. -/
theorem step_stmatrix_wr_x {d : C.D} {gd : Option (Nat × Bool)} {i : MatrixInstr}
    {m : MatrixMove} (hc0 : K.code[C.pc d]? = some ⟨gd, .matrix i⟩) (hop : i.op = .move m)
    (hst : m.store = true) (hsub : C.sub d ≠ 0)
    (hok : ∀ x bs, C.inv d → ∀ u, At u (C.pc d + 1) (C.facts d) →
      C.Cont d ⟨C.pc d, .wr x bs⟩ u) : C.StepOk d := by
  constructor
  intro t e u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain ⟨loc, -, rfl, rfl⟩ := fires_stmatrix_wr hop hst (fun hc => hsub (h.2.1.symm.trans hc)) hf
  exact hok _ _ hi _ ⟨by simp [PTX.next, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩

/-! ### An unpack as a piece -/

/-- **`mov.b<w> {lo, hi}, a` as a piece checked against stated values**: from the facts `F` to
the facts `G`, which are checked by evaluation as in `SegD.outs_lit`, when the value of `a`
unpacks; otherwise the thread is dead. -/
theorem unpack_piece (hM : CoreMoves A) (hS : Assumption.NoSegments A) {w pc lo hi a : Nat}
    {F G : List (Nat × Value)} (hw : w = 32 ∨ w = 64)
    (hc : K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b w, [some lo, some hi], [.reg a]⟩⟩)
    (ha : (F.map Prod.fst).contains a = true) (hne : (lo != hi) = true)
    (hcov : (G.map Prod.fst).all (fun r => r == lo || r == hi ||
      (F.map Prod.fst).contains r) = true)
    (hG : factsFrom (G.map Prod.fst) (valueEx (lookupD F)
      [(hi, (splitValue w (lookupD F a)).2), (lo, (splitValue w (lookupD F a)).1)]) = G) :
    SegD K A L g 1 pc F (pc + 1) G (∃ x, unpackE w (lookupD F a) = .ok x) := by
  intro t ht
  have hreg : ∀ r, r ∈ F.map Prod.fst → t.regs r = some (lookupD F r) := by
    intro r hr
    obtain ⟨v, hv⟩ := lookup_some hr
    rw [show lookupD F r = v by simp [lookupD, hv]]
    exact lookup_holds ht.2.2.2.2 hv
  have hra := hreg a (by simpa using ha)
  have he := exec_unpackE (L := L) (g := g) (lo := lo) (hi := hi) hM hS hw hra
  have hlh : lo ≠ hi := by simpa using hne
  refine ⟨fun ⟨x, hx⟩ => ?_, fun hno => ?_⟩
  · rw [hx] at he
    have hxs := unpackE_eq hx
    refine ⟨_, run_local hc rfl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, ?_⟩
    rw [← hG]
    refine holds_of_pointwise fun r hr => ?_
    have hcr := List.all_eq_true.mp hcov r hr
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcr
    by_cases e2 : r = hi
    · subst e2
      simp [PTX.next, setReg, valueEx, hxs]
    · by_cases e1 : r = lo
      · subst e1
        have hb : (r == hi) = false := by simpa using e2
        simp [PTX.next, setReg, valueEx, List.lookup, hb, Function.update_of_ne e2, hxs]
      · have hrF : r ∈ F.map Prod.fst := by
          rcases hcr with (h | h) | h
          · exact absurd h e1
          · exact absurd h e2
          · exact h
        have hb1 : (r == hi) = false := by simpa using e2
        have hb2 : (r == lo) = false := by simpa using e1
        simp only [PTX.next, setReg, Function.update_of_ne e2, Function.update_of_ne e1, valueEx,
          List.lookup, hb1, hb2, Option.getD_none]
        exact hreg r hrF
  · rcases hE : unpackE w (lookupD F a) with f | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) rfl ht.2.2.2.1 he
    · exact absurd ⟨x, hE⟩ hno

end
end PTX.Kernels.FlashKdaFwd.Proof.Thread
