-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMachine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputGeometry

@[expose] public section

/-! # A lane writes each output element only once -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0StageUnique

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem rank_step_at {X : Execution} {g i : Nat} {d d' : Machine.ThreadD} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (ha : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hb : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some d')) :
    Bound.rank P L g d' + (if e.counts then 1 else 0) ≤ Bound.rank P L g d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he ha
  have hi : (Machine.code P L g).inv d := (Exists.choose_spec hf).1.2
  rw [Frame.stateAt_succ he, ha] at hb
  exact Bound.rank_step hpre hi hf hb

private theorem rank_le_at {X : Execution} {g i k : Nat} {d d' : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hk : k ≤ (X.tr g).length) (hik : i ≤ k)
    (ha : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hb : Frame.stateAt (Machine.code P L) X g k = some (some d')) :
    Bound.rank P L g d' ≤ Bound.rank P L g d := by
  induction k generalizing d' with
  | zero =>
    have hzero : i = 0 := by omega
    subst i
    rw [ha] at hb
    cases hb
    exact Nat.le_refl _
  | succ k ih =>
    by_cases heq : i = k + 1
    · subst i
      rw [ha] at hb
      cases hb
      exact Nat.le_refl _
    have hkl : k < (X.tr g).length := by omega
    have he : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hkl
    obtain ⟨p, hp⟩ := Frame.stateAt_live ht hg hb (Nat.le_succ _)
    have hs' := rank_step_at hpre hX hs he hp hb
    have hm := ih (Nat.le_of_lt hkl) (by omega) hp
    omega

private theorem rank_lt_of_counted_at {X : Execution} {g i k : Nat} {d d' : Machine.ThreadD}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hk : k ≤ (X.tr g).length) (hik : i < k) (he : X.get (g, i) = some e) (hc : e.counts = true)
    (ha : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hb : Frame.stateAt (Machine.code P L) X g k = some (some d')) :
    Bound.rank P L g d' < Bound.rank P L g d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨p, hp⟩ := Frame.stateAt_live ht hg hb (show i + 1 ≤ k by omega)
  have hstep := rank_step_at hpre hX hs he ha hp
  simp only [hc, ↓reduceIte] at hstep
  have hm := rank_le_at hpre hX hs ht hg hk (show i + 1 ≤ k by omega) hp hb
  omega

/-- A thread's writes of a given output tile, vector and element are the same event. -/
theorem sameElement {X : Execution} {g i k : Nat} {d d' : D} {j : Fin 4} {v : Fin 8} {e f : Event}
    {a a' : Acc} {bytes bytes' : List Byte} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, i) = some e)
    (hf : X.get (g, k) = some f) (hew : e.kind = .wr a bytes) (hfw : f.kind = .wr a' bytes')
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hd' : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d')))
    (hs1 : d.site = .oStage j v) (hs2 : d'.site = .oStage j v) (hsub : d.sub = d'.sub) :
    i = k := by
  have hg := Frame.lt_of_get hX he
  have tr := (hs.produces (hX.thr g hg))
  obtain ⟨_, _, ⟨_, hi⟩, _⟩ := tr.fired_at he hd
  obtain ⟨_, _, ⟨_, hk⟩, _⟩ := tr.fired_at hf hd'
  have hi' : Wg0.Inv P L g d := hi
  have hk' : Wg0.Inv P L g d' := hk
  have hb1 := hi'.epilogueLast (by rw [hs1]; rfl)
  have hb2 := hk'.epilogueLast (by rw [hs2]; rfl)
  have hblocks : d.block = d'.block := by omega
  have hr : Bound.rank P L g (.wg0 d) = Bound.rank P L g (.wg0 d') := by
    simp [Bound.rank, Bound.wg0Rank, Bound.wg0Block, hs1, hs2, hsub, hblocks]
  have hci : e.counts = true := by
    obtain ⟨_, _⟩ := e
    cases hew
    rfl
  have hck : f.counts = true := by
    obtain ⟨_, _⟩ := f
    cases hfw
    rfl
  rcases lt_trichotomy i k with h | h | h
  · have hx := rank_lt_of_counted_at hpre hX hs ht (PTX.len_of_get hf).le h he hci hd hd'
    omega
  · exact h
  · have hx := rank_lt_of_counted_at hpre hX hs ht (PTX.len_of_get he).le h hf hck hd' hd
    omega

private theorem fold_inverse (j : Fin 4) (w : Fin 2) :
    stageGroup (planeAdd j.val + 2 * w.val) = j.val ∧
    stageHalf (planeAdd j.val + 2 * w.val) = w.val := by
  fin_cases j <;> fin_cases w <;> decide

private theorem stage_addr {L : Launch} {g : Nat} {j : Fin 4} {v : Fin 8} {s pos : Nat}
    (hw : half L g < 2) (hs : s < 4) (hp : pos < 4) :
    let column := tmaX j.val (half L g) + (8 * v.val + 2 * s + pos / 2)
    stageOff (head L g) column + pos % 2 = stageWrite L g j.val v.val s + pos := by
  let x := 8 * v.val + 2 * s + pos / 2
  let c := tmaX j.val (half L g) + x
  let w : Fin 2 := ⟨half L g, hw⟩
  have hv := v.isLt
  have hx : x < 64 := by unfold x; omega
  have hc : c < 512 := Result.outputColumn_lt j hw hx
  have hplane : c / 64 = planeAdd j.val + 2 * w.val := by
    change c / 64 = planeAdd j.val + 2 * half L g
    unfold c tmaX
    omega
  have hgrp : stageGroup (c / 64) = j.val := by rw [hplane]; exact (fold_inverse j w).1
  have hhalf : half L g = stageHalf (c / 64) := by
    rw [hplane]
    exact (fold_inverse j w).2.symm
  have hl := stageOff_eq_stageWrite hc hhalf rfl
  have hk : c % 64 / 8 = v.val := by unfold c tmaX x; omega
  have hsub : c % 8 / 2 = s := by unfold c tmaX x; omega
  have hpos : 2 * (c % 8 % 2) + pos % 2 = pos := by
    unfold c tmaX x
    omega
  change stageOff (head L g) c + pos % 2 = _
  rw [hl, hgrp, hk, hsub, Nat.add_assoc, hpos]

private theorem byteAt {L : Launch} {g : Nat} {j : Fin 4} {v : Fin 8} {s : Nat} {a : Acc}
    {l : Loc} (hw : half L g < 2) (hs : s < 4)
    (ha : a.loc = shLoc L g (stageWrite L g j.val v.val s)) (hz : a.size = 4)
    (hc : a.Covers l) :
    let pos := l.addr - a.loc.addr
    pos < 4 ∧ l.addr = L.sharedBase +
      (stageOff (head L g) (tmaX j.val (half L g) + (8 * v.val + 2 * s + pos / 2)) +
        pos % 2) := by
  let pos := l.addr - a.loc.addr
  have hpos : pos < 4 := by
    obtain ⟨_, _, hlo, hhi⟩ := hc
    unfold pos
    omega
  have hoff := stage_addr (j := j) (v := v) hw hs hpos
  have hbase : a.loc.addr = L.sharedBase + stageWrite L g j.val v.val s :=
    congrArg Loc.addr ha
  refine ⟨hpos, ?_⟩
  change l.addr = L.sharedBase +
    (stageOff (head L g) (tmaX j.val (half L g) + (8 * v.val + 2 * s + pos / 2)) + pos % 2)
  rw [hoff, ← Nat.add_assoc, ← hbase]
  have hlow := hc.2.2.1
  unfold pos
  omega

/-- Two staging elements that cover one shared byte have the same writing lane and indices. -/
theorem sameFootprint {g g' s s' : Nat} {j j' : Fin 4} {v v' : Fin 8} {a a' : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hw : half L g < 2) (hw' : half L g' < 2) (hs : s < 4) (hs' : s' < 4)
    (ha : a.loc = shLoc L g (stageWrite L g j.val v.val s))
    (ha' : a'.loc = shLoc L g' (stageWrite L g' j'.val v'.val s')) (hz : a.size = 4)
    (hz' : a'.size = 4) (hc : a.Covers l) (hc' : a'.Covers l) :
    g = g' ∧ j = j' ∧ v = v' ∧ s = s' := by
  let pos := l.addr - a.loc.addr
  let pos' := l.addr - a'.loc.addr
  let c := tmaX j.val (half L g) + (8 * v.val + 2 * s + pos / 2)
  let c' := tmaX j'.val (half L g') + (8 * v'.val + 2 * s' + pos' / 2)
  obtain ⟨hpos, hloc⟩ := byteAt hw hs ha hz hc
  obtain ⟨hpos', hloc'⟩ := byteAt hw' hs' ha' hz' hc'
  have heq : stageOff (head L g) c + pos % 2 = stageOff (head L g') c' + pos' % 2 := by
    apply Nat.add_left_cancel (n := L.sharedBase)
    exact hloc.symm.trans hloc'
  obtain ⟨hhead, hcol, _⟩ := Result.stageByte_injective
    (by unfold head; omega) (by unfold head; omega) (by omega) (by omega) heq
  have hv := v.isLt
  have hv' := v'.isLt
  let x : Fin 64 := ⟨8 * v.val + 2 * s + pos / 2, by omega⟩
  let x' : Fin 64 := ⟨8 * v'.val + 2 * s' + pos' / 2, by omega⟩
  let w : Fin 2 := ⟨half L g, hw⟩
  let w' : Fin 2 := ⟨half L g', hw'⟩
  have hlogical : Result.outputColumn (j, w, x) = Result.outputColumn (j', w', x') :=
    Fin.ext hcol
  have heq := Result.outputColumn_bijective.1 hlogical
  have hj : j = j' := congrArg Prod.fst heq
  have hhalf : half L g = half L g' := congrArg (fun u => u.2.1.val) heq
  have hx : 8 * v.val + 2 * s + pos / 2 = 8 * v'.val + 2 * s' + pos' / 2 :=
    congrArg (fun u => u.2.2.val) heq
  have hcta : ctaOf L g = ctaOf L g' := by
    have h := hc.2.1.symm.trans hc'.2.1
    simpa only [ha, ha', shLoc] using h
  have hthread : g = g' := by
    simp only [ctaOf, Wg0.half, warpOf, head, tidOf_eq hpre, hpre.block] at hcta hhalf hhead
    omega
  exact ⟨hthread, hj, Fin.ext (by omega), by omega⟩

private theorem writeFootprint {X : Execution} {g i : Nat} {d : D} {j : Fin 4} {v : Fin 8}
    {e : Event} {a : Acc} {bytes : List Byte} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e) (hew : e.kind = .wr a bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oStage j v) :
    Wg0.half L g < 2 ∧ d.sub < 4 ∧
      a.loc = shLoc L g (stageWrite L g j.val v.val d.sub) ∧ a.size = 4 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  have hi : Wg0.Inv P L g d := (Exists.choose_spec hf).1.2
  have hw := hi.warpLt
  have hsub : d.sub < 4 := by simpa only [hsite, Site.elems] using hi.subLt
  have ho : ∃ u, o = some u := by
    obtain ⟨t, _, hf⟩ := hf
    generalize (Machine.machine P L g).tmpl (some (.wg0 d)) t = tm at hf
    cases tm <;> simp only [Fires] at hf <;> aesop
  obtain ⟨u, rfl⟩ := ho
  have hrole : (Wg0.code P L g).toMachine.Fired (some d) e (some u) := hf
  obtain ⟨a', hkind, hloc, hsize⟩ := Wg0.fired_stageOutput hpre hg hsite hrole
  rw [hew, Kind.wr.injEq] at hkind
  obtain ⟨rfl, _⟩ := hkind
  exact ⟨by unfold Wg0.half; omega, hsub, hloc, hsize⟩

/-- A byte of a staging write has the SW128 address of its indexed output value. -/
theorem writeByteAddress {X : Execution} {g i : Nat} {d : D} {j : Fin 4} {v : Fin 8} {a : Acc}
    {bytes : List Byte} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hw : X.Writes (g, i) a bytes)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oStage j v) (pos : Fin 4) :
    Wg0.half L g < 2 ∧ d.sub < 4 ∧
      a.loc.at pos.val = shLoc L g
        (stageOff (head L g) (tmaX j.val (Wg0.half L g) + (8 * v.val + 2 * d.sub + pos.val / 2)) +
          pos.val % 2) := by
  obtain ⟨tag, he⟩ := hw
  obtain ⟨hhalf, hsub, ha, _⟩ := writeFootprint hpre hX hs he rfl hd hsite
  refine ⟨hhalf, hsub, ?_⟩
  rw [ha, stage_addr (j := j) (v := v) hhalf hsub pos.isLt]
  simp only [Loc.at, shLoc, Nat.add_assoc]

/-- Each shared byte is written by at most one staging event in the execution. -/
theorem sameByte {X : Execution} {g g' i k : Nat} {d d' : D} {j j' : Fin 4} {v v' : Fin 8}
    {e f : Event} {a a' : Acc} {bytes bytes' : List Byte} {l : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (g', k) = some f) (hew : e.kind = .wr a bytes)
    (hfw : f.kind = .wr a' bytes')
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hd' : Frame.stateAt (Machine.code P L) X g' k = some (some (.wg0 d')))
    (hsite : d.site = .oStage j v) (hsite' : d'.site = .oStage j' v') (hc : a.Covers l)
    (hc' : a'.Covers l) :
    (g, i) = (g', k) := by
  have hs1 := hs g (Frame.lt_of_get hX he)
  have hs2 := hs g' (Frame.lt_of_get hX hf)
  obtain ⟨hw, hsub, ha, hz⟩ := writeFootprint hpre hX hs1 he hew hd hsite
  obtain ⟨hw', hsub', ha', hz'⟩ := writeFootprint hpre hX hs2 hf hfw hd' hsite'
  obtain ⟨rfl, rfl, rfl, hsubEq⟩ :=
    sameFootprint hpre hw hw' hsub hsub' ha ha' hz hz' hc hc'
  have hi := sameElement hpre hX hs1 ht he hf hew hfw hd hd' hsite hsite' hsubEq
  rw [hi]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0StageUnique
