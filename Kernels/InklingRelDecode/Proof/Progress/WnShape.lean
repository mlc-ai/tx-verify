-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Lk4WarpExit
public import Kernels.InklingRelDecode.Proof.Interface.WnAll
public import Lemmas.Flow.CommitTarget

@[expose] public section

/-!
# `WarpCollFacts.shape` from the lockstep of the lanes

The static part of a warp collective is a function of its position: the program names the lane
operands and member masks of its warp collectives by immediates, all masks full
(`Lk.wImm_of_code`), so the template at a warp-collective position is undefined behaviour or has
the static part `pcShape` of the position (`warpTmpl_shape`), and so has every event fired from it
(`event_shape`, `state_shape`).

The position of a lane's `n`-th warp collective is a function of its warp and `n`
(`wc_pc_eq`): two lanes of a warp at warp-collective states after equally many warp collectives
are at synchronizing states of one ordinal (a lane with a larger ordinal has a synchronizing state
of the other's ordinal, of the same key and so of the class, whose warp collective it made,
`Lk.lock_count`, `cnt_gt_of_ord`), so of one key (`Lk.lock_kernel`), so at one position. `wcPc`
chooses it, and `warpColl_shape` is `WarpCollFacts.shape` with
`F key n = (wcPc key n, pcShape (wcPc key n))`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
open PTX.Kernels.InklingRelDecode.Proof.Lk (tb wImm wImm_of_code)

noncomputable section
set_option maxRecDepth 100000

/-! ### The static part of a position -/

/-- The static part of a warp collective with immediate operands. -/
def wShape (w : WarpInstr) : Sched.CollShape :=
  match w.kind, w.srcs, w.mask with
  | .shfl m, [_, .imm b, .imm c], _ => .shfl m (tb b) (tb c)
  | .elect, _, some (.imm mk) => .elect (tb mk)
  | .barWarp, _, some (.imm mk) => .warpBar (tb mk)
  | _, _, _ => .elect 4294967295

/-- The static part of the warp collective at a position (a full election elsewhere). -/
def pcShape (pc : Nat) : Sched.CollShape :=
  match kernel.code[pc]? with
  | some ins =>
    match ins.op with
    | .warp w => wShape w
    | _ => .elect 4294967295
  | none => .elect 4294967295

theorem wShape_full {w : WarpInstr} (h : wImm w = true) : (wShape w).Full := by
  rcases w with ⟨kind, ty, dsts, srcs, mask⟩
  unfold wImm at h
  unfold wShape
  simp only at h ⊢
  split at h <;> simp_all [Sched.CollShape.Full]

/-- **Every position's static part names the whole warp.** -/
theorem pcShape_full (pc : Nat) : (pcShape pc).Full := by
  unfold pcShape
  cases hc : kernel.code[pc]? with
  | none => rfl
  | some ins =>
    simp only
    cases hop : ins.op with
    | warp w => exact wShape_full (wImm_of_code hc hop)
    | _ => rfl

theorem readBits_imm_eq {L : Launch} {g : Nat} {t : TState} {w : Nat} {v : Int} :
    readBits L g t w (.imm v) = .ok (truncBits w (BitVec.ofInt 64 v)) := rfl

/-- **The template of a warp collective with immediate operands** is undefined behaviour or has
its static part. -/
theorem warpTmpl_shape {L : Launch} {g : Nat} {t : TState} {w : WarpInstr}
    (h : wImm w = true) :
    (∃ f, warpTmpl L g t w = .ub f) ∨ Sched.tmplShape (warpTmpl L g t w) = some (wShape w) := by
  rcases w with ⟨kind, ty, dsts, srcs, mask⟩
  unfold wImm at h
  simp only at h
  split at h <;> try simp at h
  all_goals
    unfold warpTmpl
    simp only
    split
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | (exfalso; simp_all; done)
    | (try cases ‹WarpKind.shfl _ = WarpKind.shfl _›)
      (try cases ‹[_, Opnd.imm _, Opnd.imm _] = [_, _, _]›)
      cases ‹some (Opnd.imm _) = some _›
  all_goals
    simp only [shflTmpl, electTmpl, warpBarTmpl, readBits_imm_eq]
    repeat' split
  all_goals first
    | exact .inl ⟨_, rfl⟩
    | (right; simp_all [Sched.tmplShape, wShape, tb])

/-- **An event fired from a template has the template's static part.** -/
theorem fires_shape {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hf : Fires pc m e o)
    (hc : Sched.isWarpColl e = true) : Sched.kindShape e.kind = Sched.tmplShape m := by
  obtain ⟨pc', k⟩ := e
  cases k <;> simp only [Sched.isWarpColl] at hc
  all_goals cases m <;> simp_all [Fires, Sched.kindShape, Sched.tmplShape]
  obtain ⟨_, ⟨⟨-, h1, -, h2, h3, -⟩, -⟩ | ⟨⟨-, h1, -, h2, h3, -⟩, -⟩⟩ := hf <;>
    exact ⟨h1, h2, h3⟩

/-- The instruction at a warp-collective position is a warp collective. -/
theorem warp_op {pc : Nat} {ins : Instr} (hw : Lk4.warpPc pc = true)
    (hc : kernel.code[pc]? = some ins) : ∃ w, ins.op = .warp w := by
  unfold Lk4.warpPc opPc at hw
  rw [hc] at hw
  simp only at hw
  revert hw
  cases ins.op <;> simp [Lk4.warpOp]

theorem pcShape_eq {pc : Nat} {ins : Instr} {w : WarpInstr} (hc : kernel.code[pc]? = some ins)
    (hop : ins.op = .warp w) : pcShape pc = wShape w := by
  unfold pcShape
  rw [hc]
  simp only [hop]

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The static part of a warp-collective event is its position's.** -/
theorem event_shape (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g k : Nat} {e : Event} {d : TSt} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some d)) (hc : Sched.isWarpColl e = true) :
    Sched.kindShape e.kind = some (pcShape (TSt.pc d)) := by
  obtain ⟨t, ins, o, -, -, hcode, hfire⟩ := Frame.fired_site hf.sound hX he hσ
  have hw : wcSt d = true := by rw [← isWarpColl_state hX hf hg he hσ]; exact hc
  have hcode' : kernel.code[TSt.pc d]? = some ins := hcode
  obtain ⟨w, hop⟩ := warp_op hw hcode'
  have hwi := wImm_of_code hcode' hop
  rw [hop] at hfire
  change Fires _ (warpTmpl L g t w) e o at hfire
  rcases warpTmpl_shape (L := L) (g := g) (t := t) hwi with ⟨f, hub⟩ | hs
  · exfalso
    rw [hub] at hfire
    obtain ⟨rfl, -⟩ := hfire
    simp [Sched.isWarpColl] at hc
  · rw [fires_shape hfire hc, hs, pcShape_eq hcode' hop]

/-- **The template at a warp-collective state** is undefined behaviour or has the static part of
the state's position. -/
theorem state_shape {g : Nat} {d : TSt} {t : TState} {m : Tmpl} (hw : wcSt d = true)
    (hat : (threadCode L g Q).AtD d t) (hout : out kernel asms L g t = .ev m) :
    (∃ f, m = .ub f) ∨ (t.pc = TSt.pc d ∧ Sched.tmplShape m = some (pcShape (TSt.pc d))) := by
  rcases out_ev hout with ⟨f, rfl⟩ | ⟨ins, hcode, rfl⟩
  · exact .inl ⟨f, rfl⟩
  have hpc : t.pc = TSt.pc d := hat.1
  rw [hpc] at hcode
  obtain ⟨w, hop⟩ := warp_op hw hcode
  rw [hop]
  rcases warpTmpl_shape (L := L) (g := g) (t := t) (wImm_of_code hcode hop) with ⟨f, hub⟩ | hs
  · exact .inl ⟨f, hub⟩
  · exact .inr ⟨hpc, by
      change Sched.tmplShape (warpTmpl L g t w) = _
      rw [hs, pcShape_eq hcode hop]⟩

/-! ### The position of a lane's `n`-th warp collective -/

section
variable (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
  (hA : LaneAgree Q L X)
include hX hf hA

/-- **A lane with more synchronizing events than a lane of its warp at a warp-collective state has
made more warp collectives.** -/
theorem cnt_gt_of_ord {g h a b : Nat} {s : TSt} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hb : b ≤ (X.tr h).length)
    (hs : St Q L X g a = some (some s)) (hc : wcSt s = true)
    (hlt : syN (kernelSkel Q L) X g a < syN (kernelSkel Q L) X h b) :
    cnt Sched.isWarpColl X g a < cnt Sched.isWarpColl X h b := by
  have ht := hf.tracked
  have hL := lock_kernel ht hA
  have hh : h < L.threads := hw.1.2.1
  have hev : ClassEv Sched.isWarpColl wcSt Q L X := fun {g k e s} hg he hσ =>
    isWarpColl_state hX hf hg he hσ
  have hsy := wcSt_sy hc
  obtain ⟨b1, hb1, hsy1, hn1, -⟩ := exists_last (kernelSkel Q L) (X := X) h b
    (syN (kernelSkel Q L) X h b - 1) (by omega)
  obtain ⟨b0, hb0, hsy0, hn0⟩ := exists_ordinal (kernelSkel Q L) (X := X) h
    (syN (kernelSkel Q L) X h b - 1 - syN (kernelSkel Q L) X g a) (a := b1)
    (n := syN (kernelSkel Q L) X g a) hsy1 (by omega)
  obtain ⟨s0, hs0, hsy0'⟩ := hsy0
  have hkey := hL _ hw ha (by omega) hs hs0 hsy hsy0' rfl hn0
  have hc0 : wcSt s0 = true := by rw [← wcKey_class hw hsy hsy0' hkey]; exact hc
  have hcnt := lock_count (kernelSkel Q L) ht hL hev (fun hs => wcSt_sy hs) wcKey_class _ hw ha
    (by omega) hs hs0 hsy hsy0' rfl hn0
  obtain ⟨e0, he0⟩ : ∃ e0, (X.tr h)[b0]? = some e0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have he0c : Sched.isWarpColl e0 = true := by
    rw [hev hh (show X.get (h, b0) = some e0 from he0) hs0]
    exact hc0
  have h1 := cnt_succ (X := X) Sched.isWarpColl he0
  have h2 := cnt_mono (X := X) Sched.isWarpColl h (show b0 + 1 ≤ b by omega)
  simp only [he0c, ↓reduceIte] at h1
  omega

/-- **Two lanes of a warp at warp-collective states after equally many warp collectives are at
one position.** -/
theorem wc_pc_eq {g h a b : Nat} {s s' : TSt} (hw : SameWarp L g h)
    (ha : a ≤ (X.tr g).length) (hb : b ≤ (X.tr h).length)
    (hs : St Q L X g a = some (some s)) (hs' : St Q L X h b = some (some s'))
    (hc : wcSt s = true) (hc' : wcSt s' = true)
    (hn : cnt Sched.isWarpColl X g a = cnt Sched.isWarpColl X h b) : TSt.pc s = TSt.pc s' := by
  rcases Nat.lt_trichotomy (syN (kernelSkel Q L) X g a) (syN (kernelSkel Q L) X h b) with
    hlt | heq | hgt
  · have := cnt_gt_of_ord hX hf hA hw ha hb hs hc hlt
    omega
  · have hL := lock_kernel hf.tracked hA
    have hkey := hL _ hw ha hb hs hs' (wcSt_sy hc) (wcSt_sy hc') rfl heq.symm
    rw [← (kernelSkel Q L).pc_key (g := g) (wcSt_sy hc),
      ← (kernelSkel Q L).pc_key (g := h) (wcSt_sy hc'), hkey]
  · have := cnt_gt_of_ord hX hf hA (sameWarp_symm hw) hb ha hs' hc' hgt
    omega

end

open Classical in
/-- The position of the `n`-th warp collective of the warp `key`: the position of a lane of the
warp at a warp-collective state after `n` warp collectives, if there is one. -/
def wcPc (Q : Params) (L : Launch) (X : Execution) (key : Nat × Nat) (n : Nat) : Nat :=
  if h : ∃ pc g a s, g < L.threads ∧ warpKey L g = key ∧ a ≤ (X.tr g).length ∧
      St Q L X g a = some (some s) ∧ wcSt s = true ∧ cnt Sched.isWarpColl X g a = n ∧ TSt.pc s = pc
  then h.choose else 0

theorem wcPc_eq (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hA : LaneAgree Q L X) {g a : Nat} {s : TSt} (hg : g < L.threads)
    (ha : a ≤ (X.tr g).length) (hs : St Q L X g a = some (some s)) (hc : wcSt s = true) :
    wcPc Q L X (warpKey L g) (cnt Sched.isWarpColl X g a) = TSt.pc s := by
  have hex : ∃ pc g' a' s', g' < L.threads ∧ warpKey L g' = warpKey L g ∧
      a' ≤ (X.tr g').length ∧ St Q L X g' a' = some (some s') ∧ wcSt s' = true ∧
      cnt Sched.isWarpColl X g' a' = cnt Sched.isWarpColl X g a ∧ TSt.pc s' = pc :=
    ⟨_, g, a, s, hg, rfl, ha, hs, hc, rfl, rfl⟩
  unfold wcPc
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨g', a', s', hg', hk, ha', hs', hc', hn, hpc⟩ := hex.choose_spec
  rw [← hpc]
  exact wc_pc_eq hX hf hA (sameWarp_of_key hg' hg hk) ha' ha hs' hs hc' hc hn

/-- **`WarpCollFacts.shape`**, with `F key n = (wcPc key n, pcShape (wcPc key n))`. -/
theorem warpColl_shape (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hA : LaneAgree Q L X) : ∃ F : Nat × Nat → Nat → Nat × Sched.CollShape,
    (∀ key n, (F key n).2.Full) ∧
    (∀ {g k : Nat} {e : Event} {d : TSt}, g < L.threads → St Q L X g k = some (some d) →
      X.get (g, k) = some e → Sched.isWarpColl e = true →
      Sched.kindShape e.kind =
        some (F (warpKey L g) (((X.tr g).take k).countP Sched.isWarpColl)).2) ∧
    (∀ {g : Nat} {d : TSt} {t : TState} {m : Tmpl}, g < L.threads →
      St Q L X g (X.tr g).length = some (some d) → nextKind d = .warp →
      (threadCode L g Q).AtD d t → out kernel asms L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1 ∧
          Sched.tmplShape m = some (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).2)) := by
  refine ⟨fun key n => (wcPc Q L X key n, pcShape (wcPc Q L X key n)),
    fun key n => pcShape_full _, ?_, ?_⟩
  · intro g k e d hg hσ he hc
    have hw : wcSt d = true := by rw [← isWarpColl_state hX hf hg he hσ]; exact hc
    have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp
      (show (X.tr g)[k]? = some e from he)).1.le
    have := wcPc_eq hX hf hA hg hk hσ hw
    simp only [cnt] at this
    simp only [this]
    exact event_shape hX hf hg he hσ hc
  · intro g d t m hg hσ hk hat hout
    have hw : wcSt d = true := (nextKind_warp d).mp hk
    have := wcPc_eq hX hf hA hg le_rfl hσ hw
    simp only [cnt, List.take_length] at this
    simp only [this]
    exact state_shape hw hat hout

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
