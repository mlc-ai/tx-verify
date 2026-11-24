-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Assumptions

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem vote_operands {d : D} {t : TState} (hd : d.site = .rescaleVote)
    (ha : (code P L g).AtD d t) :
    readBits L g t 32 (.reg 1112) = .ok (BitVec.ofNat 64 (2 ^ 32 - 1)) ∧
      readPred L g t (.reg 109) = .ok d.voteTest := by
  have hp : t.regs 109 = some (.pred d.voteTest) :=
    reg_value ha (by rw [hd]; decide +kernel)
  have hm : t.regs 1112 = some (b32 (2 ^ 32 - 1)) :=
    reg_value ha (by rw [hd]; decide +kernel)
  have hbits := readBits_b32 (L := L) (g := g) hm (by decide : 2 ^ 32 - 1 < 2 ^ 32)
  have hpred : readPred L g t (.reg 109) = .ok d.voteTest := by
    simp [readPred, readReg, hp, bind, Except.bind, pure, Except.pure]
  exact ⟨hbits, hpred⟩

/-- The full-mask rescale vote has a defined template in every launched warp. -/
theorem rescaleVote_template {mem0 : Mem0} (hpre : Pre P L mem0)
    {d : D} {t : TState} {ins : Instr}
    (hd : d.site = .rescaleVote) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl asms L g t ins.op =
      .voteMode .any (2 ^ 32 - 1) d.voteTest (fun r => PTX.next (setReg t 1 (.pred r))) := by
  obtain ⟨hbits, hpred⟩ := vote_operands hd ha
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_578)
  have hm : electMember (2 ^ 32 - 1) (PTX.laneOf L g) := by
    have hl := Nat.mod_lt (g % L.block) (show 0 < 32 by decide)
    refine ⟨hl, ?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hl
  have hw : warpSize L g = 32 := by
    have h := Nat.mod_lt g (show 0 < 384 by decide)
    unfold warpSize
    rw [hpre.block, Nat.min_eq_left]
    omega
  have hmw : maskInWarp L g (2 ^ 32 - 1) := by
    unfold maskInWarp
    rw [hw]
    decide
  change voteModeTmpl L g t .any 1 109 false (.reg 1112) = _
  simp only [voteModeTmpl, hbits, hpred,
    show (BitVec.ofNat 64 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 from rfl, hm, hmw,
    ↓reduceIte, Bool.bne_false]

/-- The collective vote names all lanes and contributes this lane's actual comparison. -/
theorem fires_rescaleVote {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .rescaleVote) (ha : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ r, e.kind = .voteMode .any (2 ^ 32 - 1) d.voteTest r ∧
      u = PTX.next (setReg t 1 (.pred r)) := by
  have hsite : d.site.pc = 578 := by rw [hd]; rfl
  obtain ⟨hbits, hpred⟩ := vote_operands hd ha
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_578)
  change Fires 578 (voteModeTmpl L g t .any 1 109 false (.reg 1112)) e (some u) at hf
  simp only [voteModeTmpl, hbits, hpred] at hf
  change (Fires 578
    (if electMember (2 ^ 32 - 1) (PTX.laneOf L g) then
      if maskInWarp L g (2 ^ 32 - 1) then
        .voteMode .any (2 ^ 32 - 1) (d.voteTest != false)
          (fun r => PTX.next (setReg t 1 (.pred r)))
      else .ub .noRule
    else .ub .badValue) e (some u)) at hf
  split_ifs at hf
  · obtain ⟨r, he, hu⟩ := hf
    exact ⟨r, by simp [he], Option.some.inj hu⟩
  · simp [Fires] at hf
  · simp [Fires] at hf

private theorem vote_branch_noSegments : NoSegments asms :=
  fun a ha _ _ t => Proof.asms_segment_free t a ha

private theorem vote_ex2_shape {op : Op} (hf : ApproxForm.ofOp op = some (.ex2 .f32)) :
    ∃ i : FloatInstr, op = .float i ∧ i.op = .ex2 := by
  cases op with
  | float i =>
    refine ⟨i, rfl, ?_⟩
    simp only [ApproxForm.ofOp] at hf
    split_ifs at hf
    cases hi : i.op <;> simp_all
  | _ => simp [ApproxForm.ofOp] at hf

/-- Exact ex2.approx.f32 and its Core fallback apply to the compiled rescale and probabilities. -/
theorem vote_ex2 : ApproxFor asms (.ex2 .f32) ∧ ApproxDecline asms (.ex2 .f32) := by
  apply approx_of_rules vote_branch_noSegments
  intro launch thread t op hf
  have hi : idealArith.localRule launch thread t op = none :=
    Assumption.idealReal_localRule_none fun f h =>
      (by rw [floatForm_none_of_approx hf] at h; cases h)
  obtain ⟨i, rfl, hex⟩ := vote_ex2_shape hf
  have ha : approx.localRule launch thread t (.float i) = execApproxExact t (.float i) := by
    simp [approx, approxExact, hf]
  have hp : paramPointers.localRule launch thread t (.float i) = none := by simp [paramPointers]
  have hs : sharedBits.localRule launch thread t (.float i) = none := by
    simp [sharedBits, deadPackRule, peerPackRule]
  simp [asms, Assumptions.all, List.findSome?_cons, hi, ha, hp, hs, mulBf16x2, lg2Exact,
    cvtBf16x2, cvtUe8m0, Assumptions.ncReadOnly, hex]
  cases execApproxExact t (.float i) <;> rfl

private def voteLive (pc : Nat) : List Nat := (Flow.live pc).filter tracked.contains

private def voteFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) :
    List (Nat × Value) :=
  factsFrom (voteLive pc) (valueOf P L g d)

private theorem after_vote_event {d : D} {t : TState} {r : Bool}
    (hd : d.site = .rescaleVote) (ha : (code P L g).AtD d t) (hi : Inv P L g d) :
    At (PTX.next (setReg t 1 (.pred r))) 579 ((1, .pred r) :: voteFacts P L g d 578) := by
  have hsite : d.site.pc = 578 := by rw [hd]; rfl
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have ht := at_next_of ha hsite hsub
  have hat : At t 578 (voteFacts P L g d 578) :=
    ⟨ha.1.trans hsite, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  exact hat.set (not_mem_factsFrom (by decide +kernel))

private theorem vote_cons_fresh {r s : Nat} {v : Value} {F : List (Nat × Value)}
    (hr : r ≠ s) (hf : ∀ p ∈ F, p.1 ≠ s) : ∀ p ∈ (r, v) :: F, p.1 ≠ s := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hr
  · exact hf p hp

private theorem vote_at_reg {t : TState} {p r : Nat} {v : Value} {F : List (Nat × Value)}
    (h : At t p F) (hm : (r, v) ∈ F) : t.regs r = some v :=
  holds_mem h.2.2.2.2 hm

private theorem vote_run_set {t : TState} {pc r : Nat} {F : List (Nat × Value)} {v : Value}
    {op : Op} (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (h : At t pc F) (hx : execLocalA asms L g t op = .ok (PTX.next (setReg t r v)))
    (hn : ∀ f ∈ F, f.1 ≠ r) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) ((r, v) :: F) :=
  ⟨_, run_local hc hl h hx, h.set hn⟩

private theorem vote_branch_move {t : TState} {m : MoveInstr}
    (hpc : 579 ≤ t.pc ∧ t.pc ≤ 585) :
    execLocalA asms L g t (.move m) = execLocal L g t (.move m) := by
  have hp : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have ht : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hd : deadPackWords t.pc = none := by
    unfold deadPackWords
    split <;> first | rfl | omega
  rw [execLocalA_noSegment (Proof.asms_segment_free t),
    execLocalRule_of_none (Thread.asms_localRule_move hp ht hd)]

private abbrev referenceNot : IntInstr :=
  ⟨.not, .pred, false, [some 110], [.reg 1]⟩

private theorem vote_prepare {d : D} {t : TState} (r : Bool)
    (hat : At t 579 ((1, .pred r) :: voteFacts P L g d 578)) :
    ∃ u, run kernel asms L g 3 t = some u ∧
      At u (if r then 582 else 586)
        ((110, .pred (!r)) :: (2951, b32 1065353216) :: voteFacts P L g d 578) := by
  let F := voteFacts P L g d 578
  have hm : execLocalA asms L g t
      (.move ⟨.scalar, .int .b 32, [some 2951], [.f32imm 1065353216]⟩) =
      .ok (PTX.next (setReg t 2951 (b32 1065353216))) := by
    rw [vote_branch_move (by rw [hat.1]; decide)]
    rfl
  obtain ⟨v, hr, hv⟩ := vote_run_set Flow.code_579 rfl hat hm
    (vote_cons_fresh (by decide) (not_mem_factsFrom (by decide +kernel)))
  have hp : v.pc ∉ paramAdds := by rw [hv.1]; decide +kernel
  have ht : v.pc ∉ prefetchTensorMapSites := by rw [hv.1]; decide +kernel
  have hs : v.pc ∉ sharedBitsSites := by rw [hv.1]; decide +kernel
  have hpeer : peerPackRule v (.int referenceNot) = none := by
    unfold peerPackRule
    rfl
  have hn : execLocalA asms L g v (.int referenceNot) =
      .ok (PTX.next (setReg v 110 (.pred (!r)))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free v),
      execLocalRule_of_none (Thread.asms_localRule_int hp ht hs hpeer),
      execLocal_int (by rfl)]
    have hpred := hv.2.2.2.2.2.1
    simp [execInt, DType.width, readPred, readReg, hpred, bind, Except.bind, pure, Except.pure]
  have hv' : At v 580 ((2951, b32 1065353216) :: F) :=
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.2⟩
  obtain ⟨w, hw, hatw⟩ := vote_run_set Flow.code_580 rfl hv' hn
    (vote_cons_fresh (by decide) (not_mem_factsFrom (by decide +kernel)))
  have hL : ∀ a ∈ asms, a.localRule L g w (.bra 586 false) = none :=
    Thread.asms_localRule_bra (by rw [hatw.1]; decide +kernel)
      (by rw [hatw.1]; decide +kernel)
  obtain ⟨u, hu, hatu⟩ := run_bra Flow.code_581 (!r) hatw hatw.2.2.2.2.1 hL
  have hpc : (if !r then 586 else 581 + 1) = (if r then 582 else 586) := by cases r <;> rfl
  rw [hpc] at hatu
  exact ⟨u, run_comp (run_comp hr hw) hu, hatu⟩

private theorem vote_ok_of_some {α : Type} {x : Exec α} {v : α}
    (h : x.toOption = some v) : x = .ok v := by
  cases x <;> simp_all [Except.toOption]

private theorem referenceVote_true {d d' : D} (h : afterReferenceVote d true = some d') :
    ∃ mi delta gain,
      peerMaxE d.blockMax (miVal d) = .ok (fl mi) ∧
      subE true (miVal d) (fl mi) = .ok delta ∧
      ex2E true delta = .ok gain ∧
      d' = { d with mi, gainWord := gain, miUpd := true } := by
  simp only [afterReferenceVote, ↓reduceIte] at h
  obtain ⟨ref, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mi, _, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases he : ref = fl mi
  · subst ref
    simp only [ite_true] at h
    obtain ⟨delta, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨gain, hg, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨mi, delta, gain, vote_ok_of_some hr, vote_ok_of_some hd, vote_ok_of_some hg,
      Option.some.inj h.symm⟩
  · simp [he] at h

/-- Reference-vote success only changes the exponent reference and this block's gain. -/
theorem afterReferenceVote_fields {d d' : D} {r : Bool} (h : afterReferenceVote d r = some d') :
    d' = { d with mi := d'.mi, gainWord := d'.gainWord, miUpd := d'.miUpd } := by
  cases r
  · have he : d' = { d with gainWord := b32 1065353216 } := Option.some.inj h.symm
    rw [he]
  · obtain ⟨mi, _, gain, _, _, _, rfl⟩ := referenceVote_true h
    rfl

private def referenceFrame : List Nat := (voteLive 578).filter (· != 2950)

private theorem run_reference_updates {d : D} {t : TState} {mi : ℝ} {delta gain : Value}
    (hm : peerMaxE d.blockMax (miVal d) = .ok (fl mi))
    (hs : subE true (miVal d) (fl mi) = .ok delta)
    (hx : ex2E true delta = .ok gain)
    (h : At t 582 ((110, .pred false) :: (2951, b32 1065353216) :: voteFacts P L g d 578)) :
    ∃ u, run kernel asms L g 4 t = some u ∧
      At u 586 ((2950, fl mi) :: (2951, gain) :: (110, .pred false) ::
        factsFrom referenceFrame (valueOf P L g d)) := by
  let F := voteFacts P L g d 578
  have ht : At t 582 ((110, .pred false) :: F) := h.mono
    ⟨h.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hmax : t.regs 479 = some d.blockMax :=
    vote_at_reg ht (List.mem_cons_of_mem _ (mem_factsFrom (by decide +kernel)))
  have hmi : t.regs 2950 = some (miVal d) :=
    vote_at_reg ht (List.mem_cons_of_mem _ (mem_factsFrom (by decide +kernel)))
  have hmf : FloatForm.max .f32 ∈ voteFloatForms := by decide
  have hmaxStep : execLocalA asms L g t (peerMaxOp 480 (.reg 479) (.reg 2950)) =
      .ok (PTX.next (setReg t 480 (fl mi))) := by
    have ha : OpndIs L g t (.reg 479) d.blockMax := .reg hmax
    have hb : OpndIs L g t (.reg 2950) (miVal d) := .reg hmi
    rw [exec_peerMaxE (vote_idealAt hmf) (vote_declineAt hmf) ha.1 hb.1 ha.2 hb.2, hm]
    rfl
  obtain ⟨u₀, hr₀, hat₀⟩ := vote_run_set Flow.code_582 rfl ht hmaxStep
    (vote_cons_fresh (by decide) (not_mem_factsFrom (by decide +kernel)))
  have hmi₀ : u₀.regs 2950 = some (miVal d) :=
    vote_at_reg hat₀ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom (by decide +kernel))))
  let subOp : Op := .float {
    subI true with
    dsts := [some 1114]
    srcs := [.reg 2950, .reg 480] }
  have hsubStep : execLocalA asms L g u₀ subOp =
      .ok (PTX.next (setReg u₀ 1114 delta)) := by
    have hf : FloatForm.subRn .f32 ∈ voteFloatForms := by decide
    change execLocalA asms L g u₀ (.float _) = _
    rw [exec_subE (vote_idealAt hf) (vote_declineAt hf) (.reg hmi₀) (.reg hat₀.2.2.2.2.1), hs]
    rfl
  obtain ⟨u₁, hr₁, hat₁⟩ := vote_run_set Flow.code_583 rfl hat₀ hsubStep
    (vote_cons_fresh (by decide) (vote_cons_fresh (by decide)
      (not_mem_factsFrom (by decide +kernel))))
  let exOp : Op := .float { ex2I true with dsts := [some 2951], srcs := [.reg 1114] }
  have hexStep : execLocalA asms L g u₁ exOp =
      .ok (PTX.next (setReg u₁ 2951 gain)) := by
    change execLocalA asms L g u₁ (.float _) = _
    rw [exec_ex2E (vote_ex2.1 L g u₁) (vote_ex2.2 L g u₁) (.reg hat₁.2.2.2.2.1), hx]
    rfl
  obtain ⟨u₂, hr₂, hat₂⟩ := vote_run_set Flow.code_584 rfl hat₁ hexStep
    (vote_cons_fresh (by decide) (vote_cons_fresh (by decide) (vote_cons_fresh (by decide)
      (not_mem_factsFrom (by decide +kernel)))))
  let F' := factsFrom referenceFrame (valueOf P L g d)
  have hfl : u₂.regs 480 = some (fl mi) := hat₂.2.2.2.2.2.2.1
  have hat₂' : At u₂ 585 ((2951, gain) :: (110, .pred false) :: F') := hat₂.mono
    ⟨hat₂.2.2.2.2.1, hat₂.2.2.2.2.2.2.2.1, holds_factsFrom_mono hat₂.2.2.2.2.2.2.2.2
      (fun _ hr => (List.mem_filter.mp hr).1)⟩
  have hmStep : execLocalA asms L g u₂ (.move ⟨.scalar, .int .b 32, [some 2950], [.reg 480]⟩) =
      .ok (PTX.next (setReg u₂ 2950 (fl mi))) := by
    rw [vote_branch_move (by rw [hat₂'.1]; decide), execLocal_move (by rfl)]
    have hfour : FloatFmt.f32.bytes = 4 := rfl
    simp [execMove, readValue, readReg, hfl, fl, Value.bytes, DType.width, hfour,
      bind, Except.bind, pure, Except.pure]
  obtain ⟨u₃, hr₃, hat₃⟩ := vote_run_set Flow.code_585 rfl hat₂' hmStep
    (vote_cons_fresh (by decide) (vote_cons_fresh (by decide)
      (not_mem_factsFrom (by decide +kernel : 2950 ∉ referenceFrame))))
  exact ⟨u₃, run_comp (run_comp (run_comp hr₀ hr₁) hr₂) hr₃, hat₃⟩

private theorem reference_value_frame {d d' : D} {r : Nat} {take : Bool}
    (h : afterReferenceVote d take = some d')
    (hne : r ∉ [2950, 2951, 3312, 110, 481, 1733, 3577])
    (hres : ¬ (1199 ≤ r ∧ r ≤ 1714)) (hstage : ¬ (1745 ≤ r ∧ r ≤ 2413)) :
    valueOf P L g { d' with voteTaken := take } r = valueOf P L g d r := by
  let n := { d with mi := d'.mi, gainWord := d'.gainWord, miUpd := d'.miUpd, voteTaken := take }
  have he : { d' with voteTaken := take } = n :=
    congrArg (fun (x : D) => { x with voteTaken := take }) (afterReferenceVote_fields h)
  rw [he]
  have hb (j : Nat) (hj : j ∈ [2950, 2951, 3312, 110, 481, 1733, 3577]) : (r == j) = false :=
    beq_eq_false_iff_ne.mpr fun hr => hne (hr ▸ hj)
  have htbl : (table P L g n).lookup r = (table P L g d).lookup r := by
    simp only [table, List.lookup_cons, hb 2950 (by decide), hb 2951 (by decide),
      hb 3312 (by decide), hb 110 (by decide), hb 481 (by decide), hb 1733 (by decide),
      hb 3577 (by decide)]
    rfl
  simp only [valueOf, ite_eq_right hres, ite_eq_right hstage, htbl]
  rfl

private theorem reference_at {d d' : D} {t : TState} {take : Bool}
    (hr : afterReferenceVote d take = some d')
    (ht : At t 586 ((2950, miVal d') :: (2951, d'.gainWord) :: (110, .pred (!take)) ::
      factsFrom referenceFrame (valueOf P L g d))) :
    At t 586 (voteFacts P L g { d' with voteTaken := take } 586) := by
  apply ht.mono
  apply holds_of_pointwise
  intro r hm
  have hcover : ∀ j ∈ voteLive 586, j ∈ 2950 :: 2951 :: 110 :: referenceFrame := by lit_mem
  have hb := hcover r hm
  by_cases hmi : r = 2950
  · subst r
    exact ht.2.2.2.2.1
  by_cases hg : r = 2951
  · subst r
    exact ht.2.2.2.2.2.1
  by_cases hv : r = 110
  · subst r
    exact ht.2.2.2.2.2.2.1
  have hs : (voteLive 586).all (fun j => decide (j ∉ [3312, 481, 1733, 3577] ∧
      ¬ (1199 ≤ j ∧ j ≤ 1714) ∧ ¬ (1745 ≤ j ∧ j ≤ 2413))) = true := by decide +kernel
  obtain ⟨hne, hres, hstage⟩ := of_decide_eq_true (List.all_eq_true.mp hs r hm)
  have he : r ∉ [2950, 2951, 3312, 110, 481, 1733, 3577] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hne ⊢
    tauto
  rw [reference_value_frame hr he hres hstage]
  have hb := (List.mem_cons.mp hb).resolve_left hmi
  have hb := (List.mem_cons.mp hb).resolve_left hg
  have hb := (List.mem_cons.mp hb).resolve_left hv
  exact holds_mem ht.2.2.2.2.2.2.2 (mem_factsFrom hb)

/-- A successful vote transition reaches the probability computation with the selected
reference, exact exponential gain, and the actual negation of the collective predicate. -/
theorem run_afterReferenceVote {d d' : D} {t u : TState} {r : Bool}
    (hd : d.site = .rescaleVote) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hr : afterReferenceVote d r = some d') (hu : u = PTX.next (setReg t 1 (.pred r))) :
    ∃ v, run kernel asms L g (if r then 7 else 3) u = some v ∧
      At v 586 (factsFrom ((Flow.live 586).filter tracked.contains)
        (valueOf P L g { d' with voteTaken := r })) := by
  have hstart := hu ▸ after_vote_event (r := r) hd ha hi
  obtain ⟨v, hv, hat⟩ := vote_prepare (L := L) (g := g) r hstart
  cases r
  · have he : d' = { d with gainWord := b32 1065353216 } := Option.some.inj hr.symm
    have hmi : v.regs 2950 = some (miVal d') := by
      rw [he]
      exact holds_mem hat.2.2.2.2.2.2 (mem_factsFrom (by decide +kernel : 2950 ∈ voteLive 578))
    have hf : At v 586 ((2950, miVal d') :: (2951, d'.gainWord) :: (110, .pred true) ::
        factsFrom referenceFrame (valueOf P L g d)) := hat.mono
      ⟨hmi, he.symm ▸ hat.2.2.2.2.2.1, hat.2.2.2.2.1, holds_factsFrom_mono
        hat.2.2.2.2.2.2 (fun _ h => (List.mem_filter.mp h).1)⟩
    exact ⟨v, hv, reference_at hr hf⟩
  · obtain ⟨mi, delta, gain, hm, hs, hx, rfl⟩ := referenceVote_true hr
    obtain ⟨w, hw, hatw⟩ := run_reference_updates (L := L) (g := g) hm hs hx hat
    exact ⟨w, run_comp hv hw, reference_at hr hatw⟩

/-- Neither the reference vote nor an ending event at its site accesses ordinary memory. -/
theorem vote_event_nonaccess {i : Nat} {e : Event} {d : D} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .rescaleVote) : e.acc = none := by
  obtain ⟨_, _, o, hAt, _, hCode, hFire⟩ := Frame.fired_site hs hX he hd
  rcases e with ⟨tag, k⟩
  cases o with
  | none =>
    rcases fires_none_ends hFire with ⟨_, h⟩ | h <;> change k = _ at h <;> rw [h] <;> rfl
  | some u =>
    obtain ⟨_, hKind, _⟩ := fires_rescaleVote hSite hAt hCode hFire
    change k = _ at hKind
    rw [hKind]
    rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
