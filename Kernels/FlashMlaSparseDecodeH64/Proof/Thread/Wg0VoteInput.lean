-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerNumeric
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.SetpCore

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem rowLocalMax_bytes (L : Launch) (d : D) : (rowLocalMax L d).bytes = 4 := by
  unfold rowLocalMax peerRowMax
  cases h0 : peerHalfMax d.scoreSums 0 with
  | error f => rfl
  | ok lo =>
    simp only [bind, Except.bind]
    cases h1 : peerHalfMax d.scoreSums 8 with
    | error f => rfl
    | ok hi =>
      simp only
      cases hm : peerMaxE lo hi with
      | error f => rfl
      | ok m =>
        simp only
        cases hv : mulE true m (b32 (paramWord L 28 4)) with
        | error f => rfl
        | ok v => exact mulE_four true m (b32 (paramWord L 28 4)) v hv

/-- The lane's maximum store can only write its shared row slot. -/
theorem fired_rowMax (hpre : Pre P L mem0)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .rowMax) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a, e.kind = .wr a (rowLocalMax L d).toBytes ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) ∧ a.size = 4 ∧
      o = some (PTX.next t) := by
  have hsite : d.site.pc = 566 := by rw [hd]; rfl
  have hzero : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have hsub := ha.2.1.trans hzero
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_566)
  let base := L.sharedBase + 4 * (tidOf L g % 128)
  let a : Loc := ⟨.shared, g / L.block, base + 221184⟩
  have hr : t.regs 471 = some (b32 base) :=
    reg_value ha (by rw [hd]; decide +kernel)
  have hv : t.regs 1109 = some (rowLocalMax L d) :=
    reg_value ha (by rw [hd]; decide +kernel)
  have hbase := sharedBase_lt hpre
  have hb : base + 221184 < 2 ^ 32 := by dsimp [base]; omega
  have hal : a.addr % 4 = 0 := by
    have hh := sharedBase_mod8 hpre
    change (L.sharedBase + 4 * (tidOf L g % 128) + 221184) % 4 = 0
    omega
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := 471) (w := 32) (by rfl) rfl rfl
    rfl (by simp)] at hf
  have haddr := effAddr_b32_off (L := L) (g := g) (off := 221184) hr hb
  change effAddr L g t .shared 471 221184 = .ok a at haddr
  have hstore := storeValue_of_bytes (w := 32) (rowLocalMax_bytes L d)
  simp [DType.width, storeTmpl, haddr, elemAcc, hsub, hal, hv, hstore, readValue, readReg,
    afterStore, bind, Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · simp [a, base, shLoc, ctaOf, rowMaxBase, Nat.add_comm, Nat.add_left_comm]
  · simpa [PTX.next, hsub] using hu

/-- The lane's shared maximum store writes exactly the four bytes of its local reduction. -/
theorem fires_rowMax (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .rowMax) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .wr a (rowLocalMax L d).toBytes ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) ∧ a.size = 4 ∧
      u = PTX.next t := by
  obtain ⟨a, he, hl, hs, hu⟩ := fired_rowMax hpre hd ha hi hc hf
  exact ⟨a, he, hl, hs, Option.some.inj hu⟩

/-- The shared maximum store is followed by the second warpgroup barrier. -/
theorem step_rowMax (hpre : Pre P L mem0) (d : D) (hd : d.site = .rowMax) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins ha hi hc hf => by
    obtain ⟨a, he, hl, hs, rfl⟩ := fires_rowMax hpre hd ha hi hc hf
    have hsite : d.site.pc = 566 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
    let d' : D := { d with site := .wg0Sync2, sub := 0 }
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, writeStep, hd, he, hl, hs, siteLoc, Site.elemBytes, Site.elems,
        hsub, d']
    have ht := at_next_of ha hsite hsub
    obtain ⟨v, hr, hv⟩ : ∃ v, run kernel asms L g 2 (PTX.next t) = some v ∧
        At v 569 (facts P L g d') := by
      seg_fp ht using
        (try simp only [d'])
        (try wg0_values)
        (norm_bits [sb])
    refine .inl (.inr ⟨d', v, hn, run_rtg hr,
      ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩, ?_⟩)
    exact inv_setSite hi .wg0Sync2 (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
      (by simp) (by simp) (by simp)

/-- These exact floating forms use the ideal hook, with Core handling its declines. -/
def voteFloatForms : List FloatForm :=
  [.max .f32, .subRn .f32, .setp .f32, .fmaRnF32x2, .addRnF32x2, .fma .f32, .mul .f32,
    .neg .f32, .add .f32]

private theorem vote_noSegments : NoSegments asms :=
  fun a ha _ _ t => Proof.asms_segment_free t a ha

/-- The ideal-real hook provides these forms as the only assumption that can execute them. -/
theorem vote_idealAt {f : FloatForm} {t : TState} (hf : f ∈ voteFloatForms) :
    IdealAt asms f L g t := by
  apply (idealFor_head (f := f) ?_ vote_noSegments.tail).at
  simp only [voteFloatForms, List.mem_cons, List.not_mem_nil, or_false] at hf ⊢
  tauto

private theorem vote_floatShape {op : Op} {f : FloatForm}
    (hf : f ∈ voteFloatForms) (hform : FloatForm.ofOp op = some f) :
    ∃ i : FloatInstr, op = .float i ∧ ApproxForm.ofOp op = none ∧ i.op ≠ .lg2 ∧
      (i.op ≠ .mul ∨ i.ty.lanes = 1) := by
  cases op with
  | float i =>
    refine ⟨i, rfl, ?_⟩
    simp only [voteFloatForms, List.mem_cons, List.not_mem_nil, or_false] at hf
    cases hi : i.op <;> simp [FloatForm.ofOp, ApproxForm.ofOp, hi] at hform ⊢
    all_goals repeat' split at hform
    all_goals simp_all
    subst f
    simp_all
  | cvt c =>
    simp only [FloatForm.ofOp] at hform
    split_ifs at hform <;> simp_all [voteFloatForms]
    all_goals subst f; simp_all
  | _ => simp [FloatForm.ofOp] at hform

private theorem vote_lg2_none {t : TState} {i : FloatInstr} (hi : i.op ≠ .lg2) :
    lg2Exact.localRule L g t (.float i) = none := by
  cases hx : i.op <;> first | exact (hi hx).elim | simp only [lg2Exact, hx]

private theorem vote_mulBf16_none {t : TState} {i : FloatInstr}
    (h : i.op ≠ .mul ∨ i.ty.lanes = 1) : mulBf16x2.localRule L g t (.float i) = none := by
  rcases h with hm | hl
  · cases hi : i.op <;> first | exact (hm hi).elim | simp only [mulBf16x2, hi]
  · cases hty : i.ty
    simp_all [mulBf16x2]

private theorem vote_param_none {t : TState} {i : FloatInstr} :
    paramPointers.localRule L g t (.float i) = none := by
  simp [paramPointers]

private theorem vote_shared_none {t : TState} {i : FloatInstr} :
    sharedBits.localRule L g t (.float i) = none := by
  simp [sharedBits, deadPackRule, peerPackRule]

/-- The other arithmetic hooks decline these forms, so a decline reaches the Core rule. -/
theorem vote_declineAt {f : FloatForm} {t : TState} (hf : f ∈ voteFloatForms) :
    DeclineAt asms f L g t := by
  apply declineAt_head
  · intro a ha op hh
    obtain ⟨i, rfl, happ, hlg, hmul⟩ := vote_floatShape hf hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [approx, approxExact, happ]
    · exact vote_mulBf16_none hmul
    · rfl
    · rfl
    · exact vote_lg2_none hlg
    · rfl
    · exact vote_param_none
    · rfl
    · exact vote_shared_none
    · rfl
  · exact vote_noSegments.tail.segFreePc

/-- A shared scalar word address preserves the XOR of bit six in the thread index. -/
private theorem max_peer_word_offset (n : Nat) : (4 * n) ^^^ 256 = 4 * (n ^^^ 64) := by
  have h := Nat.shiftLeft_xor_distrib (a := n) (b := 64) (i := 2)
  simpa [Nat.shiftLeft_eq, Nat.mul_comm _ 4] using h.symm

/-- The partner-maximum load can only read the paired lane's shared slot. -/
theorem fired_maxRead (hpre : Pre P L mem0)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .maxRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      bs.length = 4 ∧ o = some (afterLoad t [1110] bs) := by
  have hsite : d.site.pc = 572 := by rw [hd]; rfl
  have hzero : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have hsub := ha.2.1.trans hzero
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_572)
  let j := tidOf L g % 128 ^^^ 64
  let base := L.sharedBase + 4 * j
  let a : Loc := ⟨.shared, g / L.block, base + 221184⟩
  have hr : t.regs 472 = some (b32 base) := by
    have hh : t.regs 472 = some (b32 (L.sharedBase + (4 * (tidOf L g % 128) ^^^ 256))) :=
      reg_value ha (by rw [hd]; decide +kernel)
    simpa only [base, j, max_peer_word_offset] using hh
  have hj : j < 128 := Nat.xor_lt_two_pow (n := 7) (Nat.mod_lt _ (by decide)) (by decide)
  have hb : base + 221184 < 2 ^ 32 := by
    have hh := sharedBase_lt hpre
    dsimp [base]
    omega
  have hal : a.addr % 4 = 0 := by
    have hh := sharedBase_mod8 hpre
    change (L.sharedBase + 4 * j + 221184) % 4 = 0
    omega
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 472) (w := 32) (by rfl) rfl rfl
    rfl rfl] at hf
  have haddr := effAddr_b32_off (L := L) (g := g) (off := 221184) hr hb
  change effAddr L g t .shared 472 221184 = .ok a at haddr
  simp [MemAccess.regs, DType.width, loadTmpl, haddr, elemAcc, hsub, hal, bind,
    Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨bs, hsize, rfl, hu⟩ := hf
  refine ⟨_, bs, rfl, ?_, rfl, hsize, hu⟩
  simp [a, base, j, shLoc, ctaOf, rowMaxBase, Nat.add_comm, Nat.add_left_comm]

/-- The row-maximum load returns the four bytes from the corresponding peer lane. -/
theorem fires_maxRead (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .maxRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)) ∧ a.size = 4 ∧
      bs.length = 4 ∧ u = afterLoad t [1110] bs := by
  obtain ⟨a, bs, he, hl, hs, hn, hu⟩ := fired_maxRead hpre hd ha hi hc hf
  exact ⟨a, bs, he, hl, hs, hn, Option.some.inj hu⟩

private def maxLive : List Nat := (Flow.live 572).filter tracked.contains

private theorem max_afterLoad {d : D} {t : TState} {bs : List (Option Byte)} {v : Value}
    (hd : d.site = .maxRead) (ha : (code P L g).AtD d t) (hi : Inv P L g d)
    (hv : rebuild 3 bs = .ok v) :
    At (afterLoad t [1110] bs) 573 ((1110, v) :: factsFrom maxLive (valueOf P L g d)) := by
  have hsite : d.site.pc = 572 := by rw [hd]; rfl
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have hnext := at_next_of ha hsite hsub
  have hat : At t 572 (factsFrom maxLive (valueOf P L g d)) :=
    ⟨ha.1.trans hsite, hnext.2.1, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2⟩
  have hh : afterLoad t [1110] bs = PTX.next (setReg t 1110 v) := by
    simp [afterLoad, hv, hat.2.1, hat.2.2.1, setRegs, PTX.next, setReg]
  rw [hh]
  exact hat.set (not_mem_factsFrom (by decide +kernel))

private theorem decodePeak_encode {v : Value} {p : WithBot ℝ} (h : decodePeak v = some p) :
    peakVal p = v := by
  unfold decodePeak at h
  split at h
  · cases h
    exact ‹v = negInf›.symm
  · cases hv : valFloat .f32 v with
    | error f => simp [hv, Except.toOption] at h
    | ok x =>
      by_cases he : fl x = v
      · simp only [hv, he, ite_true, Except.toOption, Option.bind_some] at h
        cases h
        exact he
      · simp [hv, he, Except.toOption] at h

private theorem vote_frame {P : Params} {L : Launch} {g : Nat} {d : D} {r : Nat}
    {m : Value} {p : WithBot ℝ} {q : Bool}
    (h : r ∉ [2885, 479, 109, 481, 1727, 1733]) :
    valueOf P L g { d with blockMax := m, peak := p, voteTest := q, site := .rescaleVote } r =
      valueOf P L g d r := by
  have hbe (j : Nat) (hm : j ∈ [2885, 479, 109, 481, 1727, 1733]) : (r == j) = false :=
    beq_eq_false_iff_ne.mpr fun he => h (he ▸ hm)
  have ht : (table P L g
      { d with blockMax := m, peak := p, voteTest := q, site := .rescaleVote }).lookup r =
      (table P L g d).lookup r := by
    simp only [table, List.lookup_cons, hbe 2885 (by decide), hbe 479 (by decide),
      hbe 109 (by decide), hbe 481 (by decide), hbe 1727 (by decide), hbe 1733 (by decide)]
    rfl
  simp only [valueOf, ht]
  rfl

private def maxFrame : List Nat := maxLive.filter (· != 2885)

private theorem vote_reg {t : TState} {p r : Nat} {v : Value} {F : List (Nat × Value)}
    (h : At t p F) (hm : (r, v) ∈ F) : t.regs r = some v :=
  holds_mem h.2.2.2.2 hm

private theorem vote_fresh {r s : Nat} {v : Value} {F : List (Nat × Value)}
    (hr : r ≠ s) (hf : ∀ p ∈ F, p.1 ≠ s) : ∀ p ∈ (r, v) :: F, p.1 ≠ s := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hr
  · exact hf p hp

private theorem run_vote_set {t : TState} {p r : Nat} {F : List (Nat × Value)} {v : Value}
    {op : Op} (hc : kernel.code[p]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (h : At t p F) (he : execLocalA asms L g t op = .ok (PTX.next (setReg t r v)))
    (hf : ∀ p ∈ F, p.1 ≠ r) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (p + 1) ((r, v) :: F) :=
  ⟨_, run_local hc hl h he, h.set hf⟩

private theorem run_vote_max {t : TState} {p r a b : Nat} {F : List (Nat × Value)}
    {va vb v : Value} (hc : kernel.code[p]? = some ⟨none, peerMaxOp r (.reg a) (.reg b)⟩)
    (h : At t p F) (ha : OpndIs L g t (.reg a) va) (hb : OpndIs L g t (.reg b) vb)
    (hv : peerMaxE va vb = .ok v) (hf : ∀ p ∈ F, p.1 ≠ r) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (p + 1) ((r, v) :: F) := by
  apply run_vote_set hc rfl h ?_ hf
  have hform : FloatForm.max .f32 ∈ voteFloatForms := by decide
  rw [exec_peerMaxE (vote_idealAt hform) (vote_declineAt hform) ha.1 hb.1 ha.2 hb.2, hv]
  rfl

private theorem run_vote_gap {t : TState} {F : List (Nat × Value)} {m mi gap : Value}
    (h : At t 575 F) (hm : t.regs 479 = some m) (hmi : t.regs 2950 = some mi)
    (hv : subE true m mi = .ok gap) (hf : ∀ p ∈ F, p.1 ≠ 1111) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 576 ((1111, gap) :: F) := by
  apply run_vote_set (op := .float {
    subI true with
    dsts := [some 1111]
    srcs := [.reg 479, .reg 2950] }) Flow.code_575 rfl h ?_ hf
  have hform : FloatForm.subRn .f32 ∈ voteFloatForms := by decide
  rw [exec_subE (vote_idealAt hform) (vote_declineAt hform) (.reg hm) (.reg hmi), hv]
  rfl

private theorem run_vote_pred {t : TState} {F : List (Nat × Value)} {gap : Value} {q : Bool}
    (h : At t 576 F) (hg : t.regs 1111 = some gap)
    (hv : setpE (.ord .gt) true gap (b32 1086324736) = .ok q)
    (hf : ∀ p ∈ F, p.1 ≠ 109) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 577 ((109, .pred q) :: F) := by
  apply run_vote_set (op := .float {
    setpI (.ord .gt) true with
    dsts := [some 109]
    srcs := [.reg 1111, .f32imm 1086324736] }) Flow.code_576 rfl h ?_ hf
  have hform : FloatForm.setp .f32 ∈ voteFloatForms := by decide
  have himm : OpndIs L g t (.f32imm 1086324736) (b32 1086324736) := .imm
  rw [exec_setpE (vote_idealAt hform) (vote_declineAt hform) (.inl rfl) rfl rfl
    (.reg hg) himm, hv]
  rfl

private theorem run_vote_mask {t : TState} {F : List (Nat × Value)}
    (h : At t 577 F) (hf : ∀ p ∈ F, p.1 ≠ 1112) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 578 ((1112, b32 (2 ^ 32 - 1)) :: F) := by
  apply run_vote_set Flow.code_577 rfl h ?_ hf
  have hp : t.pc ∉ paramAdds := by rw [h.1]; decide +kernel
  have ht : t.pc ∉ prefetchTensorMapSites := by rw [h.1]; decide +kernel
  have hd : deadPackWords t.pc = none := by rw [h.1]; rfl
  rw [execLocalA_noSegment (Proof.asms_segment_free t),
    execLocalRule_of_none (Thread.asms_localRule_move hp ht hd)]
  rfl

private theorem except_ok_of_some {α ε : Type} {x : Except ε α} {v : α}
    (h : x.toOption = some v) : x = .ok v := by
  cases x <;> simp_all [Except.toOption]

private theorem withPeerMax_witness {d d' : D} {peer : Value} (h : withPeerMax L d peer = some d') :
    ∃ m p gap q,
      peerMaxE (rowLocalMax L d) peer = .ok m ∧
      peerMaxE (peakVal d.peak) m = .ok (peakVal p) ∧
      subE true m (miVal d) = .ok gap ∧
      setpE (.ord .gt) true gap (b32 1086324736) = .ok q ∧
      d' = { d with blockMax := m, peak := p, voteTest := q } := by
  unfold withPeerMax at h
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨gap, hg, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨m, p, gap, q, except_ok_of_some hm, ?_, except_ok_of_some hg,
    except_ok_of_some hq, Option.some.inj h.symm⟩
  rw [decodePeak_encode hp]
  exact except_ok_of_some hv

private theorem vote_run_input {d d' : D} {t : TState} {peer : Value}
    (h : withPeerMax L d peer = some d')
    (ht : At t 573 ((1110, peer) :: factsFrom maxLive (valueOf P L g d))) :
    ∃ u, run kernel asms L g 5 t = some u ∧
      At u 578 (facts P L g { d' with site := .rescaleVote }) := by
  obtain ⟨m, p, gap, q, hm, hpeak, hgap, hpred, rfl⟩ := withPeerMax_witness h
  let F := factsFrom maxFrame (valueOf P L g d)
  have hno0 : 479 ∉ maxLive := by decide +kernel
  have hown : t.regs 1109 = some (rowLocalMax L d) :=
    vote_reg ht (List.mem_cons_of_mem _ (mem_factsFrom (by decide +kernel)))
  obtain ⟨u0, hu0, hat0⟩ := run_vote_max Flow.code_573 ht
    (.reg hown) (.reg ht.2.2.2.2.1) hm
    (vote_fresh (by decide) (not_mem_factsFrom hno0))
  have hp0 : u0.regs 2885 = some (peakVal d.peak) :=
    vote_reg hat0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom (by decide +kernel))))
  have hat0' : At u0 574 ((479, m) :: F) := hat0.mono
    ⟨hat0.2.2.2.2.1, holds_factsFrom_mono hat0.2.2.2.2.2.2
      (fun _ hr => (List.mem_filter.mp hr).1)⟩
  obtain ⟨u1, hu1, hat1⟩ := run_vote_max Flow.code_574 hat0' (.reg hp0)
    (.reg hat0'.2.2.2.2.1) hpeak
    (vote_fresh (by decide) (not_mem_factsFrom (by decide +kernel : 2885 ∉ maxFrame)))
  have hmi : u1.regs 2950 = some (miVal d) :=
    vote_reg hat1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (mem_factsFrom (by decide +kernel))))
  obtain ⟨u2, hu2, hat2⟩ := run_vote_gap (L := L) (g := g) hat1 hat1.2.2.2.2.2.1 hmi hgap
    (vote_fresh (by decide) (vote_fresh (by decide)
      (not_mem_factsFrom (by decide +kernel : 1111 ∉ maxFrame))))
  obtain ⟨u3, hu3, hat3⟩ := run_vote_pred (L := L) (g := g) hat2 hat2.2.2.2.2.1 hpred
    (vote_fresh (by decide) (vote_fresh (by decide) (vote_fresh (by decide)
      (not_mem_factsFrom (by decide +kernel : 109 ∉ maxFrame)))))
  obtain ⟨u4, hu4, hat4⟩ := run_vote_mask (L := L) (g := g) hat3
    (vote_fresh (by decide) (vote_fresh (by decide) (vote_fresh (by decide)
      (vote_fresh (by decide) (not_mem_factsFrom (by decide +kernel : 1112 ∉ maxFrame))))))
  refine ⟨u4, run_comp (run_comp (run_comp (run_comp hu0 hu1) hu2) hu3) hu4, hat4.mono ?_⟩
  apply holds_of_pointwise
  intro r hr
  let R := (Flow.live 578).filter tracked.contains
  change r ∈ R at hr
  have hcover : ∀ r ∈ R, r ∈ 1112 :: 109 :: 2885 :: 479 :: maxFrame := by
    dsimp [R]
    lit_mem
  have hmem := hcover r hr
  by_cases hmask : r = 1112
  · subst r; exact hat4.2.2.2.2.1
  by_cases hq : r = 109
  · subst r; exact hat4.2.2.2.2.2.1
  by_cases hp : r = 2885
  · subst r; exact hat4.2.2.2.2.2.2.2.1
  by_cases hm' : r = 479
  · subst r; exact hat4.2.2.2.2.2.2.2.2.1
  have hframe : r ∉ [2885, 479, 109, 481, 1727, 1733] := by
    intro hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp rfl
    · exact hm' rfl
    · exact hq rfl
    · exact (by dsimp [R]; decide +kernel : 481 ∉ R) hr
    · exact (by dsimp [R]; decide +kernel : 1727 ∉ R) hr
    · exact (by dsimp [R]; decide +kernel : 1733 ∉ R) hr
  rw [vote_frame hframe]
  have hmem := (List.mem_cons.mp hmem).resolve_left hmask
  have hmem := (List.mem_cons.mp hmem).resolve_left hq
  have hmem := (List.mem_cons.mp hmem).resolve_left hp
  have hmem := (List.mem_cons.mp hmem).resolve_left hm'
  exact holds_mem hat4.2.2.2.2.2.2.2.2.2 (mem_factsFrom hmem)

private theorem vote_input_inv {d d' : D} {peer : Value} (hi : Inv P L g d)
    (hd : d.site = .maxRead) (h : withPeerMax L d peer = some d') :
    Inv P L g { d' with site := .rescaleVote } := by
  obtain ⟨m, p, _, q, _, _, _, _, rfl⟩ := withPeerMax_witness h
  have hs : d.sub < (Site.rescaleVote.elems) := by simpa [hd, Site.elems] using hi.subLt
  exact ⟨hi.wg, hi.warpLt, hi.laneLt, hi.headEq, hi.ring, hi.blockLt,
    by simp [Site.inEpilogue], by simp [Site.inRescale], hs, by simp, by simp, by simp,
    by simp [Site.needsRowTotal], by simp [Site.needsExchangeReady]⟩

/-- The peer word produces the running maximum and lane predicate before the warp vote. -/
theorem step_maxRead (hpre : Pre P L mem0) (d : D) (hd : d.site = .maxRead) :
    (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins ha hi hc hf
  obtain ⟨a, bs, he, hl, hs, _, rfl⟩ := fires_maxRead hpre hd ha hi hc hf
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have hn : next P L g d e = some ((rebuild 3 bs).toOption.bind fun peer =>
      (withPeerMax L d peer).map fun d' => { d' with site := .rescaleVote }) := by
    simp [next, nextSite, hd, he, siteLoc, hl, hs, Site.elemBytes]
  refine .inl ?_
  cases hb : rebuild 3 bs with
  | error f => exact .inl (by simp [hn, hb, Except.toOption])
  | ok peer =>
    cases hp : withPeerMax L d peer with
    | none => exact .inl (by simp [hn, hb, hp, Except.toOption])
    | some d' =>
      have hat := max_afterLoad hd ha hi hb
      obtain ⟨v, hr, hv⟩ := vote_run_input hp hat
      have hsub' : d'.sub = 0 := by
        obtain ⟨m, p, _, q, _, _, _, _, rfl⟩ := withPeerMax_witness hp
        exact hsub
      refine .inr ⟨{ d' with site := .rescaleVote }, v, ?_, run_rtg hr,
        ⟨hv.1, hv.2.1.trans hsub'.symm, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩,
        vote_input_inv hi hd hp⟩
      simp [hn, hb, hp, Except.toOption]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
