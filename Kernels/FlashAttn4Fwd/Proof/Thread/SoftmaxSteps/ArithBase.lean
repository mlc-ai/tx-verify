-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase
public import Lemmas.Flow.FmaRun
public import Lemmas.Flow.BarReg

@[expose] public section

/-! # The softmax arithmetic segments: checkpoint tools

The long local segments of a tile (the row maximum, the exponentials, the probability packs)
are cut at checkpoints (`Seg`, `SegChain`): the facts at a checkpoint are the registers live
there, valued by the table of the state with the intermediate values listed in front
(`valueEx`). An evaluated piece is closed by `ar_seg` (`ar_close` for each written value); the
steps evaluation does not take are pieces of their own (`FloatRun`, `FmaRun`), with the facts
this file proves:

* the scale parameter's word reads as `sc L`, alone and as a pair (`scale_ok`, `scale_pair`);
* with `sk % 128 = 0` the first tile's column mask is all ones (`mask_base`);
* the numbers of the constants `0f00000000` and `0fC1000000` (`fzero`, `neg8`);
* the address of the statistics word (`alpha_addr`);
* outside the software `exp2` and peer-bit sites no assumption takes a segment, so the ideal
  reading of `idealArith` applies (`segFree_rest`, `segFree_range`, `ideal_at`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The scale parameter's word reads as a number (`Pre.paramScale`). -/
theorem scale_read {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ∃ x, valFloat .f32 (scaleV L) = .ok x := by
  obtain ⟨bits, hb, hp, hv⟩ := hpre.paramScale
  cases hq : f32Value bits with
  | none => simp [hq] at hv
  | some q =>
    refine ⟨q, ?_⟩
    have hs : scaleV L = b32 bits := by
      simp only [scaleV, hp, Option.getD_some, truncBits, BitVec.toNat_ofNat, b32]
      congr 2
      omega
    rw [hs]
    exact valFloat_b32 (by omega) hq

/-- The scale parameter's word reads as `sc L`. -/
theorem scale_ok {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    valFloat .f32 (scaleV L) = .ok (sc L) := by
  obtain ⟨x, hx⟩ := scale_read hpre
  rw [hx, sc, rd32, hx]
  rfl

/-- The assumptions after the ideal arithmetic. -/
abbrev rest : List Assumption :=
  [Assumptions.clusterMbar, Assumptions.approx, Assumptions.swExp2, Assumptions.peerBit,
    Assumptions.tcLd, Assumptions.commitOrder, Assumptions.pollAgree]

/-- The assumptions before the software `exp2`. -/
abbrev front : List Assumption :=
  [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.approx]

/-- The assumptions after the software `exp2`. -/
abbrev back : List Assumption :=
  [Assumptions.peerBit, Assumptions.tcLd, Assumptions.commitOrder, Assumptions.pollAgree]

/-- Outside the software `exp2` and peer-bit sites no assumption takes a segment. -/
theorem segFree_rest {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false) :
    Assumption.SegFreePc rest pc := by
  simp only [Bool.or_eq_false_iff] at h
  refine .cons (fun _ _ _ _ => rfl) (.cons (fun _ _ _ _ => rfl)
    (.cons (Assumption.segmentExact_segFreePc h.1) (.cons (Assumption.pairEvenAt_segFreePc h.2)
    ?_)))
  repeat' first | exact .nil | refine .cons (fun _ _ _ _ => rfl) ?_

/-- The same for a range of program counters. -/
theorem segFree_range {pc n : Nat}
    (h : (List.range n).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true) :
    ∀ k < n, Assumption.SegFreePc rest (pc + k) := by
  intro k hk
  refine segFree_rest ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using this

/-- The assumptions before the software `exp2` take no segment. -/
theorem segFree_front (pc : Nat) : Assumption.SegFreePc front pc :=
  .cons (fun _ _ _ _ => rfl) (.cons (fun _ _ _ _ => rfl) (.cons (fun _ _ _ _ => rfl) .nil))

/-- The ideal reading of a form of `idealArith` at a program counter outside the segment
sites. -/
theorem ideal_at {L : Launch} {g : Nat} {f : Assumption.FloatForm}
    (hf : f ∈ ([.add .f32, .mul .f32, .subRn .f32, .addRnF32x2, .subRnF32x2, .fmaRnF32x2,
      .mulF32x2, .max .f32, .setp .f32, .setpInf .f32, .cvtRnF16x2F32] :
      List Assumption.FloatForm)) {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false) :
    ∀ t : TState, t.pc = pc → Assumption.IdealAt asms f L g t :=
  fun _ ht => Assumption.idealAt_head (A' := rest) hf (ht ▸ segFree_rest h)

/-- The first column of the masked tile: the first tile's columns start at
`kv = sk - 128 · max (n - 1, 0)` (`max.s32`, `shl.b32 …, 7`, `sub.s32`), which is `128` when the
`n` tiles of `128` keys cover `sk` exactly; the mask of each word of 32 columns is then all
ones. -/
theorem mask_base (x y : Nat) (hx : x < 2 ^ 31) (hy : x = 128 * (y + 1)) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) - truncBits 32
      (if (truncBits 32 (BitVec.ofInt 64 7)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32
        (if compare (if True then Cmp.gt else Cmp.lt) (if True then IType.s else IType.u) 32
          (truncBits 32 (BitVec.ofNat 64 y)) (truncBits 32 (BitVec.ofInt 64 0)) = true then
            truncBits 32 (BitVec.ofNat 64 y) else truncBits 32 (BitVec.ofInt 64 0)) <<<
          (truncBits 32 (BitVec.ofInt 64 7)).toNat)))) = b32 128 := by
  nf_simp [PTX.compare, toSigned]
  split_ifs
  all_goals (simp only [decide_eq_true_eq] at *; nf_simp)
  all_goals omega

/-- The number of `0fC1000000`, the threshold of the lazy rescale. -/
theorem neg8 : valFloat .f32 (.bits 32 (BitVec.ofNat 64 3238002688)) = .ok (-8) := by
  have h : f32Value 3238002688 = some (-8) := by
    simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
      Layout.magnitude, Layout.bias, Layout.width, FVal.num]
    norm_num
  simpa [b32] using valFloat_b32 (by norm_num) h

/-- The address of the thread's statistics word: `sb + ((128 st | (tid & 127)) << 2)` is
`sb + 4 tid` for the stage `st = tid / 128` of a thread of the 512-thread block. -/
theorem alpha_addr (b x : Nat) (hx : x < 512) (hb : b + 232448 ≤ 2 ^ 18) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (b + 0)) + truncBits 32
      (if (truncBits 32 (BitVec.ofInt 64 2)).toNat ≥ 32 then 0 else truncBits 32 (truncBits 32
        (truncBits 32 (BitVec.ofNat 64 (128 * (x / 32 / 4))) ||| truncBits 32
          (truncBits 32 (BitVec.ofNat 64 x) &&& truncBits 32 (BitVec.ofInt 64 127))) <<<
        (truncBits 32 (BitVec.ofInt 64 2)).toNat)))) = b32 (b + 4 * x) := by
  have hm : x % 4294967296 = x := Nat.mod_eq_of_lt (by omega)
  have h128 : 128 * (x / 32 / 4) % 4294967296 = 128 * (x / 32 / 4) := Nat.mod_eq_of_lt (by omega)
  have hand : x &&& 127 = x % 128 := by
    rw [show (127 : Nat) = 2 ^ 7 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : x % 128 % 4294967296 = x % 128 := Nat.mod_eq_of_lt (by omega)
  have hor : 128 * (x / 32 / 4) ||| x % 128 = x := by
    rw [lor_eq_add (k := 7) (by omega) (by omega)]; omega
  have hm' : x % 18446744073709551616 = x := Nat.mod_eq_of_lt (by omega)
  have h128' : 128 * (x / 32 / 4) % 18446744073709551616 = 128 * (x / 32 / 4) :=
    Nat.mod_eq_of_lt (by omega)
  have hx' : x % 4294967296 % 18446744073709551616 = x := by omega
  have h2' : x % 128 % 18446744073709551616 = x % 128 := Nat.mod_eq_of_lt (by omega)
  nf_simp [hm, h128, hand, h2, hor, hm', h128', hx', h2']
  omega

/-- Close one equation between a computed and a stated value of a register. -/
syntax "ar_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ar_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | with_reducible rfl
      | exact mask_base _ _ ‹skOf _ < 2 ^ 31› ‹skOf _ = 128 * (trips _ - 1 + 1)›
      | (simp only [erealCompare_ne_bot]; done)
      | (simp only [negM, joinValue]
         norm_num [FloatFmt.magnitude, FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.bias]; done)
      | rfl
      | close_fact [$extra,*])

/-- Evaluate a piece from `h`, closing the written values by `ar_close`. -/
syntax "ar_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ar_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
        try simp only [valueEx, valueX, valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, List.lookup_cons, List.lookup_nil, Nat.reduceBEq]
        all_goals ar_close [$extra,*])

/-- `ar_seg` with a first closer: `simp only` with the given lemmas, else the tactic `tac`. -/
syntax "ar_seg_with " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" " using " tactic : tactic
macro_rules
  | `(tactic| ar_seg_with $h [$ls,*] using $tac) =>
    `(tactic| seg_fp $h using
        try simp only [valueEx, valueX, valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, List.lookup_cons, List.lookup_nil, Nat.reduceBEq,
          Prologue.sb]
        all_goals first
          | (simp only [$ls,*]; done)
          | ($tac:tactic)
          | ar_close)

/-- No assumption takes a segment in a range of program counters outside the software `exp2`
and peer-bit sites. -/
theorem segFree_asms {pc n : Nat}
    (h : (List.range n).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true) :
    ∀ k < n, Assumption.SegFreePc asms (pc + k) :=
  fun k hk => segFree_ideal (segFree_range h k hk)

/-- The ideal reading of `max.f32` in a range of program counters outside the segment
sites. -/
theorem ideal_max_range {L : Launch} {g : Nat} {pc n : Nat}
    (h : (List.range n).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true) :
    ∀ k < n, ∀ t : TState, t.pc = pc + k → Assumption.IdealAt asms (.max .f32) L g t :=
  fun k hk => ideal_at (by decide) (by simpa using List.all_eq_true.mp h k (List.mem_range.mpr hk))

/-- No assumption has a local rule for an item of a read run other than a `max.f32`. -/
theorem noItemRule_asms (items : List RItem) : NoItemRule asms items :=
  fun it _ hm _ _ _ => asms_localRule_none (it.floatForm_none hm) it.approxForm_none

/-- Outside the segment sites a declined `max.f32` takes the Core rule: no assumption after the
ideal arithmetic names it. -/
theorem decline_max_range {L : Launch} {g : Nat} {pc n : Nat}
    (h : (List.range n).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true) :
    ∀ k < n, ∀ t : TState, t.pc = pc + k → DeclineAt asms (.max .f32) L g t := by
  intro k hk t ht
  refine declineAt_head (A' := rest) (fun a ha op hf => ?_) (ht ▸ segFree_range h k hk)
  simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact Assumption.approxExact_localRule_none fun f h' => by
      rw [approxForm_none_of_max hf] at h'; cases h'
  all_goals rfl

/-! ### Outcome runs and pieces -/

/-- No assumption takes a segment at a program counter outside the segment sites. -/
theorem segFree_pc {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false) :
    Assumption.SegFreePc asms pc :=
  segFree_ideal (segFree_rest h)

/-- Outside the segment sites a declined floating form takes the Core rule: no assumption after
the ideal arithmetic names it. -/
theorem declineAt_pc {L : Launch} {g : Nat} {f : Assumption.FloatForm} {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false) :
    ∀ t : TState, t.pc = pc → DeclineAt asms f L g t := by
  intro t ht
  refine declineAt_head (A' := rest) (fun a ha op hf => ?_) (ht ▸ segFree_rest h)
  simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact Assumption.approxExact_localRule_none fun f' h' => by
      rw [approxForm_none_of_float hf] at h'; cases h'
  all_goals rfl

/-- Outside the segment sites `ex2.approx.f32` is the exact power of two (ASM-APPROX) on a
finite operand and takes the Core rule on another. -/
theorem approxAt_pc {L : Launch} {g : Nat} {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false) :
    ∀ t : TState, t.pc = pc →
      ApproxAt asms (.ex2 .f32) L g t ∧ ApproxDeclineAt asms (.ex2 .f32) L g t := by
  intro t ht
  have key : ∀ op, Assumption.ApproxForm.ofOp op = some (.ex2 .f32) →
      execLocalA asms L g t op = match Assumption.execApproxExact t op with
        | some r => r
        | none => execLocal L g t op := by
    intro op hf
    rw [(segFree_pc h).exec ht]
    have h1 : Assumptions.idealArith.localRule L g t op = none :=
      Assumption.idealReal_localRule_none fun f' h' => by
        rw [Flow.floatForm_none_of_approx hf] at h'; cases h'
    have h3 : Assumptions.approx.localRule L g t op = Assumption.execApproxExact t op :=
      Assumption.approxExact_localRule_of hf (by simp)
    simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h3]
    rcases Assumption.execApproxExact t op with _ | r <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he], fun op hf he => by rw [key op hf, he]⟩

/-- Outside the segment sites the assumptions do with every item what `OItem.Rule` says. -/
theorem rule_pc {L : Launch} {g : Nat} {pc : Nat}
    (h : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) = false)
    (it : OItem) : ∀ t : TState, t.pc = pc → it.Rule asms L g t := by
  intro t ht
  cases it with
  | movImm d b =>
    exact asms_localRule_none (by simp [OItem.op, Assumption.FloatForm.ofOp])
      (by simp [OItem.op, Assumption.ApproxForm.ofOp])
  | mov d a =>
    exact asms_localRule_none (by simp [OItem.op, Assumption.FloatForm.ofOp])
      (by simp [OItem.op, Assumption.ApproxForm.ofOp])
  | pack d a b =>
    exact asms_localRule_none (by simp [OItem.op, Assumption.FloatForm.ofOp])
      (by simp [OItem.op, Assumption.ApproxForm.ofOp])
  | unpack lo hi a =>
    exact asms_localRule_none (by simp [OItem.op, Assumption.FloatForm.ofOp])
      (by simp [OItem.op, Assumption.ApproxForm.ofOp])
  | selp d a b p =>
    exact asms_localRule_none (by simp [OItem.op, Assumption.FloatForm.ofOp])
      (by simp [OItem.op, Assumption.ApproxForm.ofOp])
  | fma2 => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | add2 => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | ex2 => exact approxAt_pc h t ht
  | cvt => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | mul => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | sub => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | add => exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
  | setp c fz p a k =>
    simp only [OItem.Rule, setpForm]
    split
    · exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩
    · exact ⟨ideal_at (by decide) h t ht, declineAt_pc h t ht⟩

/-- A run outside the segment sites meets `ORules`. -/
theorem orules_asms {L : Launch} {g : Nat} : ∀ (pc : Nat) (items : List OItem),
    (List.range items.length).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true → ORules asms L g pc items
  | _, [], _ => trivial
  | pc, it :: its, h => by
    have hall := List.all_eq_true.mp h
    have h0 : (Assumptions.swExp2Sites.contains pc || Assumptions.peerBitSites.contains pc) =
        false := by
      simpa using hall 0 (List.mem_range.mpr (by simp))
    refine ⟨⟨segFree_pc h0, rule_pc h0 it⟩, orules_asms (pc + 1) its ?_⟩
    refine List.all_eq_true.mpr fun k hk => ?_
    have := hall (k + 1) (List.mem_range.mpr (by simp at hk ⊢; omega))
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- A piece between the facts by `V` at its `pc` and the facts after it, under its condition. -/
def PieceSeg (L : Launch) (g pc : Nat) (V : Nat → Value) (p : Piece) : Prop :=
  SegD kernel asms L g p.len pc (factsFrom (Flow.live pc) V) (p.stop pc)
    (factsFrom (Flow.live (p.stop pc)) (p.apply V)) (p.cond V)

/-- Each piece of a list between its facts. -/
def ChainSeg (L : Launch) (g : Nat) : Nat → (Nat → Value) → List Piece → Prop
  | _, _, [] => True
  | pc, V, p :: ps => PieceSeg L g pc V p ∧ ChainSeg L g (p.stop pc) (p.apply V) ps

/-- **A list of pieces, as a piece**, under the conjunction of their conditions. -/
theorem chain_seg {L : Launch} {g : Nat} : ∀ (ps : List Piece) (pc : Nat) (V : Nat → Value),
    ChainSeg L g pc V ps →
    SegD kernel asms L g (chainLen ps) pc (factsFrom (Flow.live pc) V) (chainStop pc ps)
      (factsFrom (Flow.live (chainStop pc ps)) (chainV V ps)) (chainCond V ps)
  | [], _, _, _ => SegD.of_seg fun t h => ⟨t, rfl, h⟩
  | _ :: ps, _, _, ⟨h1, h2⟩ => SegD.comp h1 (chain_seg ps _ _ h2)

theorem chainSeg_append {L : Launch} {g : Nat} : ∀ (ps qs : List Piece) (pc : Nat)
    (V : Nat → Value), ChainSeg L g pc V ps →
    ChainSeg L g (chainStop pc ps) (chainV V ps) qs → ChainSeg L g pc V (ps ++ qs)
  | [], _, _, _, _, h => h
  | _ :: ps, qs, _, _, ⟨h1, h2⟩, h => ⟨h1, chainSeg_append ps qs _ _ h2 h⟩

/-- A run outside the segment sites, as a piece. -/
theorem pieceSeg_run {L : Launch} {g pc : Nat} {V : Nat → Value} {items : List OItem}
    (hcode : oCodeB kernel pc items = true) (hreads : oReadsB (Flow.live pc) items = true)
    (hreq : oReq V items = true) (hloc : oLocalB items = true)
    (hfree : (List.range items.length).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true)
    (hcov : ∀ r ∈ Flow.live (pc + items.length), r ∈ oWrites items ∨ r ∈ Flow.live pc) :
    PieceSeg L g pc V (.run items) :=
  SegD.outs hcode hreads hreq hloc (orules_asms pc items hfree) hcov

/-- An instance of the software `exp2`, as a piece. -/
theorem pieceSeg_sw {L : Launch} {g pc : Nat} {V : Nat → Value}
    {m : Assumption.SegMatch Assumption.CuteSlot} {op : Op}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hs : Assumptions.swExp2Sites.contains pc = true)
    (hm : Assumption.cuteExp2.matchAt kernel pc = some m)
    (hio : m.shape.io = [(.x0, .y0), (.x1, .y1)])
    (hcst : m.shape.defines = true ∨ ((∀ p ∈ m.shape.consts, m.regOf p.1 ∈ Flow.live pc) ∧
      m.shape.consts.map (fun p => V (m.regOf p.1)) = m.shape.consts.map Prod.snd))
    (hi₀ : m.regOf .x0 ∈ Flow.live pc) (hi₁ : m.regOf .x1 ∈ Flow.live pc)
    (hnd : (segKeys m .y0 .y1).Nodup)
    (hcov : ∀ r ∈ Flow.live m.stop, r ∈ segKeys m .y0 .y1 ∨
      (r ∉ segKeys m .y0 .y1 ++ m.shape.writes.map m.regOf ∧ r ∈ Flow.live pc)) :
    PieceSeg L g pc V (.sw m) :=
  SegD.segTwo (T := Assumption.cuteExp2) (a := Assumptions.swExp2) (A₁ := front) (A₂ := back)
    rfl rfl hc hl hs hm hio hcst hi₀ hi₁ hnd hcov (segFree_front pc)

/-- Fewer live registers at the start. -/
theorem holds_live_sub {R : Nat → Option Value} {l l' : List Nat} {V : Nat → Value}
    (hl : ∀ r ∈ l', r ∈ l) (h : Holds R (factsFrom l V)) : Holds R (factsFrom l' V) :=
  holds_of_pointwise fun r hr => holds_mem h (mem_factsFrom (hl r hr))

/-- Facts by value functions that agree on the live registers. -/
theorem holds_live_congr {R : Nat → Option Value} {l : List Nat} {V W : Nat → Value}
    (he : l.map V = l.map W) (h : Holds R (factsFrom l V)) : Holds R (factsFrom l W) :=
  factsFrom_congr he ▸ h

/-- A pack of two conversions is accepted by the unpack. -/
theorem unpackOk_cvt (a b c e : Value) : UnpackOk (joinValue (cvtV a b) (cvtV c e)) :=
  unpackOk_join (okVal_cvtPairE_bytes a b) (okVal_cvtPairE_bytes c e) (okVal_cvtPairE_ns a b)

/-- A run that meets its condition, as a piece between facts by the table: the values after it
are those of `W` on the live registers. -/
theorem seg_outs {L : Launch} {g pc : Nat} {liveS : List Nat} {V W : Nat → Value}
    {items : List OItem} (hcode : oCodeB kernel pc items = true)
    (hreads : oReadsB liveS items = true) (hreq : oReq V items = true)
    (hloc : oLocalB items = true)
    (hfree : (List.range items.length).all (fun k => !(Assumptions.swExp2Sites.contains (pc + k) ||
      Assumptions.peerBitSites.contains (pc + k))) = true)
    (hcov : ∀ r ∈ Flow.live (pc + items.length), r ∈ oWrites items ∨ r ∈ liveS)
    (hok : oCond V items)
    (hfin : (Flow.live (pc + items.length)).map (oFinal V items) =
      (Flow.live (pc + items.length)).map W) :
    Seg kernel asms L g items.length pc (factsFrom liveS V) (pc + items.length)
      (factsFrom (Flow.live (pc + items.length)) W) :=
  ((SegD.outs hcode hreads hreq hloc (orules_asms pc items hfree) hcov).weaken_end
    fun _ h => holds_live_congr hfin h).seg hok

/-- The condition of a run of unpacks of packed conversions (by the items' membership). -/
macro "unpacks_ok" : tactic => `(tactic| (
  refine oCond_unpacks _ fun it hit => ?_
  simp only [pst0a, pst0b, pst0c, pst1a, pst1b, pst1c, List.mem_cons, List.not_mem_nil,
    or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, by decide, by
      simp only [valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit, Option.getD_some]
      exact unpackOk_cvt _ _ _ _⟩))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
