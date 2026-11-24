-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerNumeric
public import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
noncomputable section

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- An aligned peer load can only read one element of the shared vector. -/
theorem fired_peer_load {A : List Assumption} {L : Launch} {g pc base a off d0 d1 : Nat}
    {t : TState} {o : Option TState} {e : Event}
    (hr : t.regs base = some (b32 a)) (hal : (a + off) % 16 = 0) (ha : a + off < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 64,
        vec := 2, addr := ⟨.reg base 32, (off : Int)⟩, dsts := [some d0, some d1] })) e
        o) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧ ac.loc = ⟨.shared, g / L.block, a + off + 8 * t.sub⟩ ∧
      ac.size = 8 ∧ o = some (afterLoad t [d0, d1] bs) := by
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32)
    rfl rfl rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl, effAddr_b32_off hr ha, bind, Except.bind,
    Bool.false_eq_true, ↓reduceIte] at hf
  rw [elemAcc_ok (by decide) (by simpa using hal)] at hf
  obtain ⟨bs, hlen, he, hu⟩ := hf
  exact ⟨_, bs, he, by simp [Loc.at], rfl, hu⟩

private def peerLive (pc : Nat) : List Nat :=
  (Flow.live pc).filter (fun r => tracked.contains r)

private def peerFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) :
    List (Nat × Value) :=
  factsFrom (peerLive pc) (valueOf P L g d)

private theorem ownMasked_bytes {d : D} (h : exchangeReady d = true) (j : Nat) :
    (ownMaskedValue d j).bytes = 4 := by
  have hgood := (Bool.and_eq_true_iff.mp h).1
  have hget : Assumptions.scoreHalf (d.ownScores.getD j (b32 0)) := by
    rcases he : d.ownScores[j]? with _ | v
    · rw [List.getD_eq_getElem?_getD, he]
      change (0 : Nat) < 2 ^ 32
      decide
    · rw [List.getD_eq_getElem?_getD, he]
      have hv := List.mem_of_getElem? he
      exact of_decide_eq_true (List.all_eq_true.mp hgood v hv)
  unfold ownMaskedValue
  split
  · exact Assumptions.scoreHalf_bytes hget
  · rfl

private theorem peer_move_local {L : Launch} {g : Nat} {t : TState} {m : MoveInstr}
    (hpc : 474 ≤ t.pc ∧ t.pc < 566) :
    execLocalA asms L g t (.move m) = execLocal L g t (.move m) := by
  have hp : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hf : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hd : deadPackWords t.pc = none := by
    unfold deadPackWords
    split <;> first | rfl | omega
  rw [execLocalA_noSegment (Proof.asms_segment_free t),
    execLocalRule_of_none (Thread.asms_localRule_move hp hf hd)]

private theorem run_peer_pack {L : Launch} {g : Nat} {t : TState} {pc dst lo hi : Nat}
    {F : List (Nat × Value)} {a b : Value}
    (hc : kernel.code[pc]? = some
      ⟨none, .move ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩⟩)
    (h : At t pc F) (hl : t.regs lo = some a) (hh : t.regs hi = some b)
    (ha : a.bytes = 4) (hb : b.bytes = 4)
    (hp : 474 ≤ pc ∧ pc < 566) (hframe : ∀ p ∈ F, p.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (pc + 1) ((dst, joinValue a b) :: F) := by
  have hx : execLocalA asms L g t (.move ⟨.pack, .int .b 64, [some dst], [.reg lo, .reg hi]⟩) =
      .ok (PTX.next (setReg t dst (joinValue a b))) := by
    rw [peer_move_local (by rw [h.1]; exact hp), execLocal_move (by rfl)]
    simp [execMove, DType.width, readValue, readReg, hl, hh, ha, hb,
      bind, Except.bind, pure, Except.pure]
  exact ⟨_, run_local hc rfl h hx, h.set hframe⟩

variable {P : Params} {L : Launch}

private theorem peerFacts_dest {g pc : Nat} {d : D} {t : TState} {dst : Nat} {v : Value}
    {F : List (Nat × Value)} (h : At t pc ((dst, v) :: F))
    (hF : ∀ r ∈ peerLive pc, r ≠ dst → (r, valueOf P L g d r) ∈ F) (hv : valueOf P L g d dst = v) :
    At t pc (peerFacts P L g d pc) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  apply holds_of_pointwise
  intro r hr
  by_cases he : r = dst
  · subst r
    rw [hv]
    exact h.2.2.2.2.1
  · exact holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (hF r hr he))

/-- The pair's named barrier orders the preceding writes before the first peer read. -/
theorem step_pairBar {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (d : D) (hd : d.site = .pairBar)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hsite : d.site.pc = 475 := by rw [hd]; rfl
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hinv.subLt
  have hr996 : t.regs 996 = some (b32 (10 + warpOf L g % 2)) :=
    reg_value hat (by rw [hsite]; decide +kernel)
  have hr997 : t.regs 997 = some (b32 64) := reg_value hat (by rw [hsite]; decide +kernel)
  have idLt : 10 + warpOf L g % 2 < 16 := by omega
  have h996 := readBits_b32 (L := L) (g := g) hr996 (by omega)
  have h997 := readBits_b32 (L := L) (g := g) hr997 (by decide : 64 < 2 ^ 32)
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_475)
  have hbar : eventTmpl asms L g t (.barSyncN (.reg 996) (.reg 997) true) =
      .bar (10 + warpOf L g % 2) (PTX.next t) (some 64) .sync := by
    have h64 : 10 + warpOf L g % 2 < 18446744073709551616 := by omega
    simp [eventTmpl, barTmpl, h996, h997, hpre.block, Nat.mod_eq_of_lt h64,
      Nat.not_le.mpr idLt]
  rw [hbar] at hf
  obtain ⟨he, hu⟩ := hf
  have hu' := Option.some.inj hu
  subst u
  let d' := { d with site := Site.peerRead 0, sub := 0 }
  have hready := hinv.exchangeWords (by rw [hd]; rfl)
  have hat' : At (PTX.next t) 476 (peerFacts P L g d 475) := at_next_of hat hsite hsub
  have ha : (PTX.next t).regs 1009 = some (ownMaskedValue d 0) := by
    exact reg_value hat (by rw [hsite]; decide +kernel)
  have hb : (PTX.next t).regs 1010 = some (ownMaskedValue d 1) := by
    exact reg_value hat (by rw [hsite]; decide +kernel)
  have hne : ∀ p ∈ peerFacts P L g d 475, p.1 ≠ 3145 :=
    fun p hp eq => by
      obtain ⟨r, hr, he⟩ := List.mem_map.mp hp
      have hir : r = 3145 := (congrArg Prod.fst he).trans eq
      subst r
      exact (by decide +kernel : 3145 ∉ peerLive 475) hr
  obtain ⟨v, hr, hv⟩ := run_peer_pack (L := L) (g := g) Flow.code_476 hat' ha hb
    (ownMasked_bytes hready 0) (ownMasked_bytes hready 1) (by decide) hne
  have htab : valueOf P L g d' = valueOf P L g d := rfl
  have hcover : ∀ r ∈ peerLive 477, r ∈ 3145 :: peerLive 475 := by lit_mem
  have hv' : At v 477 (peerFacts P L g d' 477) := by
    apply peerFacts_dest (d := d') hv ?_ rfl
    intro r hmem hne
    rw [htab]
    have hm := List.mem_cons.mp (hcover r hmem)
    exact mem_factsFrom (hm.resolve_left hne)
  refine .inl (.inr ⟨d', v, by simp [next, nextSite, hd, he, d', hsub], run_rtg hr, ?_, ?_⟩)
  · exact ⟨hv'.1, hv'.2.1, hv'.2.2.1.trans (siteAcc_nil d' rfl).symm,
      hv'.2.2.2.1, hv'.2.2.2.2⟩
  · exact inv_setSite hinv (.peerRead 0) (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
      (by simp) (by simp) (by simp) (by simp [Site.needsRowTotal]) (fun _ => hready)

/-- The concrete vector instruction of each peer-read site. -/
private def peerLoadOp (i : Fin 8) : Op :=
  .mem {
    kind := .load
    space := some (.shared .cta)
    sem := .weak
    elem := .int .b 64
    vec := 2
    addr := ⟨.reg 475 32, (exchangeBase + exchangeChunk * i.val : Nat)⟩
    dsts := [some (3146 + 4 * i.val), some (3148 + 4 * i.val)] }

private theorem peerLoad_code (i : Fin 8) :
    kernel.code[(Site.peerRead i).pc]? = some ⟨none, peerLoadOp i⟩ := by
  fin_cases i <;> first
    | exact Flow.code_477
    | exact Flow.code_482
    | exact Flow.code_487
    | exact Flow.code_492
    | exact Flow.code_497
    | exact Flow.code_502
    | exact Flow.code_507
    | exact Flow.code_512

/-- A peer-score load can only read the specified eight-byte element. -/
theorem fired_peerRead_at {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {o : Option TState}
    {i : Fin 8} {ins : Instr} {e : Event} (hpre : Pre P L mem0) (hd : d.site = .peerRead i)
    (hi : Inv P L g d) (hat : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ac bytes, e.kind = .rd ac bytes ∧
      siteLoc L g d.site d.block d.sub = some ac.loc ∧ ac.size = d.site.elemBytes ∧
      o = some (afterLoad t [3146 + 4 * i.val, 3148 + 4 * i.val] bytes) := by
  have hins : ins = ⟨none, peerLoadOp i⟩ := by
    rw [hd] at hc
    exact Option.some.inj (hc.symm.trans (peerLoad_code i))
  subst ins
  let base := L.sharedBase + (4096 * warpOf L g + 16 * laneOf L g)
  have hbase : t.regs 475 = some (b32 base) := by
    apply reg_value hat
    rw [hd]
    fin_cases i <;> decide +kernel
  have hwin := sharedBase_lt hpre
  have hw := hi.warpLt
  have hl := hi.laneLt
  have hidx := i.isLt
  have haddr : base + (exchangeBase + exchangeChunk * i.val) < 2 ^ 32 := by
    dsimp [base, exchangeBase, exchangeChunk]
    omega
  have hal : (base + (exchangeBase + exchangeChunk * i.val)) % 16 = 0 := by
    have h1024 : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
    dsimp [base, exchangeBase, exchangeChunk]
    omega
  obtain ⟨ac, bytes, he, hloc, hsize, hu⟩ := fired_peer_load hbase hal haddr hf
  refine ⟨ac, bytes, by rw [he], ?_, ?_, hu⟩
  · rw [hd, hloc, hat.2.1]
    have hadd : L.sharedBase + (exchangeBase + exchangeQuad * warpOf L g +
        16 * laneOf L g + exchangeChunk * i.val + 8 * d.sub) =
        base + (exchangeBase + exchangeChunk * i.val) + 8 * d.sub := by
      dsimp [base, exchangeBase, exchangeQuad, exchangeChunk]
      omega
    change some (Loc.mk .shared (g / L.block) _) = some (Loc.mk .shared (g / L.block) _)
    rw [hadd]
    rfl
  · rw [hsize, hd]
    rfl

/-- A fired peer read is the specified eight-byte access, and rebuilds into the concrete load. -/
theorem fires_peerRead_at {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {i : Fin 8} {ins : Instr}
    {e : Event} (hpre : Pre P L mem0) (hd : d.site = .peerRead i) (hi : Inv P L g d)
    (hat : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ ac bytes, e.kind = .rd ac bytes ∧
      siteLoc L g d.site d.block d.sub = some ac.loc ∧ ac.size = d.site.elemBytes ∧
      u = afterLoad t [3146 + 4 * i.val, 3148 + 4 * i.val] bytes := by
  obtain ⟨ac, bs, he, hl, hs, hu⟩ := fired_peerRead_at hpre hd hi hat hc hf
  exact ⟨ac, bs, he, hl, hs, Option.some.inj hu⟩

private theorem peer_noSegments : NoSegments asms :=
  fun a ha _ _ t => Proof.asms_segment_free t a ha

private theorem peer_ideal {f : FloatForm}
    (hf : f = .addRnF32x2 ∨ f = .max .f32 ∨ f = .mul .f32) : IdealFor asms f := by
  rcases hf with rfl | rfl | rfl
  all_goals
    exact idealFor_head (by simp) peer_noSegments.tail

private theorem peer_float_shape {op : Op}
    (hf : FloatForm.ofOp op = some .addRnF32x2 ∨
          FloatForm.ofOp op = some (.max .f32) ∨ FloatForm.ofOp op = some (.mul .f32)) :
    ∃ i : FloatInstr, op = .float i ∧
      (i.op = .add ∨ i.op = .max ∨ i.op = .mul ∧ i.ty.lanes = 1) := by
  cases op with
  | float i =>
    refine ⟨i, rfl, ?_⟩
    cases hi : i.op <;> simp [FloatForm.ofOp, hi] at hf ⊢
    all_goals repeat' split at hf
    all_goals simp_all
  | cvt c =>
    simp only [FloatForm.ofOp] at hf
    split_ifs at hf <;> simp_all
  | _ => simp [FloatForm.ofOp] at hf

private theorem peer_decline {L : Launch} {g : Nat} {t : TState} {f : FloatForm}
    (hf : f = .addRnF32x2 ∨ f = .max .f32 ∨ f = .mul .f32) :
    DeclineAt asms f L g t := by
  apply declineAt_head
  · intro a ha op hform
    have hs : FloatForm.ofOp op = some .addRnF32x2 ∨
        FloatForm.ofOp op = some (.max .f32) ∨ FloatForm.ofOp op = some (.mul .f32) := by
      rcases hf with rfl | rfl | rfl <;> simp [hform]
    obtain ⟨i, rfl, ht⟩ := peer_float_shape hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases ht with h | h | ⟨h, _⟩ <;> simp [approx, approxExact, ApproxForm.ofOp, h]
    · rcases ht with h | h | ⟨h, hl⟩
      · simp [mulBf16x2, h]
      · simp [mulBf16x2, h]
      · cases hty : i.ty
        simp_all [mulBf16x2]
    · rfl
    · rfl
    · rcases ht with h | h | ⟨h, _⟩ <;> simp [lg2Exact, h]
    · rfl
    · simp [paramPointers]
    · rfl
    · simp [sharedBits, deadPackRule, peerPackRule]
    · rfl
  · exact peer_noSegments.tail.segFreePc


private abbrev peerAddOp (dst a b : Nat) : Op :=
  .float { peerAddI with dsts := [some dst], srcs := [.reg a, .reg b] }

private theorem run_peer_add {L : Launch} {g : Nat} {t : TState} {pc dst a b : Nat}
    {F : List (Nat × Value)} {va vb v : Value}
    (hc : kernel.code[pc]? = some ⟨none, peerAddOp dst a b⟩) (h : At t pc F)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (hv : peerAddE va vb = .ok v)
    (hf : ∀ p ∈ F, p.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) ((dst, v) :: F) := by
  have hex : execLocalA asms L g t (peerAddOp dst a b) =
      .ok (PTX.next (setReg t dst v)) := by
    rw [exec_peerAddE (peer_ideal (.inl rfl)).at (peer_decline (.inl rfl)) ha hb, hv]
    rfl
  exact ⟨_, run_local hc rfl h hex, h.set hf⟩

private theorem run_peer_max {L : Launch} {g : Nat} {t : TState} {pc dst : Nat}
    {a b : Opnd} {F : List (Nat × Value)} {va vb v : Value}
    (hc : kernel.code[pc]? = some ⟨none, peerMaxOp dst a b⟩) (h : At t pc F)
    (ha : readValue L g t 32 a = .ok va) (hb : readValue L g t 32 b = .ok vb)
    (ha' : readERealOpnd t .f32 a = readEReal .f32 va)
    (hb' : readERealOpnd t .f32 b = readEReal .f32 vb)
    (hv : peerMaxE va vb = .ok v)
    (hf : ∀ p ∈ F, p.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) ((dst, v) :: F) := by
  have hex : execLocalA asms L g t (peerMaxOp dst a b) =
      .ok (PTX.next (setReg t dst v)) := by
    rw [exec_peerMaxE (peer_ideal (.inr (.inl rfl))).at (peer_decline (.inr (.inl rfl)))
      ha hb ha' hb', hv]
    rfl
  exact ⟨_, run_local hc rfl h hex, h.set hf⟩

private theorem run_peer_unpack {L : Launch} {g : Nat} {t : TState} {pc lo hi src : Nat}
    {F : List (Nat × Value)} {v a b : Value}
    (hc : kernel.code[pc]? = some
      ⟨none, .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg src]⟩⟩)
    (h : At t pc F) (hv : t.regs src = some v) (hu : unpackE 64 v = .ok (a, b))
    (hp : 474 ≤ pc ∧ pc < 566) (hlo : ∀ p ∈ F, p.1 ≠ lo)
    (hhi : ∀ p ∈ F, p.1 ≠ hi) (hne : lo ≠ hi) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) ((lo, a) :: (hi, b) :: F) := by
  have hbytes : v.bytes = 8 ∧ (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4 := by
    unfold unpackE at hu
    split at hu
    · assumption
    · cases hu
  have hsplit : splitValue 64 v = (a, b) := by
    simpa [unpackE, hbytes.1, hbytes.2.1, hbytes.2.2] using hu
  let t' := PTX.next (setReg (setReg t lo a) hi b)
  have hx : execLocalA asms L g t (.move ⟨.unpack, .int .b 64,
        [some lo, some hi], [.reg src]⟩) = .ok t' := by
    rw [peer_move_local (by rw [h.1]; exact hp), execLocal_move (by rfl)]
    simp [execMove, DType.width, readValue, readReg, hv, hbytes.1, hsplit, t',
      show a.bytes = 4 by simpa [hsplit] using hbytes.2.1,
      show b.bytes = 4 by simpa [hsplit] using hbytes.2.2,
      bind, Except.bind, pure, Except.pure]
  refine ⟨_, run_local hc rfl h hx, h.1 ▸ rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  exact ⟨by simp [t', PTX.next, setReg, Function.update_of_ne hne],
    by simp [t', PTX.next, setReg], holds_update (holds_update h.2.2.2.2 hlo) hhi⟩


/-- The first element leaves both destinations untouched and carries exactly one rebuilt word. -/
theorem peerRead_low {g : Nat} {d : D} {t : TState} {i : Fin 8} {bytes : List (Option Byte)}
    {word : Value} (hd : d.site = .peerRead i) (hs : d.sub = 0) (hi : Inv P L g d)
    (ht : (code P L g).AtD d t) (hr : rebuild 3 bytes = .ok word) :
    (code P L g).Good (some { d with sub := 1, peerPending := [word] })
      (afterLoad t [3146 + 4 * i.val, 3148 + 4 * i.val] bytes) := by
  have hsub : t.sub = 0 := ht.2.1.trans hs
  have hacc : t.acc = [] := ht.2.2.1.trans (siteAcc_nil d hs)
  rw [afterLoad_mid hr (by simp [hsub])]
  refine ⟨⟨ht.1, by change t.sub + 1 = 1; omega, ?_, ht.2.2.2.1, ht.2.2.2.2⟩,
    { hi with subLt := ?_ }⟩
  · change t.acc ++ [word] = siteAcc _
    simp [hacc, siteAcc, hd]
  · simp [hd, Site.elems]

private theorem peer_fact {g pc r : Nat} {d : D} (h : r ∈ peerLive pc)
    : (r, valueOf P L g d r) ∈ peerFacts P L g d pc :=
  mem_factsFrom h

private theorem peer_fresh {g pc r : Nat} {d : D} (hr : r ∉ peerLive pc)
    : ∀ p ∈ peerFacts P L g d pc, p.1 ≠ r := by
  intro p hp he
  obtain ⟨j, hj, eq⟩ := List.mem_map.mp hp
  exact hr (((congrArg Prod.fst eq).trans he) ▸ hj)

private abbrev peerPC (i : Fin 8) : Nat := (Site.peerRead i).pc

private abbrev sumLow (i : Fin 8) : Nat := scoreSumRegs.getD (2 * i.val) 0
private abbrev sumHigh (i : Fin 8) : Nat := scoreSumRegs.getD (2 * i.val + 1) 0

private theorem valueOf_pack (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8) :
    valueOf P L g d (3145 + 4 * i.val) = ownScorePair d (2 * i.val) := by
  fin_cases i <;> rfl

private theorem valueOf_maskLow (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8) :
    valueOf P L g d (1009 + 4 * i.val + i.val / 2 + 2) = ownMaskedValue d (4 * i.val + 2) := by
  fin_cases i <;> rfl

private theorem valueOf_maskHigh (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8) :
    valueOf P L g d (1009 + 4 * i.val + i.val / 2 + 3) = ownMaskedValue d (4 * i.val + 3) := by
  fin_cases i <;> rfl

private theorem peerHigh_fresh (i : Fin 8) :
    3146 + 4 * i.val ∉ peerLive (peerPC i) ∧
    3147 + 4 * i.val ∉ peerLive (peerPC i) ∧
    3148 + 4 * i.val ∉ peerLive (peerPC i) ∧
    sumLow i ∉ peerLive (peerPC i) ∧ sumHigh i ∉ peerLive (peerPC i) := by
  fin_cases i <;> decide +kernel

private theorem peerHigh_frame (i : Fin 8) :
    3145 + 4 * i.val ∈ peerLive (peerPC i) ∧
    1009 + 4 * i.val + i.val / 2 + 2 ∈ peerLive (peerPC i) ∧
    1009 + 4 * i.val + i.val / 2 + 3 ∈ peerLive (peerPC i) := by
  fin_cases i <;> decide +kernel

private theorem peerAddLo_code (i : Fin 8) :
    kernel.code[peerPC i + 1]? =
      some ⟨none, peerAddOp (sumLow i) (3145 + 4 * i.val) (3146 + 4 * i.val)⟩ := by
  fin_cases i <;> kernel_rfl

private theorem peerPackHi_code (i : Fin 8) :
    kernel.code[peerPC i + 2]? = some ⟨none, .move
      ⟨.pack, .int .b 64, [some (3147 + 4 * i.val)],
        [.reg (1009 + 4 * i.val + i.val / 2 + 2), .reg (1009 + 4 * i.val + i.val / 2 + 3)]⟩⟩ := by
  fin_cases i <;> kernel_rfl

private theorem peerAddHi_code (i : Fin 8) :
    kernel.code[peerPC i + 3]? =
      some ⟨none, peerAddOp (sumHigh i) (3147 + 4 * i.val) (3148 + 4 * i.val)⟩ := by
  fin_cases i <;> kernel_rfl

private theorem peer_cons_fresh {r dst : Nat} {v : Value} {F : List (Nat × Value)}
    (hr : r ≠ dst) (hF : ∀ p ∈ F, p.1 ≠ dst) : ∀ p ∈ (r, v) :: F, p.1 ≠ dst := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hr
  · exact hF p hp

private theorem peer_get {t : TState} {pc r : Nat} {v : Value} {F : List (Nat × Value)}
    (h : At t pc F) (hm : (r, v) ∈ F) : t.regs r = some v :=
  holds_mem h.2.2.2.2 hm

private theorem peer_finish_load {g : Nat} {d : D} {t : TState} {i : Fin 8} {first second : Value}
    {bytes : List (Option Byte)} (hd : d.site = .peerRead i) (hs : d.sub = 1)
    (ha : d.peerPending = [first]) (ht : (code P L g).AtD d t) (hr : rebuild 3 bytes = .ok second) :
    At (afterLoad t [3146 + 4 * i.val, 3148 + 4 * i.val] bytes) (peerPC i + 1)
      ((3146 + 4 * i.val, first) :: (3148 + 4 * i.val, second) ::
        peerFacts P L g d (peerPC i)) := by
  have hsub : t.sub = 1 := ht.2.1.trans hs
  have hacc : t.acc = [first] := by
    have he := ht.2.2.1
    change t.acc = siteAcc d at he
    simpa [siteAcc, hd, hs, ha] using he
  have hpc : t.pc = peerPC i := by simpa [code, hd] using ht.1
  rw [afterLoad_last hr (by simp [hsub]), hacc]
  have hF : Holds t.regs (peerFacts P L g d (peerPC i)) := by
    have hh := ht.2.2.2.2
    change Holds t.regs (peerFacts P L g d d.site.pc) at hh
    simpa [hd] using hh
  have hf := peerHigh_fresh i
  refine ⟨by simp [hpc], rfl, rfl, ht.2.2.2.1, ?_⟩
  exact ⟨by simp [setRegs, setReg],
    by simp [setRegs, setReg],
    holds_update (holds_update hF (peer_fresh hf.1)) (peer_fresh hf.2.2.1)⟩

private theorem peer_run_adds {g : Nat} {d : D} {u : TState} {i : Fin 8} {first second a b : Value}
    (hw : exchangeReady d = true) (h0 : peerAddE (ownScorePair d (2 * i.val)) first = .ok a)
    (h1 : peerAddE (ownScorePair d (2 * i.val + 1)) second = .ok b)
    (hu : At u (peerPC i + 1) ((3146 + 4 * i.val, first) :: (3148 + 4 * i.val, second) ::
      peerFacts P L g d (peerPC i))) :
    ∃ v, run kernel asms L g 3 u = some v ∧ At v (peerPC i + 4)
      ((sumHigh i, b) :: (sumLow i, a) :: peerFacts P L g d (peerPC i)) := by
  have hf := peerHigh_fresh i
  have hm := peerHigh_frame i
  let F := peerFacts P L g d (peerPC i)
  have hfl : ∀ p ∈ (3146 + 4 * i.val, first) :: (3148 + 4 * i.val, second) :: F,
      p.1 ≠ sumLow i :=
    peer_cons_fresh (by fin_cases i <;> decide)
      (peer_cons_fresh (by fin_cases i <;> decide) (peer_fresh hf.2.2.2.1))
  have hpack : u.regs (3145 + 4 * i.val) = some (ownScorePair d (2 * i.val)) := by
    rw [← valueOf_pack P L g d i]
    exact peer_get hu (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (peer_fact hm.1)))
  obtain ⟨v0, hv0, hAt0⟩ := run_peer_add (L := L) (g := g)
    (peerAddLo_code i) hu hpack (peer_get hu (by simp)) h0 hfl
  have hlo : v0.regs (1009 + 4 * i.val + i.val / 2 + 2) =
      some (ownMaskedValue d (4 * i.val + 2)) := by
    rw [← valueOf_maskLow P L g d i]
    exact peer_get hAt0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (peer_fact hm.2.1))))
  have hhi : v0.regs (1009 + 4 * i.val + i.val / 2 + 3) =
      some (ownMaskedValue d (4 * i.val + 3)) := by
    rw [← valueOf_maskHigh P L g d i]
    exact peer_get hAt0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (peer_fact hm.2.2))))
  have hfpack : ∀ p ∈ (sumLow i, a) :: (3146 + 4 * i.val, first) ::
      (3148 + 4 * i.val, second) :: F, p.1 ≠ 3147 + 4 * i.val :=
    peer_cons_fresh (by fin_cases i <;> decide)
      (peer_cons_fresh (by omega) (peer_cons_fresh (by omega) (peer_fresh hf.2.1)))
  have hpc : 474 ≤ peerPC i + 2 ∧ peerPC i + 2 < 566 := by
    change 474 ≤ 477 + 5 * i.val + 2 ∧ 477 + 5 * i.val + 2 < 566
    omega
  obtain ⟨v1, hv1, hAt1⟩ := run_peer_pack (L := L) (g := g)
    (peerPackHi_code i) hAt0 hlo hhi (ownMasked_bytes hw _) (ownMasked_bytes hw _) hpc hfpack
  have hp : v1.regs (3147 + 4 * i.val) = some (ownScorePair d (2 * i.val + 1)) := by
    have hk : 2 * (2 * i.val + 1) = 4 * i.val + 2 := by omega
    simpa [ownScorePair, hk] using hAt1.2.2.2.2.1
  have hsecond : v1.regs (3148 + 4 * i.val) = some second :=
    peer_get hAt1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hfh : ∀ p ∈ (3147 + 4 * i.val, joinValue (ownMaskedValue d (4 * i.val + 2))
        (ownMaskedValue d (4 * i.val + 3))) :: (sumLow i, a) ::
      (3146 + 4 * i.val, first) :: (3148 + 4 * i.val, second) :: F, p.1 ≠ sumHigh i :=
    peer_cons_fresh (by fin_cases i <;> decide)
      (peer_cons_fresh (by fin_cases i <;> decide)
        (peer_cons_fresh (by fin_cases i <;> decide)
          (peer_cons_fresh (by fin_cases i <;> decide) (peer_fresh hf.2.2.2.2))))
  obtain ⟨v2, hv2, hAt2⟩ := run_peer_add (L := L) (g := g)
    (peerAddHi_code i) hAt1 hp hsecond h1 hfh
  exact ⟨v2, run_comp (run_comp hv0 hv1) hv2, hAt2.mono
    ⟨hAt2.2.2.2.2.1, hAt2.2.2.2.2.2.2.1, hAt2.2.2.2.2.2.2.2.2.2⟩⟩

private def finishPeer (d : D) (i : Fin 8) (a b : Value) (s : Site) : D :=
  { d with
    site := s
    sub := 0
    peerPending := []
    scoreSums := Function.update (Function.update d.scoreSums (2 * i.val) a) (2 * i.val + 1) b }

private theorem peer_table_stable (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8)
    (a b : Value) (s : Site) {r : Nat} (hr : r ≠ 1109) :
    (table P L g (finishPeer d i a b s)).lookup r = (table P L g d).lookup r := by
  have hbe : (r == 1109) = false := beq_eq_false_iff_ne.mpr hr
  simp only [table, finishPeer, List.lookup_cons, hbe]
  rfl

private theorem scoreSum_idx_reg {r j : Nat} (hj : scoreSumRegs.idxOf? r = some j) :
    scoreSumRegs.getD j 0 = r := by
  obtain ⟨hh, he, _⟩ := List.idxOf?_eq_some_iff.mp hj
  have hget : scoreSumRegs[j]? = some scoreSumRegs[j] := getElem?_pos scoreSumRegs j hh
  simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some, he]

private theorem peer_value_stable (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8)
    (a b : Value) (s : Site) {r : Nat} (hm : r ≠ 1109)
    (ha : r ≠ sumLow i) (hb : r ≠ sumHigh i) :
    valueOf P L g (finishPeer d i a b s) r = valueOf P L g d r := by
  have ht := peer_table_stable P L g d i a b s hm
  simp only [valueOf, ht]
  by_cases hOwn : 2918 ≤ r ∧ r < 2950
  · simp only [hOwn]
    rfl
  simp only [hOwn]
  by_cases hPeer : 2886 ≤ r ∧ r < 2918
  · simp only [hPeer]
    rfl
  simp only [hPeer]
  by_cases hMask : 1009 ≤ r ∧ r ≤ 1043
  · simp only [hMask]
    cases (List.finRange 32).find? (fun i => maskSelectDst i == r) <;> rfl
  simp only [hMask]
  by_cases hPack : 3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0
  · simp only [hPack]
    rfl
  simp only [hPack]
  by_cases hExch : 4031 ≤ r ∧ r < 4039
  · simp only [hExch]
    rfl
  simp only [hExch]
  by_cases hSum : 3242 ≤ r ∧ r ≤ 3304
  · simp only [hSum]
    cases hj : scoreSumRegs.idxOf? r with
    | none => rfl
    | some j =>
      have hget := scoreSum_idx_reg hj
      have hneA : j ≠ 2 * i.val := fun h => ha (by simpa [h] using hget.symm)
      have hneB : j ≠ 2 * i.val + 1 := fun h => hb (by simpa [h] using hget.symm)
      simp only [finishPeer, Function.update_of_ne hneA, Function.update_of_ne hneB,
        and_self, ↓reduceIte]
  simp only [hSum]
  by_cases hP : 1115 ≤ r ∧ r ≤ 1160 ∧ (r - 1115) % 3 = 0
  · simp only [hP]
    rfl
  simp only [hP]
  by_cases hRs : 1199 ≤ r ∧ r ≤ 1714
  · simp only [hRs]
    cases h₁ : outputIndex (fun j => 1199 + 129 * j.val) 64 1 r <;>
      cases h₂ : outputIndex (fun j => 1264 + 129 * j.val) 64 1 r <;> rfl
  simp only [hRs]
  by_cases hO : 1745 ≤ r ∧ r ≤ 2413
  · simp only [hO]
    cases h₁ : outputIndex outputFirst 64 1 r <;>
      cases h₂ : outputIndex stageFirst 32 3 r <;> rfl
  simp only [hO, ite_false]

private theorem peer_value_sum (P : Params) (L : Launch) (g : Nat) (d : D)
    (j : Fin 16) : valueOf P L g d (scoreSumRegs.getD j.val 0) = d.scoreSums j.val := by
  fin_cases j <;> rfl

private theorem peer_finish_At {g : Nat} {d : D} {v : TState} {i : Fin 8} {a b : Value} {s : Site}
    {pc : Nat} (h : At v pc ((sumHigh i, b) :: (sumLow i, a) :: peerFacts P L g d (peerPC i)))
    (hc : ∀ r ∈ peerLive pc, r ∈ sumHigh i :: sumLow i :: peerLive (peerPC i))
    (hn : 1109 ∉ peerLive pc) :
    At v pc (peerFacts P L g (finishPeer d i a b s) pc) := by
  apply h.mono
  apply holds_of_pointwise
  intro r hr
  have hv := hc r hr
  by_cases hb : r = sumHigh i
  · subst r
    have he := peer_value_sum P L g (finishPeer d i a b s) ⟨2 * i.val + 1, by omega⟩
    rw [he]
    simpa [finishPeer] using h.2.2.2.2.1
  by_cases ha : r = sumLow i
  · subst r
    have he := peer_value_sum P L g (finishPeer d i a b s) ⟨2 * i.val, by omega⟩
    rw [he]
    simpa [finishPeer, Function.update_of_ne (by omega : 2 * i.val ≠ 2 * i.val + 1)]
      using h.2.2.2.2.2.1
  rw [peer_value_stable P L g d i a b s (fun he => hn (he ▸ hr)) ha hb]
  exact peer_get h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (peer_fact ((List.mem_cons.mp ((List.mem_cons.mp hv).resolve_left hb)).resolve_left ha))))

private theorem peerPackNext_code (i : Fin 8) (h : i.val + 1 < 8) :
    kernel.code[peerPC i + 4]? = some ⟨none, .move
      ⟨.pack, .int .b 64, [some (3145 + 4 * (i.val + 1))],
        [.reg (1009 + 4 * (i.val + 1) + (i.val + 1) / 2),
          .reg (1009 + 4 * (i.val + 1) + (i.val + 1) / 2 + 1)]⟩⟩ := by
  fin_cases i <;> first | kernel_rfl | simp at h

private theorem peer_packNext_frame (i : Fin 8) (h : i.val + 1 < 8) :
    1009 + 4 * (i.val + 1) + (i.val + 1) / 2 ∈ peerLive (peerPC i) ∧
    1009 + 4 * (i.val + 1) + (i.val + 1) / 2 + 1 ∈ peerLive (peerPC i) ∧
    3145 + 4 * (i.val + 1) ∉ sumHigh i :: sumLow i :: peerLive (peerPC i) := by
  fin_cases i <;> first | decide +kernel | simp at h

private theorem peer_next_cover (i : Fin 8) (h : i.val + 1 < 8) :
    ∀ r ∈ peerLive (peerPC ⟨i.val + 1, h⟩),
      r ∈ (3145 + 4 * (i.val + 1)) :: sumHigh i :: sumLow i :: peerLive (peerPC i) := by
  fin_cases i <;> first | lit_mem | simp at h

private theorem peer_next_fresh (i : Fin 8) : 1109 ∉ peerLive (peerPC i) := by
  fin_cases i <;> decide +kernel

private theorem valueOf_nextMaskLow (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8) :
    valueOf P L g d (1009 + 4 * i.val + i.val / 2) = ownMaskedValue d (4 * i.val) := by
  fin_cases i <;> rfl

private theorem valueOf_nextMaskHigh (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 8) :
    valueOf P L g d (1009 + 4 * i.val + i.val / 2 + 1) = ownMaskedValue d (4 * i.val + 1) := by
  fin_cases i <;> rfl

private theorem peer_run_next {g : Nat} {d : D} {v : TState} {i : Fin 8} {a b : Value}
    (hnext : i.val + 1 < 8) (hw : exchangeReady d = true)
    (hv : At v (peerPC i + 4) ((sumHigh i, b) :: (sumLow i, a) :: peerFacts P L g d (peerPC i))) :
    ∃ u, run kernel asms L g 1 v = some u ∧
      (code P L g).AtD (finishPeer d i a b (.peerRead ⟨i.val + 1, hnext⟩)) u := by
  let j : Fin 8 := ⟨i.val + 1, hnext⟩
  let d' := finishPeer d i a b (.peerRead j)
  have hf := peer_packNext_frame i hnext
  have hlo : v.regs (1009 + 4 * j.val + j.val / 2) = some (ownMaskedValue d (4 * j.val)) := by
    rw [← valueOf_nextMaskLow P L g d j]
    exact peer_get hv (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (peer_fact hf.1)))
  have hhi : v.regs (1009 + 4 * j.val + j.val / 2 + 1) =
      some (ownMaskedValue d (4 * j.val + 1)) := by
    rw [← valueOf_nextMaskHigh P L g d j]
    exact peer_get hv (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (peer_fact hf.2.1)))
  have hpc : 474 ≤ peerPC i + 4 ∧ peerPC i + 4 < 566 := by
    change 474 ≤ 477 + 5 * i.val + 4 ∧ 477 + 5 * i.val + 4 < 566
    omega
  have hfresh := List.ne_and_not_mem_of_not_mem_cons hf.2.2
  have hfresh' := List.ne_and_not_mem_of_not_mem_cons hfresh.2
  obtain ⟨u, hu, hat⟩ := run_peer_pack (L := L) (g := g) (peerPackNext_code i hnext)
    hv hlo hhi (ownMasked_bytes hw _) (ownMasked_bytes hw _) hpc
    (peer_cons_fresh (Ne.symm hfresh.1)
      (peer_cons_fresh (Ne.symm hfresh'.1) (peer_fresh hfresh'.2)))
  refine ⟨u, hu, ?_⟩
  have hp : peerPC i + 4 + 1 = peerPC j := by
    change 477 + 5 * i.val + 4 + 1 = 477 + 5 * (i.val + 1)
    omega
  rw [hp] at hat
  refine ⟨hat.1, hat.2.1, hat.2.2.1.trans (siteAcc_nil d' rfl).symm, hat.2.2.2.1, ?_⟩
  apply holds_of_pointwise
  intro r hmem
  change r ∈ peerLive (peerPC j) at hmem
  change u.regs r = some (valueOf P L g d' r)
  have hm := peer_next_cover i hnext r hmem
  by_cases hdst : r = 3145 + 4 * j.val
  · subst r
    rw [valueOf_pack]
    have he : 2 * (2 * j.val) = 4 * j.val := by omega
    simpa [ownScorePair, ownMaskedValue, d', finishPeer, he] using hat.2.2.2.2.1
  by_cases hb : r = sumHigh i
  · subst r
    rw [peer_value_sum P L g d' ⟨2 * i.val + 1, by omega⟩]
    simpa [d', finishPeer] using hat.2.2.2.2.2.1
  by_cases ha : r = sumLow i
  · subst r
    rw [peer_value_sum P L g d' ⟨2 * i.val, by omega⟩]
    simpa [d', finishPeer, Function.update_of_ne (by omega : 2 * i.val ≠ 2 * i.val + 1)]
      using hat.2.2.2.2.2.2.1
  rw [peer_value_stable P L g d i a b (.peerRead j)
    (fun he => peer_next_fresh j (he ▸ hmem)) ha hb]
  have hrest := (List.mem_cons.mp (show r ∈ (3145 + 4 * j.val) :: _ from hm)).resolve_left hdst
  have hrest := (List.mem_cons.mp hrest).resolve_left hb
  have hrest := (List.mem_cons.mp hrest).resolve_left ha
  exact peer_get hat (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (peer_fact hrest))))

private abbrev reducePC (k : Nat) := 516 + 3 * k
private abbrev reduceDst (k : Nat) := 1044 + 4 * k

private def reduceStep (words : Nat → Value) (k : Nat) (seed : Value) : Exec Value := do
  let (lo, hi) ← unpackE 64 (words k)
  let m ← if k % 8 = 0 then peerMaxE lo (b32 4286578688) else peerMaxE seed lo
  peerMaxE m hi

private abbrev reduceArg₁ (k : Nat) : Opnd :=
  if k % 8 = 0 then .reg (reduceDst k) else .reg (1043 + 4 * k)

private abbrev reduceArg₂ (k : Nat) : Opnd :=
  if k % 8 = 0 then .f32imm 4286578688 else .reg (reduceDst k)

private theorem reduceUnpack_code (k : Fin 16) :
    kernel.code[reducePC k.val]? = some ⟨none, .move
      ⟨.unpack, .int .b 64, [some (reduceDst k.val), some (reduceDst k.val + 1)],
        [.reg (scoreSumRegs.getD k.val 0)]⟩⟩ := by
  fin_cases k <;> kernel_rfl

private theorem reduceMax1_code (k : Fin 16) :
    kernel.code[reducePC k.val + 1]? = some
      ⟨none, peerMaxOp (reduceDst k.val + 2) (reduceArg₁ k.val) (reduceArg₂ k.val)⟩ := by
  fin_cases k <;> kernel_rfl

private theorem reduceMax2_code (k : Fin 16) :
    kernel.code[reducePC k.val + 2]? = some
      ⟨none, peerMaxOp (reduceDst k.val + 3) (.reg (reduceDst k.val + 2))
        (.reg (reduceDst k.val + 1))⟩ := by
  fin_cases k <;> kernel_rfl

private theorem run_reduceStep {L : Launch} {g : Nat} {t : TState} {k : Nat} {seed out : Value}
    {words : Nat → Value} {F : List (Nat × Value)} (hk : k < 16)
    (ht : At t (reducePC k) F)
    (hsum : (scoreSumRegs.getD k 0, words k) ∈ F)
    (hseed : k % 8 ≠ 0 → (1043 + 4 * k, seed) ∈ F)
    (hf : ∀ p ∈ F, p.1 < reduceDst k ∨ 1107 < p.1)
    (hout : reduceStep words k seed = .ok out) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u (reducePC (k + 1))
      ((1043 + 4 * (k + 1), out) :: F) := by
  unfold reduceStep at hout
  cases hbytes : unpackE 64 (words k) with
  | error f => simp [hbytes, bind, Except.bind] at hout
  | ok pair =>
    rcases pair with ⟨lo, hi⟩
    simp only [hbytes, bind, Except.bind] at hout
    let left := if k % 8 = 0 then lo else seed
    let right := if k % 8 = 0 then b32 4286578688 else lo
    have he : (if k % 8 = 0 then (peerMaxE lo (b32 4286578688)).bind (peerMaxE · hi)
        else (peerMaxE seed lo).bind (peerMaxE · hi)) =
        (peerMaxE left right).bind (peerMaxE · hi) := by
      by_cases hc : k % 8 = 0 <;> simp [left, right, hc]
    change (if k % 8 = 0 then (peerMaxE lo (b32 4286578688)).bind (peerMaxE · hi)
      else (peerMaxE seed lo).bind (peerMaxE · hi)) = .ok out at hout
    rw [he] at hout
    cases hm : peerMaxE left right with
    | error f => simp [hm, Except.bind] at hout
    | ok m =>
      rw [hm] at hout
      have hmax : peerMaxE m hi = .ok out := hout
      have hf' (j : Nat) (hj : j < 4) : ∀ p ∈ F, p.1 ≠ reduceDst k + j :=
        fun p hp heq => by have hgap := hf p hp; dsimp only [reduceDst] at *; omega
      obtain ⟨u0, h0, hu0⟩ := run_peer_unpack (L := L) (g := g)
        (reduceUnpack_code ⟨k, hk⟩) ht (peer_get ht hsum) hbytes
        (by dsimp only [reducePC, Fin.val_mk]; omega)
        (hf' 0 (by decide)) (hf' 1 (by decide)) (by omega)
      have hlo : OpndIs L g u0 (.reg (reduceDst k)) lo := .reg hu0.2.2.2.2.1
      have hop : OpndIs L g u0 (reduceArg₁ k) left ∧ OpndIs L g u0 (reduceArg₂ k) right := by
        by_cases hz : k % 8 = 0
        · simpa [reduceArg₁, reduceArg₂, left, right, hz, b32] using And.intro hlo
            (OpndIs.imm (L := L) (g := g) (t := u0) (b := 4286578688))
        · simpa [reduceArg₁, reduceArg₂, left, right, hz] using And.intro
            (OpndIs.reg (L := L) (g := g) (peer_get hu0
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hseed hz))))) hlo
      obtain ⟨u1, h1, hu1⟩ := run_peer_max (reduceMax1_code ⟨k, hk⟩) hu0
        hop.1.1 hop.2.1 hop.1.2 hop.2.2 hm
        (peer_cons_fresh (by omega) (peer_cons_fresh (by omega) (hf' 2 (by decide))))
      have hleft : OpndIs L g u1 (.reg (reduceDst k + 2)) m := .reg hu1.2.2.2.2.1
      have hright : OpndIs L g u1 (.reg (reduceDst k + 1)) hi := .reg hu1.2.2.2.2.2.2.1
      obtain ⟨u2, h2, hu2⟩ := run_peer_max (reduceMax2_code ⟨k, hk⟩) hu1
        hleft.1 hright.1 hleft.2 hright.2 hmax
        (peer_cons_fresh (by omega) (peer_cons_fresh (by omega)
          (peer_cons_fresh (by omega) (hf' 3 (by decide)))))
      have hpc : reducePC k + 3 = reducePC (k + 1) := by dsimp only [reducePC]; omega
      rw [hpc] at hu2
      refine ⟨u2, run_comp (run_comp h0 h1) h2, hu2.mono ⟨?_, hu2.2.2.2.2.2.2.2.2⟩⟩
      rw [show 1043 + 4 * (k + 1) = reduceDst k + 3 by dsimp only [reduceDst]; omega]
      exact hu2.2.2.2.2.1

private def tailMax (words : Nat → Value) (base : Nat) (seed : Value) (i : Nat) : Exec Value := do
  let (lo, hi) ← unpackE 64 (words (base + i + 1))
  let m ← peerMaxE seed lo
  peerMaxE m hi

private theorem reduceStep_tail (words : Nat → Value) (base i : Nat) (seed : Value)
    (h : (base + i + 1) % 8 ≠ 0) :
    reduceStep words (base + i + 1) seed = tailMax words base seed i := by
  simp [reduceStep, tailMax, h]

private theorem run_half_tail {L : Launch} {g : Nat} {t : TState} {base n : Nat}
    {initial out : Value} {words : Nat → Value} {F : List (Nat × Value)}
    (hb : base = 0 ∨ base = 8) (hn : n ≤ 7)
    (ht : At t (reducePC (base + 1)) ((1043 + 4 * (base + 1), initial) :: F))
    (hwords : ∀ j : Fin 16, (scoreSumRegs.getD j.val 0, words j.val) ∈ F)
    (hf : ∀ p ∈ F, p.1 < reduceDst base ∨ 1107 < p.1)
    (hout : (List.range n).foldlM (tailMax words base) initial = .ok out) :
    ∃ u, run kernel asms L g (3 * n) t = some u ∧
      At u (reducePC (base + n + 1)) ((1043 + 4 * (base + n + 1), out) :: F) := by
  induction n generalizing out with
  | zero =>
    have he : initial = out := Except.ok.inj hout
    subst out
    exact ⟨t, rfl, ht⟩
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append] at hout
    cases he : (List.range n).foldlM (tailMax words base) initial with
    | error f => simp [he, bind, Except.bind] at hout
    | ok m =>
      have hm : tailMax words base m n = .ok out := by
        rw [he] at hout
        change (Except.ok m >>= fun acc => [n].foldlM (tailMax words base) acc) = .ok out at hout
        simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hout
        exact hout
      obtain ⟨v, hv, hat⟩ := ih (by omega) he
      have hk0 : (base + n + 1) % 8 ≠ 0 := by omega
      have hk : base + n + 1 < 16 := by omega
      have hf' : ∀ p ∈ (1043 + 4 * (base + n + 1), m) :: F,
          p.1 < reduceDst (base + n + 1) ∨ 1107 < p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | h
        · left; dsimp only [reduceDst]; omega
        · have hc := hf p h
          dsimp only [reduceDst] at *
          omega
      obtain ⟨u, hu, huAt⟩ := run_reduceStep (L := L) (g := g) (seed := m) hk hat
        (List.mem_cons_of_mem _ (hwords ⟨_, hk⟩)) (fun _ => List.mem_cons_self) hf'
        ((reduceStep_tail words base n m hk0).trans hm)
      have hpc : base + n + 1 + 1 = base + (n + 1) + 1 := by omega
      rw [hpc] at huAt
      refine ⟨u, ?_, huAt.mono ⟨huAt.2.2.2.2.1, huAt.2.2.2.2.2.2⟩⟩
      rw [show 3 * (n + 1) = 3 * n + 3 by omega]
      exact run_comp hv hu

private theorem run_half_max {L : Launch} {g : Nat} {t : TState} {base : Nat}
    {out : Value} {words : Nat → Value} {F : List (Nat × Value)} (hb : base = 0 ∨ base = 8)
    (ht : At t (reducePC base) F)
    (hwords : ∀ j : Fin 16, (scoreSumRegs.getD j.val 0, words j.val) ∈ F)
    (hf : ∀ p ∈ F, p.1 < reduceDst base ∨ 1107 < p.1)
    (hout : peerHalfMax words base = .ok out) :
    ∃ u, run kernel asms L g 24 t = some u ∧
      At u (reducePC (base + 8)) ((1043 + 4 * (base + 8), out) :: F) := by
  let seed := b32 4286578688
  have h0 : base % 8 = 0 := by omega
  have hk : base < 16 := by omega
  have hf' : ∀ p ∈ F, p.1 < reduceDst base ∨ 1107 < p.1 := by
    intro p hp
    have hc := hf p hp
    dsimp only [reduceDst]
    omega
  have hEq : peerHalfMax words base = (do
      let m ← reduceStep words base seed
      (List.range 7).foldlM (tailMax words base) m) := by
    simp only [peerHalfMax, reduceStep, h0, ↓reduceIte, bind_assoc]
    rfl
  rw [hEq] at hout
  cases he : reduceStep words base seed with
  | error f => simp [he, bind, Except.bind] at hout
  | ok m =>
    have hm : (List.range 7).foldlM (tailMax words base) m = .ok out := by
      simpa only [he, bind, Except.bind] using hout
    obtain ⟨v, hv, hat⟩ := run_reduceStep (L := L) (g := g) hk ht (hwords ⟨_, hk⟩)
      (fun hne => (hne h0).elim) hf' he
    obtain ⟨u, hu, huAt⟩ := run_half_tail (L := L) (g := g) hb (by decide : 7 ≤ 7) hat
      hwords hf hm
    exact ⟨u, run_comp hv hu, huAt⟩

private theorem run_row_reduce {L : Launch} {g : Nat} {t : TState} {out scale : Value}
    {words : Nat → Value} {F : List (Nat × Value)}
    (ht : At t 516 F) (hwords : ∀ j : Fin 16, (scoreSumRegs.getD j.val 0, words j.val) ∈ F)
    (hs : (467, scale) ∈ F) (hf : ∀ p ∈ F, p.1 < 1044 ∨ 1109 < p.1)
    (hout : peerRowMax words scale = .ok out) :
    ∃ u, run kernel asms L g 50 t = some u ∧ At u 566 ((1109, out) :: F) := by
  unfold peerRowMax at hout
  cases hl : peerHalfMax words 0 with
  | error f => simp [hl, bind, Except.bind] at hout
  | ok lo =>
    simp only [hl, bind, Except.bind] at hout
    cases hh : peerHalfMax words 8 with
    | error f => simp [hh] at hout
    | ok hi =>
      simp only [hh] at hout
      cases hm : peerMaxE lo hi with
      | error f => simp [hm] at hout
      | ok m =>
        rw [hm] at hout
        have hmul : mulE true m scale = .ok out := hout
        have hf₀ : ∀ p ∈ F, p.1 < reduceDst 0 ∨ 1107 < p.1 := by
          intro p hp
          have hv := hf p hp
          change p.1 < 1044 ∨ 1107 < p.1
          omega
        obtain ⟨u0, hu0, hat0⟩ := run_half_max (L := L) (g := g) (.inl rfl) ht hwords hf₀ hl
        have hf₁ : ∀ p ∈ (1075, lo) :: F, p.1 < reduceDst 8 ∨ 1107 < p.1 := by
          intro p hp
          change p.1 < 1076 ∨ 1107 < p.1
          rcases List.mem_cons.mp hp with rfl | hp
          · exact .inl (by change 1075 < 1076; decide)
          · have hv := hf p hp
            omega
        obtain ⟨u1, hu1, hat1⟩ := run_half_max (L := L) (g := g) (.inr rfl) hat0
          (fun k => List.mem_cons_of_mem _ (hwords k)) hf₁ hh
        have hno (r : Nat) (hr : 1108 ≤ r ∧ r ≤ 1109) : ∀ p ∈ F, p.1 ≠ r :=
          fun p hp he => by have hv := hf p hp; omega
        have hLo : OpndIs L g u1 (.reg 1075) lo := .reg hat1.2.2.2.2.2.1
        have hHi : OpndIs L g u1 (.reg 1107) hi := .reg hat1.2.2.2.2.1
        obtain ⟨u2, hu2, hat2⟩ := run_peer_max Flow.code_564 hat1
          hLo.1 hHi.1 hLo.2 hHi.2 hm
          (peer_cons_fresh (by decide) (peer_cons_fresh (by decide) (hno 1108 (by decide))))
        have hs' := peer_get hat2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hs)))
        have he : execLocalA asms L g u2
            (.float { mulI true with dsts := [some 1109], srcs := [.reg 1108, .reg 467] }) =
            .ok (PTX.next (setReg u2 1109 out)) := by
          rw [exec_mulE (peer_ideal (.inr (.inr rfl))).at (peer_decline (.inr (.inr rfl)))
            (.reg hat2.2.2.2.2.1) (.reg hs'), hmul]
          rfl
        have hr := run_local Flow.code_565 rfl hat2 he
        have hfinal := hat2.set (v := out) (peer_cons_fresh (by decide) (peer_cons_fresh (by decide)
          (peer_cons_fresh (by decide) (hno 1109 (by decide)))))
        exact ⟨_, run_comp (run_comp (run_comp hu0 hu1) hu2) hr,
          hfinal.mono ⟨hfinal.2.2.2.2.1, hfinal.2.2.2.2.2.2.2.2⟩⟩

private theorem peer_row_cover :
    ∀ r ∈ peerLive 566, r ∈ 1109 :: peerLive 516 := by lit_mem

private theorem peer_row_facts {g : Nat} {d : D} {t : TState} :
    (hs : peerRowMax d.scoreSums (b32 (paramWord L 28 4)) = .ok (rowLocalMax L d)) →
    At t 516 (peerFacts P L g d 516) →
    ∃ u, run kernel asms L g 50 t = some u ∧ At u 566 (peerFacts P L g d 566) := by
  intro hs ht
  have hscore (j : Fin 16) : scoreSumRegs.getD j.val 0 ∈ peerLive 516 := by
    fin_cases j <;> decide +kernel
  have hwords (j : Fin 16) : (scoreSumRegs.getD j.val 0, d.scoreSums j.val) ∈
      peerFacts P L g d 516 := by
    rw [← peer_value_sum P L g d j]
    exact peer_fact (hscore j)
  have hscale : (467, b32 (paramWord L 28 4)) ∈ peerFacts P L g d 516 :=
    peer_fact (by decide +kernel)
  have hsafe : (peerLive 516).all (fun r => decide (r < 1044 ∨ 1109 < r)) = true := by
    decide +kernel
  have hf : ∀ p ∈ peerFacts P L g d 516, p.1 < 1044 ∨ 1109 < p.1 := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact of_decide_eq_true (List.all_eq_true.mp hsafe r hr)
  obtain ⟨u, hu, hat⟩ := run_row_reduce (L := L) (g := g) ht hwords hscale hf hs
  refine ⟨u, hu, peerFacts_dest hat ?_ rfl⟩
  intro r hr hne
  exact peer_fact ((List.mem_cons.mp (peer_row_cover r hr)).resolve_left hne)

private theorem peer_run_final {g : Nat} {d : D} {t : TState} {i : Fin 8} {a b : Value}
    (hlast : ¬ i.val + 1 < 8)
    (ht : At t (peerPC i + 4) ((sumHigh i, b) :: (sumLow i, a) :: peerFacts P L g d (peerPC i)))
    (hs : (peerRowMax (finishPeer d i a b .rowMax).scoreSums
      (b32 (paramWord L 28 4))).toOption.isSome = true) :
    ∃ u, run kernel asms L g 50 t = some u ∧
      (code P L g).AtD (finishPeer d i a b .rowMax) u := by
  have hi : i = (7 : Fin 8) := Fin.ext (by have hb := i.isLt; omega)
  subst i
  let d' := finishPeer d 7 a b .rowMax
  have hsum : peerRowMax d'.scoreSums (b32 (paramWord L 28 4)) = .ok (rowLocalMax L d') := by
    unfold rowLocalMax
    cases he : peerRowMax d'.scoreSums (b32 (paramWord L 28 4)) with
    | error f =>
      change (peerRowMax d'.scoreSums _).toOption.isSome = true at hs
      simp [he, Except.toOption] at hs
    | ok value => rfl
  have ht' : At t 516 (peerFacts P L g d' 516) :=
    peer_finish_At (i := 7) (a := a) (b := b) (s := .rowMax) ht
      (by lit_mem) (by decide +kernel)
  obtain ⟨u, hr, hu⟩ := peer_row_facts hsum ht'
  exact ⟨u, hr, hu.1, hu.2.1, hu.2.2.1.trans (siteAcc_nil d' rfl).symm,
    hu.2.2.2.1, hu.2.2.2.2⟩

private theorem peer_finish_inv {g : Nat} {d : D} {i : Fin 8} {a b : Value} (hi : Inv P L g d)
    (hx : exchangeReady d = true) {s : Site} (hs : s = .rowMax ∨ ∃ j, s = .peerRead j) :
    Inv P L g (finishPeer d i a b s) := by
  let d₀ := { d with peerPending := [], scoreSums := (finishPeer d i a b s).scoreSums }
  have hv : Inv P L g d₀ := { hi with subLt := hi.subLt }
  rcases hs with rfl | ⟨j, rfl⟩
  · exact inv_setSite hv .rowMax (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
      (by simp) (by simp) (by simp)
  · exact inv_setSite hv (.peerRead j) (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
      (by simp) (by simp) (by simp) (by simp [Site.needsRowTotal]) (fun _ => hx)

/-- Each peer read follows the concrete vector load and runs the matching local arithmetic. -/
theorem step_peerRead {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (d : D) {i : Fin 8}
    (hd : d.site = .peerRead i) :
    (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  obtain ⟨ac, bytes, he, hloc, hsize, hu⟩ := fires_peerRead_at hpre hd hinv hat hc hf
  have hstep : next P L g d e = nextSite P L g d ⟨e.pc, .rd ac bytes⟩ := by
    rw [next, ← he]
  rw [hd] at hloc hsize
  have emain := hinv.exchangeWords (by rw [hd]; rfl)
  have hsub : d.sub < 2 := by simpa [hd, Site.elems] using hinv.subLt
  refine .inl ?_
  cases hw : rebuild 3 bytes with
  | error f =>
    exact .inl (by simp [hstep, nextSite, hd, hsize, hw])
  | ok word =>
    by_cases hzero : d.sub = 0
    · have hloc₀ := hloc
      rw [hzero] at hloc₀
      refine .inr ⟨{ d with sub := 1, peerPending := [word] }, u, ?_, .refl, ?_⟩
      · simp [hstep, nextSite, hd, hloc₀, hsize, hw, hzero]
      · rw [hu]
        exact peerRead_low hd hzero hinv hat hw
    have hone : d.sub = 1 := by omega
    cases hpend : d.peerPending with
    | nil => exact .inl (by simp [hstep, nextSite, hd, hsize, hw, hzero, hpend])
    | cons first tail =>
      cases tail with
      | cons _ _ => exact .inl (by simp [hstep, nextSite, hd, hsize, hw, hzero, hpend])
      | nil =>
        have hbody (va vb : Value) :=
          fun ha : peerAddE (ownScorePair d (2 * i.val)) first = .ok va =>
          fun hb : peerAddE (ownScorePair d (2 * i.val + 1)) word = .ok vb =>
            peer_run_adds (P := P) (L := L) (g := g) emain ha hb
              (hu ▸ peer_finish_load hd hone hpend hat hw)
        cases ha : peerAddE (ownScorePair d (2 * i.val)) first with
        | error f =>
          exact .inl (by simp [hstep, nextSite, hd, hsize, hw, hzero, hpend, ha])
        | ok a =>
          cases hb : peerAddE (ownScorePair d (2 * i.val + 1)) word with
          | error f =>
            exact .inl (by simp [hstep, nextSite, hd, hsize, hw, hzero, hpend, ha, hb])
          | ok b =>
            obtain ⟨v, hr, hv⟩ := hbody a b ha hb
            by_cases hcut : i.val + 1 < 8
            · obtain ⟨u', hr', hu'⟩ := peer_run_next hcut emain hv
              refine .inr ⟨_, u', ?_, run_rtg (run_comp hr hr'), hu',
                peer_finish_inv hinv emain (.inr ⟨_, rfl⟩)⟩
              simp [hstep, nextSite, hd, hloc, hsize, hw, hzero, hpend, ha, hb, hcut, finishPeer]
            · by_cases hs : (peerRowMax (finishPeer d i a b .rowMax).scoreSums
                  (b32 (paramWord L 28 4))).toOption.isSome = true
              · obtain ⟨u', hr', hu'⟩ := peer_run_final hcut hv hs
                refine .inr ⟨_, u', ?_, run_rtg (run_comp hr hr'), hu',
                  peer_finish_inv hinv emain (.inl rfl)⟩
                simp only [finishPeer] at hs
                simp [hstep, nextSite, hd, hloc, hsize, hw, hzero, hpend, ha, hb, hcut,
                  finishPeer, hs]
              · exact .inl (by
                  have hs' := hs
                  simp only [finishPeer] at hs'
                  simp [hstep, nextSite, hd, hsize, hw, hzero, hpend, ha, hb, hcut, hs'])

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
