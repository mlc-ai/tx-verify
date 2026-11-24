-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Kernels.FlashMlaSparseDecodeH64.Audit.PeerScores
import all Kernels.FlashMlaSparseDecodeH64.Assumptions.PeerScores

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow PTX.Proof
open Assumptions

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- The active assumption rule realizes a peer pack action in one local step. -/
theorem run_peer_action {t u : TState} {site : Nat} {step : PeerPack} {F : List (Nat × Value)}
    (h : At t site F) (hs : peerPack site = some step)
    (hc : kernel.code[site]? = some ⟨none, step.op⟩) (hr : step.run t = some u) :
    run kernel asms L g 1 t = some u := by
  have hsite : 394 ≤ t.pc ∧ t.pc < 474 := by
    have he : peerPack t.pc = some step := by rw [h.1]; exact hs
    unfold peerPack at he
    split at he
    · assumption
    · cases he
  have hA : ∀ a ∈ asms, a.segmentRule L g t = none := Proof.asms_segment_free (L := L) (g := g) t
  have hsel := peerPackRule_of_step (t := t) (by rw [h.1]; exact hs)
  have hdead : deadPackWords t.pc = none := by
    unfold deadPackWords
    split <;> first | rfl | omega
  have hshared : t.pc ∉ sharedBitsSites := by
    simp [sharedBitsSites]
    omega
  have hparam : ¬ t.pc ∈ paramAdds := by
    simp [paramAdds]
    omega
  have hpref : ¬ t.pc ∈ prefetchTensorMapSites := by
    simp [prefetchTensorMapSites]
    omega
  have hlocal : step.op.isLocal = true := by
    cases step with
    | extend => rfl
    | upper => rfl
    | merge _ _ _ highFirst => cases highFirst <;> rfl
  refine run_local (K := kernel) hc hlocal h ?_
  rw [execLocalA_noSegment hA]
  have hh : sharedBits.localRule L g t step.op = some (.ok u) := by
    simp [sharedBits, hshared, deadPackRule_of_none hdead, hsel, hr]
  cases step <;> simp only [PeerPack.op] at hh <;> simp [execLocalRule, asms, Assumptions.all,
    Assumptions.idealArith, Assumptions.approx, Assumptions.ncReadOnly, Assumptions.storeDrain,
    Assumption.idealReal, Assumption.approxExact, Assumption.ncReadOnly,
    Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, Assumptions.lg2Exact,
    Assumptions.paramPointers, hparam, hpref, Assumption.FloatForm.ofOp,
    Assumption.ApproxForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hh, PeerPack.op]

/-- A successful pack substep writes one register and advances. -/
theorem peer_action_next {t u : TState} {p : PeerPack} (h : p.run t = some u) :
    ∃ dst value, u = PTX.next (setReg t dst value) := by
  cases p <;> simp only [PeerPack.run, bind, Option.bind] at h
  all_goals
    repeat' first
      | exact ⟨_, _, (Option.some.inj h).symm⟩
      | contradiction
      | (split at h <;> (try dsimp only at h))

/-- A list of pack operations certified against the frozen program executes as written. -/
theorem run_peer_program {ps : List PeerPack} {t u : TState} {site : Nat}
    (h : At t site [])
    (hc : ∀ i p, ps[i]? = some p → peerPack (site + i) = some p ∧
      kernel.code[site + i]? = some ⟨none, p.op⟩)
    (hr : ps.foldlM PeerPack.run t = some u) :
    run kernel asms L g ps.length t = some u := by
  induction ps generalizing t site with
  | nil => exact hr
  | cons p ps ih =>
    have ht := hc 0 p rfl
    cases hp : p.run t with
    | none => simp [List.foldlM, hp, bind, Option.bind] at hr
    | some t' =>
      have he := run_peer_action (L := L) (g := g) h ht.1 ht.2 hp
      have hs : At t' (site + 1) [] := by
        obtain ⟨dest, value, rfl⟩ := peer_action_next hp
        exact ⟨congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, trivial⟩
      have htail := ih hs (fun j p' hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hc (j+1) p' hj)
        (by simpa [List.foldlM, hp, bind, Option.bind] using hr)
      simpa [Nat.add_comm] using run_comp he htail

/-- The eight local steps that produce two ordered pairs of scores. -/
def peerGroup (j : Fin 8) : List PeerPack :=
  let b := 2886 + 4 * j.val
  let x := 3177 + 8 * j.val
  [.extend x (b + 3), .upper (x + 1) x, .extend (x + 2) (b + 2), .extend (x + 3) (b + 1),
    .upper (x + 4) (x + 3), .extend (x + 5) b, .merge (x + 6) (x + 5) (x + 4) true,
    .merge (x + 7) (x + 2) (x + 1) false]

/-- These are the eight transport callbacks attached to this group's frozen instructions. -/
theorem peerGroup_matches (j : Fin 8) (i : Fin 8) :
    peerPack (394 + 10 * j.val + i.val) = (peerGroup j)[i.val]? := by
  fin_cases j <;> fin_cases i <;> rfl

/-- On four scores of the proper representation, the widened values retain their exact order. -/
theorem eval_peerGroup (j : Fin 8) {t : TState} {a b c d : Value}
    (ha : t.regs (2886 + 4 * j.val) = some a)
    (hb : t.regs (2887 + 4 * j.val) = some b)
    (hc : t.regs (2888 + 4 * j.val) = some c)
    (hd : t.regs (2889 + 4 * j.val) = some d)
    (ha' : scoreHalf a) (hb' : scoreHalf b) (hc' : scoreHalf c) (hd' : scoreHalf d) :
    ∃ u, (peerGroup j).foldlM PeerPack.run t = some u ∧
      u.pc = t.pc + 8 ∧ u.sub = t.sub ∧ u.fault = t.fault ∧ u.acc = t.acc ∧
      u.regs (3183 + 8 * j.val) = some (.pair a b) ∧
      u.regs (3184 + 8 * j.val) = some (.pair c d) ∧
      ∀ r, r < 3177 + 8 * j.val ∨ 3184 + 8 * j.val < r → u.regs r = t.regs r := by
  let x := 3177 + 8 * j.val
  let z := peerPackZero
  let writes : List (Nat × Value) :=
    [(x, .pair d z), (x+1, .pair z d), (x+2, .pair c z), (x+3, .pair b z),
      (x+4, .pair z b), (x+5, .pair a z), (x+6, .pair a b), (x+7, .pair c d)]
  let regs := writes.foldl
    (fun (R : Nat → Option Value) p => Function.update R p.1 (some p.2)) t.regs
  let u := { t with pc := t.pc + 8, regs := regs }
  refine ⟨u, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · fin_cases j <;>
      simp only [Nat.reduceAdd, Nat.reduceMul] at ha hb hc hd x
    all_goals
      simp only [peerGroup, List.foldlM_cons, List.foldlM_nil, PeerPack.run, Option.bind, bind,
        pure, PTX.next, setReg, Function.update_apply, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, ↓reduceIte, ha, hb, hc, hd, ha', hb', hc', hd', true_and,
        and_true, and_self, u, regs, writes, x, z, List.foldl_cons, List.foldl_nil]
  · fin_cases j <;> rfl
  · fin_cases j <;> rfl
  · intro r hr
    have hne (k : Nat) (hk : k ≤ 7) : r ≠ x+k := by
      dsimp only [x] at *
      omega
    simp only [u, regs, writes, List.foldl_cons, List.foldl_nil, Function.update_apply]
    have h0 : r ≠ x := fun h => hne 0 (by decide) (by simpa using h)
    simp only [h0, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
      hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide), ite_false]

/-- Execute the eight audited operations carrying one group of four scores. -/
theorem run_peerGroup (j : Fin 8) {t : TState} {F : List (Nat × Value)} {a b c d : Value}
    (hat : At t (394 + 10 * j.val) F)
    (ha : t.regs (2886 + 4 * j.val) = some a)
    (hb : t.regs (2887 + 4 * j.val) = some b)
    (hc : t.regs (2888 + 4 * j.val) = some c)
    (hd : t.regs (2889 + 4 * j.val) = some d)
    (ha' : scoreHalf a) (hb' : scoreHalf b) (hc' : scoreHalf c) (hd' : scoreHalf d)
    (hframe : ∀ q ∈ F, q.1 < 3177 + 8 * j.val ∨ 3184 + 8 * j.val < q.1) :
    ∃ u, run kernel asms L g 8 t = some u ∧
      At u (402 + 10 * j.val)
        ((3183 + 8 * j.val, .pair a b) :: (3184 + 8 * j.val, .pair c d) :: F) := by
  have hlen : (peerGroup j).length = 8 := rfl
  have hcode : ∀ i p, (peerGroup j)[i]? = some p →
      peerPack ((394 + 10 * j.val) + i) = some p ∧
      kernel.code[(394 + 10 * j.val) + i]? = some ⟨none, p.op⟩ := by
    intro i p hp
    have hi : i < 8 := by
      have hb := List.getElem?_eq_some_iff.mp hp
      simpa only [hlen] using hb.choose
    have hstep := (peerGroup_matches j ⟨i, hi⟩).trans hp
    have hc := Audit.peerPack_matches ⟨10 * j.val + i, by have := j.isLt; omega⟩
    change (match peerPack (394 + (10 * j.val + i)) with
      | none => True
      | some p => kernel.code[394 + (10 * j.val + i)]? = some ⟨none, p.op⟩) at hc
    rw [← Nat.add_assoc, hstep] at hc
    exact ⟨hstep, hc⟩
  obtain ⟨u, hu, hupc, husub, hufault, huacc, hul, hur, hframe'⟩ :=
    eval_peerGroup j ha hb hc hd ha' hb' hc' hd'
  have h := run_peer_program (L := L) (g := g) (hat.mono (by simp)) hcode hu
  rw [hlen] at h
  have htpc := hat.1
  refine ⟨u, h, by omega, husub.trans hat.2.1, huacc.trans hat.2.2.1,
    hufault.trans hat.2.2.2.1, hul, hur, ?_⟩
  suffices ∀ G : List (Nat × Value), (∀ q ∈ G, q ∈ F) → Holds u.regs G from
    this F fun _ hq => hq
  intro G hG
  induction G with
  | nil => trivial
  | cons q qs ih =>
    obtain ⟨r, v⟩ := q
    refine ⟨?_, ih fun q hq => hG q (List.mem_cons_of_mem _ hq)⟩
    have hq := hG (r, v) (by simp)
    rw [hframe' r (hframe (r, v) hq)]
    exact holds_mem hat.2.2.2.2 hq

/-- Assemble the audited pairs into the 16-byte word that the peer store writes. -/
theorem run_peerPack (j : Fin 8) {t : TState} {F : List (Nat × Value)} {a b c d : Value}
    (hat : At t (402 + 10 * j.val) F)
    (ha : t.regs (3183 + 8 * j.val) = some (.pair a b))
    (hb : t.regs (3184 + 8 * j.val) = some (.pair c d))
    (ha' : scoreHalf a) (hb' : scoreHalf b) (hc' : scoreHalf c) (hd' : scoreHalf d)
    (hframe : ∀ q ∈ F, q.1 ≠ 4031 + j.val) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (403 + 10 * j.val) ((4031 + j.val, .pair (.pair a b) (.pair c d)) :: F) := by
  let m : MoveInstr := ⟨.pack, .int .b 128, [some (4031 + j.val)],
    [.reg (3183 + 8 * j.val), .reg (3184 + 8 * j.val)]⟩
  have hpc := hat.1
  have h1 : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have h2 : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hdead : deadPackWords t.pc = none := by unfold deadPackWords; split <;> first | rfl | omega
  have hnone := Thread.asms_localRule_move (L := L) (g := g) (m := m) h1 h2 hdead
  have he : execLocalA asms L g t (.move m) =
      .ok (PTX.next (setReg t (4031 + j.val) (.pair (.pair a b) (.pair c d)))) := by
    rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hnone,
      execLocal_move (by rfl)]
    simp [m, execMove, DType.width, readValue, readReg, ha, hb, Value.bytes, scoreHalf_bytes ha',
      scoreHalf_bytes hb', scoreHalf_bytes hc', scoreHalf_bytes hd', joinValue,
      bind, Except.bind, pure, Except.pure]
  refine ⟨_, run_local (K := kernel) (Audit.peerPack_stores j).1 rfl hat he, ?_⟩
  convert hat.set hframe using 1
  omega

/-- A four-byte score retained from a load, with an immediate zero for a missing index. -/
theorem scoreHalf_getD {words : List Value}
    (h : words.all (fun v => decide (scoreHalf v)) = true) (i : Nat) :
    scoreHalf (words.getD i (b32 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : words[i]? with
  | none => exact (by decide : scoreHalf (b32 0))
  | some v =>
    change scoreHalf v
    exact of_decide_eq_true (List.all_eq_true.mp h v (List.mem_of_getElem? hv))

/-- A packed exchange value occupies exactly the sixteen bytes of the shared store. -/
theorem exchangeValue_bytes {d : D} (h : exchangeReady d = true) (i : Nat) :
    (exchangeValue d i).bytes = 16 := by
  have hp : d.peerScores.all (fun v => decide (scoreHalf v)) = true :=
    (Bool.and_eq_true_iff.mp h).2
  simp only [exchangeValue, Value.bytes, scoreHalf_bytes (scoreHalf_getD hp _)]

/-- The peer exchange can only emit its aligned shared write. -/
theorem fired_exchangeStore (hpre : Pre P L mem0) (j : Fin 8)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .exchStore j) (hat : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ a, e.kind = .wr a (exchangeValue d j.val).toBytes ∧
      siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = 16 ∧ o = some (PTX.next t) := by
  have hpc : d.site.pc = 403 + 10 * j.val := congrArg Site.pc hd
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (Audit.peerPack_stores j).2)
  have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
  have hts := hat.2.1.trans hsub
  let off := exchangeBase + exchangeQuad * (warpOf L g ^^^ 2) + 16 * laneOf L g +
    exchangeChunk * j.val
  have hr : t.regs (988 + j.val) = some (sb L off) := by
    have h := reg_value hat (r := 988 + j.val) (by
      rw [hd]
      fin_cases j <;> decide +kernel)
    fin_cases j <;> exact h
  have hv : t.regs (4031 + j.val) = some (exchangeValue d j.val) := by
    have h := reg_value hat (r := 4031 + j.val) (by
      rw [hd]
      fin_cases j <;> decide +kernel)
    fin_cases j <;> exact h
  have hbase := sharedBase_lt hpre
  have hlane := hi.laneLt
  have hw : warpOf L g < 4 := hi.warpLt
  have hj := j.isLt
  have hxor : (warpOf L g ^^^ 2) < 4 := by
    interval_cases h : warpOf L g <;> decide
  have hlt : L.sharedBase + off < 2 ^ 32 := by
    dsimp [off, exchangeBase, exchangeQuad, exchangeChunk]
    omega
  have hbaseAlign : L.sharedBase % 1024 = 0 := by
    rw [hpre.sharedBase]
    exact hpre.sharedAlignment
  have hal : (L.sharedBase + off) % 16 = 0 := by
    dsimp [off, exchangeBase, exchangeQuad, exchangeChunk]
    omega
  have haddr : effAddr L g t .shared (988 + j.val) 0 =
      .ok (shLoc L g off) := effAddr_b32 hr hlt
  have hready := hi.exchangeWords (by rw [hd]; rfl)
  have hstore := storeValue_of_bytes (w := 128) (exchangeValue_bytes hready j.val)
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := 988 + j.val) (w := 32)
    (by rfl) rfl rfl rfl (by simp)] at hf
  simp [DType.width, storeTmpl, haddr, elemAcc, hts, hal, shLoc, hv, hstore, readValue, readReg,
    afterStore, bind, Except.bind, pure, Except.pure, Loc.at, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · simp [hd, siteLoc, off, shLoc]
  · simpa [PTX.next, hts] using hu

/-- A shared peer store writes the four retained scores as the exact paired payload. -/
theorem fires_exchangeStore (hpre : Pre P L mem0) (j : Fin 8)
    {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .exchStore j) (hat : (code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ a, e.kind = .wr a (exchangeValue d j.val).toBytes ∧
      siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = 16 ∧ u = PTX.next t := by
  obtain ⟨a, he, hl, hs, hu⟩ := fired_exchangeStore hpre j hd hat hi hc hf
  exact ⟨a, he, hl, hs, Option.some.inj hu⟩

/-- The tracked live registers on entry to a peer pack. -/
def exchangeLive (j : Fin 8) : List Nat :=
  (Flow.live (394 + 10 * j.val)).filter tracked.contains

private theorem exchange_source {d : D} {t : TState} (j : Fin 8) (i : Fin 4)
    (hat : At t (394 + 10 * j.val) (factsFrom (exchangeLive j) (valueOf P L g d))) :
    t.regs (2886 + 4 * j.val + i.val) =
      some (d.peerScores.getD (4 * j.val + i.val) (b32 0)) := by
  have hmem : 2886 + 4 * j.val + i.val ∈ exchangeLive j := by
    fin_cases j <;> fin_cases i <;> decide +kernel
  have ha := holds_mem hat.2.2.2.2 (mem_factsFrom hmem)
  have hi := i.isLt
  have hj := j.isLt
  have hr₀ : ¬ (2918 ≤ 2886 + 4 * j.val + i.val ∧ 2886 + 4 * j.val + i.val < 2950) := by omega
  have hr₁ : 2886 ≤ 2886 + 4 * j.val + i.val ∧ 2886 + 4 * j.val + i.val < 2918 := by omega
  have hindex : 2886 + 4 * j.val + i.val - 2886 = 4 * j.val + i.val := by omega
  simpa only [valueOf, ite_eq_right hr₀, ite_eq_left hr₁, hindex] using ha

/-- Run the local pack for a group, preserving the other live state at the shared write. -/
theorem run_to_exchange (j : Fin 8) (d : D) {t : TState} (hready : exchangeReady d = true)
    (hat : At t (394 + 10 * j.val) (factsFrom (exchangeLive j) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 9 t = some u ∧
      At u (Site.exchStore j).pc (facts P L g { d with site := .exchStore j }) := by
  have hw := (Bool.and_eq_true_iff.mp hready).2
  have hframe : ∀ q ∈ factsFrom (exchangeLive j) (valueOf P L g d),
      q.1 < 3177 + 8 * j.val ∨ 3184 + 8 * j.val < q.1 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact (by fin_cases j <;> decide +kernel :
      ∀ r ∈ exchangeLive j, r < 3177 + 8 * j.val ∨ 3184 + 8 * j.val < r) r hr
  have ha := exchange_source j 0 hat
  have hb := exchange_source j 1 hat
  have hc := exchange_source j 2 hat
  have hd := exchange_source j 3 hat
  have h₀ : 2886 + 4 * j.val + (0 : Fin 4).val = 2886 + 4 * j.val := rfl
  have h₁ : 2886 + 4 * j.val + (1 : Fin 4).val = 2887 + 4 * j.val := by omega
  have h₂ : 2886 + 4 * j.val + (2 : Fin 4).val = 2888 + 4 * j.val := by omega
  have h₃ : 2886 + 4 * j.val + (3 : Fin 4).val = 2889 + 4 * j.val := by omega
  rw [h₀] at ha
  rw [h₁] at hb
  rw [h₂] at hc
  rw [h₃] at hd
  obtain ⟨u, hrun, hu⟩ := run_peerGroup (L := L) (g := g) j hat ha hb hc hd
    (scoreHalf_getD hw _) (scoreHalf_getD hw _) (scoreHalf_getD hw _) (scoreHalf_getD hw _) hframe
  let get (i : Nat) := d.peerScores.getD (4 * j.val + i) (b32 0)
  have hp : ∀ q ∈ ((3183 + 8 * j.val, .pair (get 0) (get 1)) ::
      (3184 + 8 * j.val, .pair (get 2) (get 3)) ::
      factsFrom (exchangeLive j) (valueOf P L g d)), q.1 ≠ 4031 + j.val := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    intro heq
    exact (by fin_cases j <;> decide +kernel : 4031 + j.val ∉ exchangeLive j) (heq ▸ hr)
  obtain ⟨v, hv, hatv⟩ := run_peerPack (L := L) (g := g) j hu hu.2.2.2.2.1 hu.2.2.2.2.2.1
    (scoreHalf_getD hw _) (scoreHalf_getD hw _) (scoreHalf_getD hw _) (scoreHalf_getD hw _) hp
  refine ⟨v, run_comp hrun hv, hatv.mono ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  by_cases heq : r = 4031 + j.val
  · subst r
    have hval : valueOf P L g { d with site := .exchStore j } (4031 + j.val) =
        exchangeValue d j.val := by fin_cases j <;> rfl
    rw [hval]
    exact hatv.2.2.2.2.1
  · have hlo : r ∈ exchangeLive j :=
      (by fin_cases j <;> decide +kernel :
        ∀ r ∈ (Flow.live (Site.exchStore j).pc).filter tracked.contains,
          r ≠ 4031 + j.val → r ∈ exchangeLive j) r hr heq
    exact holds_mem hatv.2.2.2.2.2.2.2 (mem_factsFrom hlo)

private theorem exchange_atD {d : D} {t : TState}
    (ha : At t d.site.pc (facts P L g d)) (hs : d.sub = 0) :
    (code P L g).AtD d t :=
  ⟨ha.1, ha.2.1.trans hs.symm, ha.2.2.1.trans (siteAcc_nil d hs).symm,
    ha.2.2.2.1, ha.2.2.2.2⟩

private theorem exchange_inv {d : D} (h : Inv P L g d) (hs : d.site.needsExchangeReady = true)
    (nxt : Site) (hepi : nxt.inEpilogue = false) (hrs : nxt.inRescale = false)
    (hscore : ¬ ∃ a k, nxt = .scoreLoad a k) (hexit : nxt ≠ .exit)
    (hloop : nxt ≠ .bulkWait ∧ nxt ≠ .lastStore) (hrow : nxt.needsRowTotal = false) :
    Inv P L g { d with site := nxt, sub := 0 } :=
  inv_setSite h nxt
    (by rw [hepi]; simp) (by rw [hrs]; simp) (fun he => (hscore he).elim)
    (by simp [hexit]) (by simp [hloop])
    (by rw [hrow]; simp) (fun _ => h.exchangeWords hs)

private theorem exchange_frame_all (j k : Fin 8) (hn : k.val = j.val + 1) :
    ∀ r ∈ exchangeLive k, r ∈ (Flow.live (Site.exchStore j).pc).filter tracked.contains := by
  revert j k
  decide +kernel

/-- The eight shared stores form one chain from peer packing to the pair's barrier. -/
theorem step_exchangeStore (hpre : Pre P L mem0) (d : D) (j : Fin 8)
    (hd : d.site = .exchStore j) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hi hcode hf => by
    obtain ⟨a, he, hloc, hsize, rfl⟩ := fires_exchangeStore hpre j hd hat hi hcode hf
    have hsub : d.sub = 0 := by simpa [Site.elems, hd] using hi.subLt
    rw [hd, hsub] at hloc
    have ht := at_next_of hat (congrArg Site.pc hd) hsub
    have hre : d.site.needsExchangeReady = true := by rw [hd]; rfl
    by_cases hnext : j.val + 1 < 8
    · let k : Fin 8 := ⟨j.val + 1, hnext⟩
      let d' : D := { d with site := .exchStore k, sub := 0 }
      have hnextEq : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, he, writeStep, hloc, hsize, hnext, hsub, Site.elemBytes,
          Site.elems, d', k]
      have hframe := exchange_frame_all j k (by rfl)
      have hstart : At (PTX.next t) (394 + 10 * k.val)
          (factsFrom (exchangeLive k) (valueOf P L g d)) := by
        have hpc : (PTX.next t).pc = (Site.exchStore j).pc + 1 := ht.1
        have heq : (Site.exchStore j).pc + 1 = 394 + 10 * k.val := by
          simp [Site.pc, k]
          omega
        exact ⟨hpc.trans heq, ht.2.1, ht.2.2.1, ht.2.2.2.1,
          holds_factsFrom_mono ht.2.2.2.2 hframe⟩
      obtain ⟨v, hr, hv⟩ := run_to_exchange k d (hi.exchangeWords hre) hstart
      refine Or.inl (Or.inr ⟨d', v, hnextEq, run_rtg hr, ?_, ?_⟩)
      · exact exchange_atD hv rfl
      · exact exchange_inv hi hre (.exchStore k) rfl rfl (by simp) (by simp)
          (by simp) rfl
    · have hj : j = 7 := Fin.ext (by have := j.isLt; omega)
      subst j
      let d' : D := { d with site := .pairBar, sub := 0 }
      have hnextEq : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, he, writeStep, hloc, hsize, hsub, Site.elemBytes, Site.elems, d']
      have hstart : At (PTX.next t) 474
          (factsFrom ((Flow.live 473).filter tracked.contains) (valueOf P L g d)) := ht
      obtain ⟨v, hr, hv⟩ : ∃ v, run kernel asms L g 1 (PTX.next t) = some v ∧
          At v 475 (facts P L g d') := by
        seg_fp hstart using rfl
      refine Or.inl (Or.inr ⟨d', v, hnextEq, run_rtg hr, ?_, ?_⟩)
      · exact exchange_atD hv rfl
      · exact exchange_inv hi hre .pairBar rfl rfl (by simp) (by simp) (by simp) rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
