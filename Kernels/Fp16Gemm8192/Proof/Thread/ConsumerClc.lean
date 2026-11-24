-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOut
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun

@[expose] public section

/-! # A consumer's successful CLC polls

A consumer's successful polls of its CTA's CLC response barrier are its arrivals on its group's CLC
barrier plus the response it holds (`Consumer.D.clcHold`), which it holds from its successful poll
to
its group's CLC barrier arrival (`cons_clc`). That arrival follows a proxy fence after the latest
successful poll (`cons_clc_fence`), and the acknowledgement arrival holds no response (`ack_hold`).
-/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The CLC counts along a thread's run: the prologue has no poll and no named barrier event of the
group's CLC barrier id; a consumer's successful polls of its CTA's CLC response barrier are its
arrivals on that id plus the response it holds, and are its accumulator arrivals plus its open task
(`Consumer.tileOpen`); it polls no accumulator of another accumulator than its own. Other roles
carry no count. -/
def ClcPollInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es ∧ es.countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) = 0
  | .inr (.cons c), es =>
      okPolls (clcResp L g) es =
        es.countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c.clcHold ∧
      okPolls (clcResp L g) es =
        arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) es + Consumer.tileOpen c ∧
      ∀ j, j < 2 → j ≠ Consumer.accIdx L g → okPolls (Consumer.accFull L g j) es = 0
  | _, _ => True

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- No prologue event is a named barrier event (decided on the code). -/
theorem prologue_no_barId {p : Prologue.D} {t : TState} {ins : Instr} {e : Event} {o :
    Option TState}
    (id : Nat) (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o) :
    Execution.isBarId id e = false := by
  obtain ⟨site, w⟩ := p
  simp only at hc hf
  unfold Execution.isBarId
  split
  · rename_i id' c hk
    have hpc := OpPcs.mem kernel_bar_pcs hc (fires_bar_op hf hk)
    clear hc hf hk
    exfalso
    revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · rfl

namespace Consumer

/-- Only the CLC barrier site of a consumer fires a named barrier event with the group's CLC
barrier id; its output barrier events carry the output id. -/
theorem isBarId_clcBar (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hb : Execution.isBarId (tidOf L g / 32 / 4 + 1) e = true) : d.site = .clcBar := by
  unfold Execution.isBarId at hb
  split at hb
  · rename_i id c m hk
    have hid : id = tidOf L g / 32 / 4 + 1 := by simpa using hb
    have h10 : outId L g = tidOf L g / 32 / 4 + 10 := rfl
    rcases bar_site hc hf hk with hs | ⟨k, hs⟩ | ⟨k, hs⟩
    · exact hs
    · have he := out_bar_event hpre hat hc hf (.inl hs)
      rw [he] at hk
      cases hk
      omega
    · have he := out_bar_event hpre hat hc hf (.inr hs)
      rw [he] at hk
      cases hk
      omega
  · cases hb

/-- One consumer step: the poll it makes raises the response it holds, its CLC barrier arrival
releases it, and every other step keeps both counts. -/
theorem clc_key (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d)
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : Consumer.next L g d e = some (some d')) :
    d.clcHold + (if okPoll (clcResp L g) e then 1 else 0) =
      (if Execution.isBarId (tidOf L g / 32 / 4 + 1) e then 1 else 0) + d'.clcHold := by
  obtain ⟨hW, hA⟩ := clc_sites hpre hg hi hat.2.2.2.2 hc hf
  obtain ⟨hok, -⟩ := clc_off hW hA
  have hbar : d.site ≠ .clcBar → Execution.isBarId (tidOf L g / 32 / 4 + 1) e = false :=
    fun hs => Bool.eq_false_iff.mpr fun h => hs (isBarId_clcBar hpre hat hc hf h)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat.2.2.2.2 hc hf
    obtain ⟨h1, -⟩ := okPoll_clc (L := L) (g := g) (pc := Site.clcWait.pc) (p := p) (ok := ok)
      (acq := acq) (sc := sc)
    simp only [Consumer.next, Option.some.injEq] at hn
    subst hn
    cases ok <;> simp [h1, Execution.isBarId, D.clcHold]
  case clcBar =>
    have hB : Execution.isBarId (tidOf L g / 32 / 4 + 1) e = true := by
      rw [clcBar_event hpre hat hc hf rfl]
      simp [Execution.isBarId]
    have hO : okPoll (clcResp L g) e = false := hok (by simp)
    simp only [Consumer.next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp [D.clcHold, hO, hB]
  all_goals (clear hat hc hf hW hA; dsimp only at hok hbar)
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hok hbar
  all_goals simp only [Consumer.next] at hn
  clc_sweep hn
  all_goals simp [D.clcHold, hok, hbar]

/-- A consumer's step polls no accumulator-full barrier of another accumulator than its own. -/
theorem okPoll_accFull_other (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {j : Nat} (hj2 : j < 2) (hj : j ≠ accIdx L g) : okPoll (accFull L g j) e = false := by
  refine Bool.eq_false_iff.mpr fun h' => hj ?_
  obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h'
  rcases wait_site hpre hi h hc hf hk with ⟨-, hm, -⟩ | ⟨-, hm, -⟩
  · have := congrArg Loc.addr hm
    simp only [Bar.loc, Bar.off] at this
    omega
  · simp only [Bar.loc, Bar.off] at hm
    omega

/-- Only a consumer's response poll and its accumulator arrival move its open task. -/
theorem tileOpen_next_of_ne {L : Launch} {g : Nat} {d d' : D} {e : Event} (hs : d.site ≠ .clcWait)
    (ha : d.site ≠ .accArrive) (hn : Consumer.next L g d e = some (some d')) :
    tileOpen d' = tileOpen d := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs ha
  cases site <;> simp only [Consumer.next] at hn <;> clc_sweep hn <;>
    first | exact absurd rfl hs | exact absurd rfl ha | simp [tileOpen]

/-- A consumer's step opens its task with a successful response poll and closes it with its
accumulator arrival, and moves its response count and its arrival count alike. -/
theorem tile_key (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hi : Inv d) (ht : Consumer.tidOf L g < 256)
    (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : Consumer.next L g d e = some (some d')) :
    (if okPoll (clcResp L g) e then 1 else 0) + tileOpen d =
      (if arrivesOn (accEmpty L g (accIdx L g)) e then 1 else 0) + tileOpen d' := by
  by_cases hs : d.site = .clcWait
  · obtain ⟨p, ok, acq, sc, -, he⟩ := clcWait_event hpre hs hat.2.2.2.2 hc hf
    obtain ⟨hok, -⟩ := okPoll_clc (L := L) (g := g) (pc := d.site.pc) (p := p) (ok := ok)
      (acq := acq) (sc := sc)
    have har : ∀ (pc : Nat) (l : Loc) (p : Nat) (ok acq : Bool) (sc : MbarScope),
        arrivesOn (accEmpty L g (accIdx L g)) (⟨pc, .wait l p ok acq sc⟩ : Event) = false :=
      fun _ _ _ _ _ _ => by simp [arrivesOn, sourceArrive]
    subst he
    simp only [Consumer.next, hs] at hn
    cases ok <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hn <;>
      subst hn <;>
      simp only [hok, har, Bool.false_eq_true, ↓reduceIte] <;>
      simp [tileOpen, hs]
  by_cases ha : d.site = .accArrive
  · obtain ⟨rel, sc, he⟩ := accArrive_event hpre hg ha hat.2.2.2.2 hc hf
    subst he
    simp only [Consumer.next, ha, Option.some.injEq] at hn
    subst hn
    have hk : okPoll (clcResp L g) (⟨d.site.pc, .arrive (accEmpty L g (accIdx L g)) 0 1 rel sc⟩ :
        Event) = false := okPoll_notWait fun l p ok acq sc h => by cases h
    rw [hk, arrivesOn_arrive rfl]
    simp [tileOpen, ha]
  have hW : okPoll (clcResp L g) e = false := by
    refine Bool.eq_false_iff.mpr fun h' => hs ?_
    obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h'
    exact ((clc_sites hpre hg hi hat.2.2.2.2 hc hf).1 p true acq sc hk).1
  have hA : arrivesOn (accEmpty L g (accIdx L g)) e = false := by
    refine Bool.eq_false_iff.mpr fun h' => ha ?_
    obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form h'
    rcases arrive_site hpre hg hat.2.2.2.2 hc hf hk with ⟨h1, -⟩ | ⟨-, hl⟩
    · exact h1
    · simp only [Bar.loc, Bar.off, accIdx] at hl
      omega
  simp [hW, hA, tileOpen_next_of_ne hs ha hn]

end Consumer

/-- Along a thread's run its CLC counts hold (`ClcPollInv`). -/
theorem clcPoll_inv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ClcPollInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ClcPollInv L g) ⟨quiet_nil, rfl⟩ ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · obtain ⟨hq1, hq2⟩ := hq
    have hb : (pre ++ [e]).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) = 0 := by
      simp [List.countP_append, hq2, prologue_no_barId (Consumer.tidOf L g / 32 / 4 + 1) hc hf]
    have hq' : Quiet (pre ++ [e]) := hq1.snoc (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact ⟨hq', hb⟩
    all_goals try trivial
    obtain rfl := Prologue.next_cons hn
    have h0 : Prologue.consStart.clcHold = 0 := rfl
    have h3 : Consumer.tileOpen Prologue.consStart = 0 := rfl
    have h1 := (hq' (clcResp L g)).1
    have h2 := (hq' (Consumer.accEmpty L g (Consumer.accIdx L g))).2.1
    show okPolls (clcResp L g) (pre ++ [e]) =
        (pre ++ [e]).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) +
          Prologue.consStart.clcHold ∧
      okPolls (clcResp L g) (pre ++ [e]) =
        arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) (pre ++ [e]) +
          Consumer.tileOpen Prologue.consStart ∧
      ∀ j, j < 2 → j ≠ Consumer.accIdx L g → okPolls (Consumer.accFull L g j) (pre ++ [e]) = 0
    refine ⟨?_, ?_, fun j _ _ => (hq' _).1⟩
    · rw [hb, h0]
      omega
    · rw [h2, h3, h1]
  · obtain ⟨l', -, rfl⟩ := next_of_loader hn; trivial
  · obtain ⟨m', -, rfl⟩ := next_of_mma hn; trivial
  · obtain ⟨s', -, rfl⟩ := next_of_sched hn; trivial
  · obtain ⟨c', hc', rfl⟩ := next_of_cons hn
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hk := Consumer.clc_key hpre hg hinv.1 hat hc hf hc'
    have ht := Consumer.tile_key hpre hg hinv.1 hinv.2.1 hat hc hf hc'
    have hz : ∀ j, j < 2 → j ≠ Consumer.accIdx L g → okPoll (Consumer.accFull L g j) e = false :=
      fun j hj hn => Consumer.okPoll_accFull_other hpre hinv.1 hat.2.2.2.2 hc hf hj hn
    show okPolls (clcResp L g) (pre ++ [e]) =
        (pre ++ [e]).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c'.clcHold ∧
      okPolls (clcResp L g) (pre ++ [e]) =
        arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) (pre ++ [e]) +
          Consumer.tileOpen c' ∧
      ∀ j, j < 2 → j ≠ Consumer.accIdx L g → okPolls (Consumer.accFull L g j) (pre ++ [e]) = 0
    refine ⟨?_, ?_, ?_⟩
    · rw [okPolls_snoc, List.countP_append, List.countP_singleton]
      omega
    · rw [okPolls_snoc, arrivals_snoc]
      omega
    · intro j hj hn
      rw [okPolls_snoc, hz j hj hn, hq3 j hj hn]
      simp

/-- A consumer's successful polls of its CTA's CLC response barrier are its arrivals on its group's
CLC barrier, plus the response it holds (`Consumer.D.clcHold`). -/
theorem cons_clc {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) =
      ((X.tr g).take k).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) + c.clcHold :=
        by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨h1, -, -⟩ := clcPoll_inv hpre hg htr k _ hσ
  exact h1

/-- A consumer at the end of its trace: its successful accumulator-full polls and its open task are
its successful response polls, less the accumulator it holds, plus the open task of the response
it polls (`Consumer.tileOpen`): each task is one response poll, one accumulator poll and one
accumulator arrival. -/
theorem cons_tiles {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) :
    consCount L g (X.tr g) + Consumer.tileOpen c =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) + Consumer.holds c := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hT := clcPoll_inv hpre hg htr (X.tr g).length _ hσ
  have hA := Consumer.accInv hpre hg htr (X.tr g).length _ hσ
  rw [List.take_length] at hT hA
  obtain ⟨-, hT2, hO⟩ := hT
  obtain ⟨hC, -, -⟩ := hA
  have hacc : Consumer.accIdx L g < 2 := by
    have hw := role_warp hpre hX hg (X.tr g).length le_rfl (.cons c) hσ
    simp only [roleWarp, Prologue.warpOf, Consumer.accIdx, Consumer.tidOf] at hw ⊢
    omega
  have hsum : consCount L g (X.tr g) =
      okPolls (Consumer.accFull L g (Consumer.accIdx L g)) (X.tr g) := by
    unfold consCount
    rw [Finset.sum_eq_single (⟨Consumer.accIdx L g, hacc⟩ : Fin 2)]
    · intro b _ hb
      exact hO b b.isLt fun h => hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hC1 := hC (Consumer.accIdx L g) hacc
  simp only [↓reduceIte] at hC1
  have hT3 : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) =
      arrivals (Consumer.accEmpty L g (Consumer.accIdx L g)) (X.tr g) + Consumer.tileOpen c := hT2
  rw [hsum, hC1, hT3]
  omega

/-- A consumer's CLC barrier arrival follows a proxy fence after its latest successful poll of its
CTA's CLC response barrier. -/
theorem cons_clc_fence {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) (hs : c.site = .clcBar) :
    ∃ j f, j < k ∧ X.get (g, j) = some f ∧
      f.kind = .fenceProxy (.async (some (.shared .cta))) none ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨-, hm, -⟩ := clcInv hpre hg htr k _ hσ
  obtain ⟨j, f, hj, hfj, hfe, hcount⟩ :=
    hm (by simp [Prologue.Role.clcFenced, Consumer.D.clcFenced, hs])
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  simp only [List.length_take, Nat.min_eq_left hk'] at hj
  refine ⟨j, f, hj, ?_, ?_, ?_⟩
  · rwa [List.getElem?_take_of_lt hj] at hfj
  · unfold isFence at hfe
    split at hfe
    · assumption
    · cases hfe
  · rwa [List.take_take, Nat.min_eq_left hj.le] at hcount

/-- A consumer's acknowledgement arrival on the CLC acknowledgement barrier happens at a state
holding no CLC response (its `clcHold` is 0). -/
theorem ack_hold {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) {tx n : Nat} {rel : Bool}
    {sc : MbarScope} (ha : e.kind = .arrive (clcAck L g) tx n rel sc) : c.clcHold = 0 := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hs := (Consumer.clc_sites hpre hg hinv.1 hat.2.2.2.2 hc hfire).2 tx n rel sc ha
  simp [Consumer.D.clcHold, hs]

end
end PTX.Kernels.Fp16Gemm8192.Proof
