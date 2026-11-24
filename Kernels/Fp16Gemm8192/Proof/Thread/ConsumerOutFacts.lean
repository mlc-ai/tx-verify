-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTc
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerTiles
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerVals
public import Lemmas.Flow.OpPcsFast
public import Kernels.Fp16Gemm8192.Proof.Thread.ReaderExitCons

@[expose] public section

/-! # A consumer's output events, along an execution

Along a consumer's run its output barrier arrivals and commits satisfy `OutRel`, its writes, TMA
stores and bulk waits are at its staging stores, TMA stores and drains, and each TMA store follows
its proxy fence (`cons_out_facts`). One run invariant `ConsInv` carries these and the exit facts
(`consumer_exit`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The kernel's stores are its staging stores and the allocation write (decided on the code). -/
theorem kernel_write_pcs :
    OpPcs kernel.code writeOp (Flow.store.toList ++ Flow.tmemAlloc.toList) = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- The kernel's tensor stores are its slices' TMA stores (decided on the code). -/
theorem kernel_tensorStore_pcs :
    OpPcs kernel.code tensorStoreOp (Flow.tensorCopy.toList.drop 24) = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- The kernel's bulk waits are its drains (decided on the code). -/
theorem kernel_bulkWait_pcs : OpPcs kernel.code bulkWaitOp Flow.bulkWait.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A consumer's stores, TMA stores and bulk waits are at its staging stores, its TMA stores and
its drains (decided on the code). -/
theorem out_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    (∀ a bs, e.kind = .wr a bs → ∃ k i el, d.site = .store k i el) ∧
      (∀ a sp, e.kind = .tensorStore a sp → ∃ k, d.site = .tma k) ∧
      ∀ m r, e.kind = .bulkWait m r → (∃ k, d.site = .drain k) ∨ d.site = .finalDrain := by
  refine ⟨fun a bs hk => ?_, fun a sp hk => ?_, fun m r hk => ?_⟩
  · have hpc := OpPcs.mem kernel_write_pcs hc (fires_write_op hf hk)
    clear hc hf hk; site_of_pc d hpc
  · have hpc := OpPcs.mem kernel_tensorStore_pcs hc (fires_tensorStore_op hf hk)
    clear hc hf hk; site_of_pc d hpc
  · have hpc := OpPcs.mem kernel_bulkWait_pcs hc (fires_bulkWait_op hf hk)
    clear hc hf hk; site_of_pc d hpc

theorem drainRel_step {d d' : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : DrainRel pre d) : DrainRel (pre ++ [e]) d' := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case drain j =>
      have := drain_event hc hf (k := j) rfl
      rw [this]
      exact ⟨_, List.getLast?_concat⟩
    all_goals exfalso
    all_goals clear hc hf hq1 hq2 hq3
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all
  · intro hk
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case commit j =>
      have he : e = ⟨(Site.commit j).pc, .bulkCommit⟩ := by
        obtain ⟨ins', hc', -⟩ := epi_commit_code j
        have := hc.symm.trans hc'
        fin_cases j <;> code_at hc <;> subst hc <;> exact fires_bulkCommit hf
      rw [he]
      exact ⟨_, List.getLast?_concat⟩
    all_goals exfalso
    all_goals clear hc hf hq1 hq2 hq3
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all
  · intro hk
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case finalDrain =>
      have he := finalDrain_event hc hf rfl
      obtain ⟨pc, hlast⟩ := hq2 rfl
      have hne : pre ≠ [] := by
        rintro rfl
        simp at hlast
      have hpos : 0 < pre.length := List.length_pos_iff.mpr hne
      refine ⟨pre.length, (Site.finalDrain).pc, pc, hpos, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (le_refl _), he]
        simp
      · rw [List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?]
        exact hlast
      · intro i hi e' a s he'
        have hi' : i = pre.length := by
          have := (List.getElem?_eq_some_iff.mp he').1
          simp only [List.length_append, List.length_singleton] at this
          omega
        subst hi'
        rw [List.getElem?_append_right (le_refl _)] at he'
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at he'
        subst he'
        intro hk'
        rw [he] at hk'
        cases hk'
    case exitArrive | exitWait | relinquish | ldBase | dealloc =>
      obtain ⟨j, pc, pc', hj, h1, h2, h3⟩ := hq3 rfl
      have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp h1).1
      refine ⟨j, pc, pc', hj, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_left hjl]
        exact h1
      · rw [List.getElem?_append_left (by omega)]
        exact h2
      · intro i hi e' a s he'
        by_cases hil : i < pre.length
        · rw [List.getElem?_append_left hil] at he'
          exact h3 i hi e' a s he'
        · have hi' : i = pre.length := by
            have := (List.getElem?_eq_some_iff.mp he').1
            simp only [List.length_append, List.length_singleton] at this
            omega
          subst hi'
          rw [List.getElem?_append_right (le_refl _)] at he'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at he'
          subst he'
          intro hk'
          obtain ⟨k', hk''⟩ := (out_site hc hf).2.1 a s hk'
          cases hk''
    all_goals exfalso
    all_goals clear hc hf hq1 hq2 hq3
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all [D.drained]

theorem TmaRel.keep {d d' : D} {es : List Event} {e : Event} (h : TmaRel L g d es)
    (hs : isTensorStore e = false) (hc : isCommit e = false) (hp : d'.tmaPend = d.tmaPend)
    (hf : ∀ k, d'.site = .fence k ∨ d'.site = .tma k → first L g = true) :
    TmaRel L g d' (es ++ [e]) := by
  refine ⟨hf, fun hnu => ?_⟩
  rw [storeIssues_snoc, (counts_snoc (L := L) (g := g) es e).2, hs, hc, hp]
  simpa using h.2 fun x hx => hnu x (List.mem_append_left _ hx)

set_option maxHeartbeats 8000000 in
theorem tmaRel_step {d d' : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : TmaRel L g d pre) : TmaRel L g d' (pre ++ [e]) := by
  have hS : (∀ k, d.site ≠ .tma k) → isTensorStore e = false := by
    intro hT
    unfold isTensorStore
    split
    · rename_i a sp hk
      obtain ⟨k, hs⟩ := (out_site hc hf).2.1 a sp hk
      exact absurd hs (hT k)
    · rfl
  have hC : (∀ k, d.site ≠ .commit k) → isCommit e = false := by
    intro hT
    unfold isCommit
    split
    · rename_i hk
      have hpc := OpPcs.mem kernel_commit_pcs hc (fires_bulkCommit_op hf hk)
      obtain ⟨k, hs⟩ : ∃ k, d.site = .commit k := by
        clear hn hq hT hc hf hk hS
        site_of_pc d hpc
      exact absurd hs (hT k)
    · rfl
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case tma k =>
    have hfirst := hq1 k (.inr rfl)
    have hcm := hC (fun _ h => by cases h)
    simp only [next, Option.some.injEq] at hn
    subst hn
    refine ⟨fun _ h => by simp at h, fun hnu => ?_⟩
    obtain ⟨cs, pol, hop⟩ : ∃ cs pol, ins.op = .cpTensorStore (.reg (tmaMap k)) cs
        (tmaSrc (k.val % 2)) 0 pol .tile none := by
      simp only at hc
      fin_cases k <;> code_at hc <;> subst hc <;> exact ⟨_, _, rfl⟩
    rw [hop] at hf
    have hst : isTensorStore e = true := by
      rcases fires_cpTensorStore_kind hf with ⟨a, sp, hk⟩ | ⟨f, hk⟩
      · simp [isTensorStore, hk]
      · exact absurd hk (hnu e (List.mem_append_right _ (List.mem_singleton.mpr rfl)) f)
    rw [storeIssues_snoc, (counts_snoc (L := L) (g := g) pre e).2, hst, hcm,
      hq2 fun x hx => hnu x (List.mem_append_left _ hx)]
    simp [hfirst, D.tmaPend]
  case commit k =>
    have he : e = ⟨(Site.commit k).pc, .bulkCommit⟩ := by
      obtain ⟨ins', hc', -⟩ := epi_commit_code k
      have := hc.symm.trans hc'
      fin_cases k <;> code_at hc <;> subst hc <;> exact fires_bulkCommit hf
    subst he
    refine ⟨fun k' hk' => ?_, fun hnu => ?_⟩
    · simp only [next] at hn
      split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;> simp at hk'
    · have h2 := hq2 fun x hx => hnu x (List.mem_append_left _ hx)
      rw [storeIssues_snoc, (counts_snoc (L := L) (g := g) pre _).2]
      simp only [isTensorStore, isCommit, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, D.tmaPend]
        at h2 ⊢
      simp only [next] at hn
      split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
        split_ifs at h2 ⊢ <;> omega
  case barB k =>
    have hs := hS (fun _ h => by cases h)
    have hcm := hC (fun _ h => by cases h)
    simp only [next] at hn
    split_ifs at hn with hfirst <;> simp only [Option.some.injEq] at hn <;> subst hn
    · exact TmaRel.keep ⟨hq1, hq2⟩ hs hcm (by simp [D.tmaPend]) fun _ _ => hfirst
    · refine ⟨fun _ h => by simp at h, fun hnu => ?_⟩
      rw [storeIssues_snoc, (counts_snoc (L := L) (g := g) pre e).2, hs, hcm]
      have h2 := hq2 fun x hx => hnu x (List.mem_append_left _ hx)
      simp only [hfirst, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
      simpa using h2
  case fence k =>
    have hs := hS (fun _ h => by cases h)
    have hcm := hC (fun _ h => by cases h)
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact TmaRel.keep ⟨hq1, hq2⟩ hs hcm (by simp [D.tmaPend]) fun _ _ => hq1 k (.inl rfl)
  all_goals have hs := hS (fun _ h => by cases h)
  all_goals have hcm := hC (fun _ h => by cases h)
  all_goals clear hS hC hc hf
  all_goals refine TmaRel.keep ⟨hq1, hq2⟩ hs hcm ?_ ?_
  all_goals simp only [next] at hn
  all_goals clear hq1 hq2 hs hcm
  clc_sweep hn
  all_goals simp [D.tmaPend]

end Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- No prologue event is a tensor store. -/
theorem prologue_no_store {p : Prologue.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o) : isTensorStore e = false := by
  obtain ⟨site, w⟩ := p
  simp only at hc hf
  unfold isTensorStore
  split
  · rename_i a sp hk
    have hpc := OpPcs.mem kernel_tensorStore_pcs hc (fires_tensorStore_op hf hk)
    clear hc hf hk
    exfalso
    revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · rfl

/-- The run invariant of a consumer's thread: a prologue state has no output barrier arrival, no
commit and no tensor store, and a consumer state has its output counts (`OutRel`), its CLC query,
its exit read when it is doomed, its fence and drain relations, its TMA stores (`TmaRel`) and its
reads of responses (`ReadInv`). -/
def ConsInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Consumer.outBars L g es = 0 ∧ commits es = 0 ∧ Quiet es ∧ dataOps es = 0 ∧
      storeIssues es = 0
  | .inr (.cons c), es => Consumer.OutRel L g c es ∧ QueryRel L g c.clcStage c.resp es ∧
      (c.doomed → FailRead L g es) ∧ Consumer.FenceRel es c ∧ Consumer.DrainRel es c ∧
      Consumer.OutTile L g c es ∧ Consumer.TcTile L g c es ∧
      (Consumer.StoreRel L g c es ∧ Consumer.ValRel L g c es) ∧
      Consumer.BarRel L g c es ∧ Consumer.TileRel L g c es ∧ Consumer.TmaRel L g c es ∧
      Consumer.ReadInv L g c es
  | _, _ => True

theorem consInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ConsInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ConsInv L g) ⟨rfl, rfl, quiet_nil, rfl, rfl⟩ ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · obtain ⟨hb, hcm⟩ := prologue_no_bar hc hf
    obtain ⟨h1, h2⟩ := Consumer.counts_snoc (L := L) (g := g) pre e
    simp only [hb, hcm, hq.1, hq.2.1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 h2
    have hq' : Quiet (pre ++ [e]) := hq.2.2.1.snoc (Prologue.fires_quiet hc hf)
    have hst : storeIssues (pre ++ [e]) = 0 := by
      rw [storeIssues_snoc, prologue_no_store hc hf, hq.2.2.2.2]
      rfl
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact ⟨h1, h2, hq', by
        rw [dataOps_snoc, Prologue.not_tcData hc hf]; simpa using hq.2.2.2.1, hst⟩
    all_goals try trivial
    rw [Prologue.next_cons hn]
    refine ⟨⟨by rw [h1]; rfl, by rw [h1, h2]; rfl⟩, QueryRel.zero,
      fun h => by simp [Consumer.D.doomed, Prologue.consStart] at h,
      fun k hk => by simp [Prologue.consStart] at hk,
      ⟨fun k hk => by simp [Prologue.consStart] at hk,
        fun hk => by simp [Prologue.consStart] at hk,
        fun hk => by simp [Prologue.consStart, Consumer.D.drained] at hk⟩, ?_, ?_,
      ⟨fun _ k n hpos => by simp [Consumer.D.storePos, Prologue.consStart] at hpos,
        fun ch hch => by simp [Consumer.D.loaded, Prologue.consStart] at hch,
        fun _ k n hpos => by simp [Consumer.D.storePos, Prologue.consStart] at hpos⟩,
      ⟨fun k hk => by simp [Prologue.consStart] at hk,
        fun k hk => by simp [Prologue.consStart] at hk⟩,
      ⟨fun _ => (hq' _).1, fun h => absurd rfl h, fun h => by simp [Consumer.D.clcStage,
        Prologue.consStart] at h, fun h => by simp [Consumer.D.afterQuery, Prologue.consStart] at h,
        fun h => by simp [Consumer.D.afterBar, Prologue.consStart] at h,
        fun k hk => by simp [Prologue.consStart] at hk⟩,
      ⟨fun k hk => by simp [Prologue.consStart] at hk, fun _ => by
        rw [hst, h2]
        split <;> rfl⟩,
      ⟨FailRel.of_quiet (hq' _).1, fun h => by simp [Prologue.consStart] at h,
        fun h => by simp [Prologue.consStart] at h⟩⟩
    · simp [Consumer.OutTile, h1, (hq' (Consumer.accEmpty L g (Consumer.accIdx L g))).2.1,
        Consumer.D.inEpi, Consumer.D.outPhase, Consumer.D.started, Prologue.consStart]
    · simp [Consumer.TcTile, dataOps_snoc, Prologue.not_tcData hc hf, hq.2.2.2.1,
        (hq' (Consumer.accEmpty L g (Consumer.accIdx L g))).2.1, Consumer.D.tcPos,
        Prologue.consStart]
  · obtain ⟨l', -, rfl⟩ := next_of_loader hn; trivial
  · obtain ⟨m', -, rfl⟩ := next_of_mma hn; trivial
  · obtain ⟨s', -, rfl⟩ := next_of_sched hn; trivial
  · obtain ⟨c', hc', rfl⟩ := next_of_cons hn
    obtain ⟨hinv1, htid, -⟩ := hinv
    exact ⟨Consumer.out_step hpre hat hc hf hc' hq.1,
      Consumer.query_step hpre hat hc hf hc' hq.2.1,
      Consumer.exit_step hat hc hf hc' hq.2.1 hq.2.2.1,
      Consumer.fenceRel_step hc hf hc', Consumer.drainRel_step hc hf hc' hq.2.2.2.2.1,
      Consumer.tile_step hpre hg hat hc hf hc' hq.2.2.2.2.2.1,
      Consumer.tc_step hpre hg hat hc hf hc' hq.2.2.2.2.2.2.1,
      ⟨Consumer.storeRel_step hpre hat htid hc hf hc' hq.2.2.2.2.2.2.2.1.1,
        Consumer.valRel_step hpre hg hat htid hc hf hc' hq.2.2.2.2.2.2.2.1.2⟩,
      Consumer.barRel_step hpre hat hc hf hc' hq.2.2.2.2.2.2.2.2.1,
      Consumer.tileRel_step hpre hg hinv1 hat hc hf hc' hq.2.2.2.2.2.2.2.2.2.1 hq.2.1,
      Consumer.tmaRel_step hc hf hc' hq.2.2.2.2.2.2.2.2.2.2.1,
      Consumer.read_step hpre hg hinv1 hat hc hf hc' hq.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A consumer's reads of responses at a state of its run (`ReadInv`). -/
theorem Consumer.readInv_of {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) : Consumer.ReadInv L g c ((X.tr g).take k) :=
  (consInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ).2.2.2.2.2.2.2.2.2.2.2

/-- **A consumer at its response wait has read no non-claiming response after a successful
response poll**: each read after a successful poll of its CTA's response barrier names a response
that claims a CTA, while the thread waits for its next response. -/
theorem Consumer.fail_wait {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.cons c))))
    (hs : c.site = .clcWait) :
    ∀ j pc p acq sc pcr src bs rr, (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g → src.size = 16 →
      Flow.responseOf bs = some rr → Loader.claims rr := by
  have h := Consumer.readInv_of hpre hX hg (k := (X.tr g).length)
    (by rw [List.take_length]; exact hσ)
  rw [List.take_length] at h
  intro j pc p acq sc pcr src bs rr ha hb hl hs' hr
  by_contra hc
  have h3 := (h.1.1 j pc p acq sc pcr src bs rr ha hb hl hs' hr hc).2
  simp [Consumer.NcSite, hs] at h3

/-- A consumer's output events along an execution: its output barrier arrivals and commits
(`OutRel`), its staging stores, its TMA stores (each right after its proxy fence), its drains
and its barriers. -/
theorem cons_out_facts {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) (htid : Consumer.tidOf L g < 256) :
    Consumer.OutRel L g c ((X.tr g).take k) ∧
    (∀ a bs, e.kind = .wr a bs → ∃ s i el, c.site = .store s i el ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase +
        Consumer.stagingOff (Consumer.tidOf L g) (s.val % 2) i el⟩ ∧
      a.size = 4) ∧
    (∀ a sp, e.kind = .tensorStore a sp → ∃ s, c.site = .tma s ∧ a = P.dMap ∧
      (⟨sp.outer, sp.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨1, Fp16Gemm8192.mapD P.dBase P.dClass⟩ ∧
      sp.sharedBase = ⟨.shared, g / L.block, L.sharedBase +
        Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2)⟩ ∧
      (∀ x y b l, TensorStore.readLoc sp x y b = some l → l.space = .shared ∧
        l.cta = g / L.block ∧
        L.sharedBase + Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2) ≤ l.addr ∧
        l.addr < L.sharedBase + Consumer.stagingBase (Consumer.tidOf L g) (s.val % 2) + 8192) ∧
      ∃ pc, 0 < k ∧ X.get (g, k - 1) = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
    (∀ m r, e.kind = .bulkWait m r → (∃ s, c.site = .drain s ∧ m = .read ∧ r = 1) ∨
      (c.site = .finalDrain ∧ m = .full ∧ r = 0)) ∧
    (∀ id cnt, e.kind = .bar id cnt →
      (c.site = .clcBar ∧ id = Consumer.tidOf L g / 32 / 4 + 1 ∧ cnt = some 128) ∨
      ((∃ s, c.site = .barA s ∨ c.site = .barB s) ∧ id = Consumer.outId L g ∧ cnt = some 128)) ∧
    (∀ s, c.site = .barA s → ∃ pc, 0 < k ∧ X.get (g, k - 1) = some ⟨pc, .bulkWait .read 1⟩) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[c.site.pc]? = some ins at hc
  change Fires c.site.pc (eventTmpl Prod L g t ins.op) e o at hfire
  obtain ⟨hout, -, -, hfen, hdrn, -, -⟩ : ConsInv L g (.inr (.cons c)) ((X.tr g).take k) :=
    consInv hpre hg htr k _ hσ
  obtain ⟨wrS, tnS, bwS⟩ := Consumer.out_site hc hfire
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  refine ⟨hout, fun a bs hk => ?_, fun a sp hk => ?_, fun m r hk => ?_, fun id cnt hk => ?_,
    fun s hs => ?_⟩
  · obtain ⟨s, i, el, hs⟩ := wrS a bs hk
    exact ⟨s, i, el, hs, Consumer.store_event hpre hat htid hc hfire hs a bs hk⟩
  · obtain ⟨s, hs⟩ := tnS a sp hk
    obtain ⟨h1, h2, h3⟩ := Consumer.tma_event hpre hat htid hc hfire hs a sp hk
    obtain ⟨pc, hl⟩ := hfen s hs
    have hpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hl)
    refine ⟨s, hs, h1, h2, h3, fun x y b l hl' => ?_, pc, hpos, ?_⟩
    · have := Consumer.mapD_readLoc h2 hl'
      rw [h3] at this
      exact this
    rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk',
      List.getElem?_take_of_lt (by omega)] at hl
    exact hl
  · rcases bwS m r hk with ⟨s, hs⟩ | hs
    · rw [Consumer.drain_event hc hfire hs] at hk; cases hk; exact .inl ⟨s, hs, rfl, rfl⟩
    · rw [Consumer.finalDrain_event hc hfire hs] at hk; cases hk; exact .inr ⟨hs, rfl, rfl⟩
  · rcases Consumer.bar_site hc hfire hk with hs | ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [Consumer.clcBar_event hpre hat hc hfire hs] at hk; cases hk
      exact .inl ⟨hs, rfl, rfl⟩
    · rw [Consumer.out_bar_event hpre hat hc hfire (.inl hs)] at hk; cases hk
      exact .inr ⟨⟨s, .inl hs⟩, rfl, rfl⟩
    · rw [Consumer.out_bar_event hpre hat hc hfire (.inr hs)] at hk; cases hk
      exact .inr ⟨⟨s, .inr hs⟩, rfl, rfl⟩
  · obtain ⟨pc, hl⟩ := hdrn.1 s hs
    have hpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hl)
    refine ⟨pc, hpos, ?_⟩
    rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk',
      List.getElem?_take_of_lt (by omega)] at hl
    exact hl

/-- A consumer's exit follows a successful poll of its CTA's response barrier and the read,
right after it, of a response that claims no CTA. -/
theorem consumer_exit {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) (hk : e.kind = .exit) :
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr, j + 1 < k ∧
      X.get (g, j) = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
      X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
      src.loc = respLoc L g ∧ src.size = 16 ∧ Flow.responseOf bs = some rr ∧
      ¬ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hs := Consumer.exit_site hc hfire hk
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hw, hr, h1, h2, h3, h4⟩ :=
    (consInv hpre hg htr k _ hσ).2.2.1 (by simp [Consumer.D.doomed, hs])
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hl : j + 1 < k := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    simp only [List.length_take, Nat.min_eq_left hk'] at this
    exact this
  rw [List.getElem?_take_of_lt (by omega)] at hw
  rw [List.getElem?_take_of_lt hl] at hr
  exact ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hl, hw, hr, h1, h2, h3, h4⟩

/-- A consumer's exit follows its final drain: the bulk wait for every group, right after a bulk
commit, before which every tensor store of the thread lies. -/
theorem cons_exit_drain_fact {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c)))) :
    ∃ j pcw pcc, 0 < j ∧ j < k ∧ X.get (g, j) = some ⟨pcw, .bulkWait .full 0⟩ ∧
      X.get (g, j - 1) = some ⟨pcc, .bulkCommit⟩ ∧
      ∀ i, j ≤ i → i < k → ∀ pc' a s, X.get (g, i) ≠ some ⟨pc', .tensorStore a s⟩ := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hs := Consumer.exit_site hc hfire rfl
  obtain ⟨j, pcw, pcc, hj, h1, h2, h3⟩ :=
    ((consInv hpre hg htr k _ hσ).2.2.2.2.1).2.2 (by simp [Consumer.D.drained, hs])
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp h1).1
    simp only [List.length_take] at this
    omega
  refine ⟨j, pcw, pcc, hj, hjk, ?_, ?_, ?_⟩
  · have := h1
    rw [List.getElem?_take_of_lt hjk] at this
    exact this
  · have := h2
    rw [List.getElem?_take_of_lt (by omega)] at this
    exact this
  · intro i hi hik pc' a s hget
    have hget' : ((X.tr g).take k)[i]? = some ⟨pc', .tensorStore a s⟩ := by
      rw [List.getElem?_take_of_lt hik]
      exact hget
    exact h3 i hi _ a s hget' rfl

/-- Only consumers arrive on named barriers: no other state is at a barrier. -/
theorem bar_role {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    {id : Nat} {cnt : Option Nat} (hk : e.kind = .bar id cnt) : ∃ c, d = .inr (.cons c) := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hpc := OpPcs.mem kernel_bar_pcs hc (fires_bar_op hfire hk)
  clear hc hfire hσ
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | c)
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Loader.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Mma.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Scheduler.Site.pc] <;> decide +revert
  · exact ⟨c, rfl⟩

/-- A bulk-group wait is a consumer's (its sites are the consumer's drain waits). -/
theorem bulk_role {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {d : ThreadD}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d))
    {m : BulkGroup.WaitMode} {r : Nat} (hk : e.kind = .bulkWait m r) : ∃ c, d = .inr (.cons c) := by
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hpc := OpPcs.mem kernel_bulkWait_pcs hc (fires_bulkWait_op hfire hk)
  clear hc hfire hσ
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | c)
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Loader.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Mma.Site.pc] <;> decide +revert
  · exfalso; change site.pc ∈ _ at hpc; revert hpc
    cases site <;> simp only [Scheduler.Site.pc] <;> decide +revert
  · exact ⟨c, rfl⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
