-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Ordered
public import Lemmas.Step.MmaDrain

@[expose] public section

/-! # The bytes an MMA reads

An MMA thread's poll for use `n` observed every copy of production `n` (`copy_exists`). An MMA of
production `n` reads at each operand byte the write of production `n`'s copy of that byte, which
precedes it (`copy_before_read`); every other write of the byte is a tensor load of another
production, ordered before that write or after the read (`write_read`). So the MMA's operand bytes
have sources (`operandSources`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every copy of a production has completed by its poll.** MMA thread `b`'s successful full
poll for use `p` observed, for each producer `a` and each `i < 3`, the completion of `a`'s tensor
issue on the slot with `3 p + i` earlier issues there (`consumer_observes`). -/
theorem copy_exists (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {b : Fin 2} {p : Nat}
    (hp : p < okPolls ((slot L c s).full 0) (X.tr (consumerOf L X c s b))) (a : Fin 2) (i : Nat)
    (hi : i < 3) :
    ∃ (g k pc al : Nat) (sp : TensorCopy.Spec) (jd : Nat) (d : Record Ref),
      X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩ ∧
      sp.mbar = (slot L c s).full 0 ∧ g / L.block % 2 = a.val ∧
      ((X.tr g).take k).countP (issuesTo ((slot L c s).full 0)) = 3 * p + i ∧
      (X.objects ((slot L c s).full 0))[jd]? = some d ∧ d.id = .async (g, k) (.notify .load) ∧
      isCompletion d = true := by
  have H := hyp hpre hX ht c s
  have hi' : i < (pslot L X c s).n := hi
  have hk := PairTmaRing.copyKind_ne a i hi'
  obtain ⟨hx, -, -⟩ := PairTmaRing.consumer_observes hX H hp (PairTmaRing.copyKind _ a i hi')
  obtain ⟨⟨jd, d, hd, hid, hf, -, h1⟩, ⟨e, he, hpe, hcnt⟩, -⟩ := PairTmaRing.SF_op H hx
  have hda := h1 hk
  simp only [PairTmaRing.opF_ne hk, PairTmaRing.kOwner_copyKind, PairTmaRing.kPred_ne hk,
    PairTmaRing.kIdx_copyKind] at he hpe hcnt
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | tensorIssue al sp =>
    simp only [issuesTo, decide_eq_true_eq] at hpe
    have hpa := producerOf_thread (X := X) hpre c s a
    simp only [producerThread, decide_eq_true_eq] at hpa
    refine ⟨_, _, pc, al, sp, jd, d, he, hpe, by simp only [pslot]; omega, hcnt, hd, ?_,
      (isCompletion_iff d).mpr ⟨hda, hf⟩⟩
    rw [hid, PairTmaRing.itF_ne hk, PairTmaRing.kOwner_copyKind, PairTmaRing.kIdx_copyKind]
  | _ => simp [issuesTo] at hpe

/-- An MMA of the MMA thread of selector `b` of cluster `c`, at slot `s`, K step `jj`. -/
theorem mma_at (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X)
    {g k dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue (g, k) dst sp acc mask) :
    ∃ (s jj : Fin 4) (b : Fin 2), g = consumerOf L X (g / L.block / 2) s b ∧
      2 * (g / L.block / 2) = g / L.block ∧ g % L.block / 32 = 8 + b.val ∧
      sp = mmaSpec L (g / L.block) (g % L.block / 32) s.val jj.val ∧
      ((X.tr g).take k).countP (commitsTo ((slot L (g / L.block / 2) s).empty 0)) + 1 =
        okPolls ((slot L (g / L.block / 2) s).full 0) ((X.tr g).take k) ∧
      ∃ m : Mma.D, Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) ∧ m.site =
        .mma s jj := by
  obtain ⟨pc, hget⟩ := hi
  have hg := Frame.lt_of_get hX hget
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
  obtain ⟨m, s, jj, rfl, hms, hlead, hsp, hcnt⟩ := ht.mma_issue hg hget hσ rfl
  have hw := ht.role_warp hg (idx_le hget) hσ
  simp only [roleWarp] at hw
  have hb : g % L.block / 32 - 8 < 2 := by omega
  have hfull : (⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ : Loc) =
      (slot L (g / L.block / 2) s).full 0 := by
    simp only [slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and]
    omega
  have hempty : (⟨.shared, g / L.block, L.sharedBase + 40 + 8 * s.val⟩ : Loc) =
      (slot L (g / L.block / 2) s).empty 0 := by
    simp only [slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and, Fin.val_zero]
    omega
  rw [hfull, hempty] at hcnt
  obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g) (k := k)
    (m := (slot L (g / L.block / 2) s).full 0) (by omega)
  have hcons : consumerThread L (g / L.block / 2) ⟨g % L.block / 32 - 8, hb⟩ g = true := by
    simp only [consumerThread, decide_eq_true_eq]
    omega
  exact ⟨s, jj, ⟨g % L.block / 32 - 8, hb⟩, consumerOf_eq hX ht hcons he', by omega,
    by simp only; omega, hsp, hcnt, m, hσ, hms⟩

/-- A completed copy has written each byte of its box: a byte of the map or the zero fill. -/
theorem completed_writes (hX : Consistent L kernel Prod mem0 X) {gw kw pc al jd : Nat}
    {sp : TensorCopy.Spec} {d : Record Ref} {m : Loc}
    (he : X.get (gw, kw) = some ⟨pc, .tensorIssue al sp⟩)
    (hd : (X.objects m)[jd]? = some d) (hdi : d.id = .async (gw, kw) (.notify .load))
    {base : Nat} {cls : TensorDescriptor.AllocationClass} {origin : Fin 2 → Int} {cta st : Nat}
    {mb : Loc} (hsp : sp = stageCopy (Fp16Gemm8192.mapA base cls) origin cta st mb true .two)
    {x y z : Nat} (hx : x < 64) (hy : y < 128) (hz : z < 2) :
    ∃ v, X.MemWrites (.async (gw, kw) (.write (.load x y z)))
      { loc := ⟨.shared, cta, st + TensorSwizzle.offset .b128 st (128 * y + 2 * x + z)⟩,
        size := 1 } [v] := by
  have hdm := List.mem_of_getElem? hd
  have hobj : objectAction X X.async m (.async (gw, kw) (.notify .load)) = some d.action := by
    have h := ((hX.tma.2.2.1 m).2.1 d hdm).1
    rw [hdi] at h
    exact h
  obtain ⟨o, hobs, hnot⟩ : ∃ o, X.tensor (gw, kw) = some o ∧ o.effects.notified = true := by
    simp only [objectAction, he] at hobj
    cases ho : X.tensor (gw, kw) with
    | none => simp [ho] at hobj
    | some o =>
      by_cases hc : sp.mbar = m ∧ o.effects.notified = true
      · exact ⟨o, rfl, hc.2⟩
      · simp [ho, hc] at hobj
  obtain ⟨⟨addr, pc', hTI⟩, hok, -, -⟩ := hX.tensor (gw, kw) o hobs
  have hspec : o.spec = sp := by
    have h := Option.some.inj (he.symm.trans hTI)
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
    exact h.2.2.symm
  have hwl := box_writeLoc (base := base) (cls := cls) (origin := origin) (cta := cta) (stage := st)
    (mbar := mb) (ca := true) (grp := .two) hx hy hz
  rw [← hsp, ← hspec] at hwl
  obtain ⟨slot, hslot, hsl⟩ := Option.map_eq_some_iff.mp hwl
  obtain ⟨value, hval⟩ := hok.complete hnot slot
  obtain ⟨v, hv⟩ : ∃ v, value.byte = some v := by
    have hw := hok.writes slot value hval
    cases hs : TensorCopy.source o.spec slot with
    | global a =>
      rw [hs] at hw
      dsimp only at hw
      obtain ⟨byte, -, rfl⟩ := hw
      exact ⟨byte, rfl⟩
    | fill mode format byte =>
      rw [hs] at hw
      dsimp only at hw
      subst hw
      have hfill : sp.descriptor.fill = .zero := by rw [hsp]; rfl
      have hfmt : sp.descriptor.format = .f16 := by rw [hsp]; rfl
      unfold TensorCopy.source at hs
      split at hs
      · cases hs
      · injection hs with h1 h2 h3
        rw [hspec, hfill] at h1
        rw [hspec, hfmt] at h2
        subst h1 h2
        exact ⟨_, rfl⟩
  refine ⟨v, o, addr, v, hobs, ⟨pc', hTI⟩, hwl, ?_, by simp⟩
  simp only [TensorCopy.writeByte, hslot, Option.bind_some, hval, hv]

/-- A stage byte of tile `j` of slot `s` is an input stage byte. -/
theorem stageByte_input {s j x y z cta : Nat} (hs : s < 4) (hj : j < 3) (hx : x < 64)
    (hy : y < 128) (hz : z < 2) :
    IsInputStage L (stageByte cta (L.sharedBase + stageOff s j) x y z) := by
  have hr := TensorSwizzle.offset_row .b128 (L.sharedBase + stageOff s j) (128 * y + 2 * x + z)
  have hlt := stageOff_lt hs hj
  have hge : 1024 ≤ stageOff s j := by unfold stageOff; split_ifs <;> omega
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [stageByte] <;> omega

/-- **The copy of an operand element.** An MMA of production `p` (its thread's commits to the
slot before it) reads the two bytes of an operand element from the writes of production `p`'s copy
of that element, which precede the reads; every other write of either byte is a tensor load of
another production of the same loader, ordered before that write or after the read. -/
theorem pair_copy (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hacc : InputAccessors L X) {g km dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, km) dst sp acc mask) (isB : Bool)
    {m : Nat} (hm : m < 4096) :
    ∃ (copy : EvId) (o : TensorCopy.Observation) (x y : Nat), X.tensor copy = some o ∧
      (∃ (mm : Mma.D) (s jj : Fin 4) (lw : Loader.D) (bw : Fin 8) (jw : Fin 3) (pcw alw : Nat),
        Frame.stateAt (code L) X g km = some (some (.inr (.mma mm))) ∧ mm.site = .mma s jj ∧
        X.get copy = some ⟨pcw, .tensorIssue alw o.spec⟩ ∧
        Frame.stateAt (code L) X copy.1 copy.2 = some (some (.inr (.loader lw))) ∧ lw.site =
          .load bw jw ∧
        InputRing.slotOf bw = s ∧ jw.val = (if isB then 2 else g % L.block / 32 % 2) ∧
        copy.1 / L.block = g / L.block / 2 * 2 + m / 16 / 128 ∧
        ((X.tr copy.1).take copy.2).countP (issuesTo (fullLoc L (g / L.block / 2) s)) =
          3 * ((X.tr g).take km).countP (commitsTo (inputEmpty L (g / L.block) s.val)) + jw.val ∧
        x = 16 * jj.val + m % 16 ∧ y = m / 16 % 128) ∧
      ∀ z, z < 2 → ∃ l, sp.byteLoc (if isB then .b else .a) (2 * m + z) = some l ∧
        TensorCopy.writeLoc o.spec x y z = some l ∧ (∃ v, TensorCopy.writeByte o x y z = some v) ∧
        modelCausality L X l (.async copy (.write (.load x y z)))
          (.async (g, km) (.mmaRead isB (2 * m + z))) ∧
        ∀ w a bs, X.MemWrites w a bs → a.Covers l → w = .async copy (.write (.load x y z)) ∨
          modelCausality L X l w (.async copy (.write (.load x y z))) ∨
          modelCausality L X l (.async (g, km) (.mmaRead isB (2 * m + z))) w := by
  obtain ⟨s, jj, b, hgc, h2c, hwarp, hsp, hcnt, m0, hσ0, hs0⟩ := mma_at ht hX hi
  set c := g / L.block / 2 with hc
  set p := ((X.tr g).take km).countP (commitsTo ((slot L c s).empty 0)) with hp
  have hp0 : ((X.tr g).take km).countP (commitsTo (inputEmpty L (g / L.block) s.val)) = p := by
    have he : inputEmpty L (g / L.block) s.val = (slot L c s).empty 0 := by
      simp only [inputEmpty, slot, Fin.val_zero, Nat.add_zero]
      congr 1
      omega
    rw [he]
  set tile : Nat := if isB then 2 else b.val with htile
  have hti : tile < 3 := by rw [htile]; split_ifs <;> omega
  set x := 16 * jj.val + m % 16 with hxdef
  set y := m / 16 % 128 with hydef
  have hx : x < 64 := by omega
  have hy : y < 128 := Nat.mod_lt _ (by decide)
  set r := m / 16 / 128 with hrdef
  have hr : r < 2 := by omega
  have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
  have hRi : X.MmaIssue (g, km) dst sp acc mask := hi
  have hkm : km < (X.tr g).length := len_of_get hi.choose_spec
  -- The MMA thread's poll of production `p`, after which every copy of it has completed.
  rw [hgc] at hcnt hp
  obtain ⟨j, pc, pw, acq', sc, hj, hew, hcw⟩ :=
    MbarRing.Poll.exists_nth (X := X) (g := consumerOf L X c s b) (k := km)
      (m := (slot L c s).full 0) (n := p)
      (by omega)
  have hjp := PairTmaRing.okPolls_lt_of_get hew
  rw [hcw] at hjp
  obtain ⟨gw, kw, pcw, alw, spw, jd, d, hew', hmw, hrw, hIw, hd, hdi, -⟩ :=
    copy_exists hpre hX ht hjp ⟨r, hr⟩ tile hti
  replace hrw : gw / L.block % 2 = r := hrw
  obtain ⟨hgw, hcw', hprodw, -⟩ := issue_facts hX ht hew' hmw
  obtain ⟨dw, hσw⟩ := Frame.event_state ht.sound hX ht.tracked hew' (by simp)
  obtain ⟨lw, bw, jw, hdw, hlsite, hmw', ⟨base, cls, origin, hspw, -⟩, -, hcntw⟩ :=
    ht.tensor_issue hgw hew' hσw rfl
  have hsw : InputRing.slotOf bw = s := by
    have h := hmw'.symm.trans hmw
    rw [hcw', fullLoc_bar] at h
    exact (fullLoc_eq_iff (L := L)).mp (by rw [fullLoc_bar, fullLoc_bar]; exact h)
  have hcntw' : ((X.tr gw).take kw).countP (issuesTo ((slot L c s).full 0)) + 3 =
      3 * okPolls ((slot L c s).empty ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩)
        ((X.tr gw).take kw) + jw.val := by
    rw [empty_of_cta, hsw, hcw'] at hcntw
    simp only [Loader.fullOf, fullLoc_bar, hcw'] at hcntw
    exact hcntw
  have hjw : jw.val = tile := by omega
  have hctaw : gw / L.block = 2 * c + r := by omega
  rw [hsw, hjw, hctaw] at hspw
  obtain ⟨v0, o, addr0, b0, hobs, -⟩ := completed_writes hX hew' hd hdi hspw hx hy
    (show 0 < 2 by decide)
  obtain ⟨addr', pc'', hTI⟩ := (hX.tensor (gw, kw) o hobs).1
  refine ⟨(gw, kw), o, x, y, hobs, ⟨m0, s, jj, lw, bw, jw, pc'', addr', hσ0, hs0, hTI,
    by rw [← hdw]; exact hσw, hlsite, hsw, ?_, by simp only; omega, ?_, rfl, rfl⟩, fun z hz => ?_⟩
  · rw [hjw, htile]
    cases isB
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · rfl
  · simp only
    rw [hp0, show fullLoc L (g / L.block / 2) s = (slot L c s).full 0 from fullLoc_bar L c s, hIw,
      hjw]
  set l := stageByte (2 * c + r) (L.sharedBase + stageOff s.val tile) x y z with hl
  have hbl : sp.byteLoc (if isB then .b else .a) (2 * m + z) = some l := by
    have hkk : 2 * m + z = 32 * (128 * r + y) + 2 * (m % 16) + z := by omega
    rw [hsp, hkk, mma_byteLoc_cover L (g / L.block) (g % L.block / 32) s.val jj.val _ hsb hr hy
      (Nat.mod_lt _ (by decide)) hz]
    have hop : opTile (g % L.block / 32) (if isB then .b else .a) = tile := by
      rw [htile]
      cases isB
      · simp only [opTile, Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [opTile, ↓reduceIte]
    rw [hop, show g / L.block / 2 * 2 + r = 2 * c + r by omega]
  have hgt : g < L.threads := Frame.lt_of_get hX hi.choose_spec
  have hpa : PairAsync L l gw g :=
    pairAsync_of_pair hpre (by simp [hl, stageByte]) hgw hgt
      (.inl (by simp only [hl, stageByte]; omega)) (by omega)
  have hpa' : PairAsync L l g gw :=
    pairAsync_of_pair hpre (by simp [hl, stageByte]) hgt hgw
      (.inr (by simp only [hl, stageByte]; omega)) (by omega)
  have hfoot : X.MmaFootprint (g, km) isB (2 * m + z) l := .inl ⟨dst, sp, acc, mask, hRi, hbl⟩
  have hcR : AsyncCovers X (g, km) (.mmaRead isB (2 * m + z)) l :=
    ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, hfoot⟩, ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
  rw [hgc] at hcR hRi hkm
  obtain ⟨v, hwr⟩ := completed_writes hX hew' hd hdi hspw hx hy hz
  have hwr' : X.MemWrites (.async (gw, kw) (.write (.load x y z))) { loc := l, size := 1 } [v] :=
    hwr
  obtain ⟨o', -, v', hobs', -, hwl, hwb, -⟩ := id hwr'
  obtain rfl : o' = o := Option.some.inj (hobs'.symm.trans hobs)
  have hcW : AsyncCovers X (gw, kw) (.write (.load x y z)) l :=
    ⟨{ loc := l, size := 1 }, true, Execution.MemWrites.intent hwr',
      ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
  refine ⟨l, hbl, hwl, ⟨v', hwb⟩, ?_, ?_⟩
  · rw [hgc]
    exact ⟨.inr ⟨by rw [← hgc]; exact hpa, .inr (mma_pairTc hX ht hRi)⟩,
      .direct (copy_before_read hpre hX ht (b := b) hkm hew' hmw
      (by rw [hIw, show (3 * p + tile) / 3 = p by omega]; omega) hcW hcR)⟩
  · intro w a' bs' hw hcov
    have hint := Execution.MemWrites.intent hw
    have hin : IsInputStage L l := stageByte_input s.isLt hti hx hy hz
    rcases hacc w a' true l hint hcov hin with ⟨i', x', y', z', rfl⟩ | ⟨i', isB', idx', rfl⟩
    · -- Another tensor load of the byte.
      have hcb : AsyncCovers X i' (.write (.load x' y' z')) l := ⟨a', true, hint, hcov⟩
      obtain ⟨pc2, a2, sp2, s2, j2, he2, hm2, hx2, hy2, hz2, hl2, hc2⟩ := write_at ht hX hcb
      obtain ⟨hcta, hss, hjj, hxx, hyy, hzz⟩ := stageByte_inj s.isLt s2.isLt hti j2.isLt hx hx2
        hy hy2 hz hz2 (hl.symm.trans hl2)
      have hs2 : s2 = s := Fin.ext hss.symm
      subst s2
      subst hxx hyy hzz
      obtain ⟨g2, k2⟩ := i'
      simp only at he2 hm2 hl2 hc2 hcta
      rw [show g2 / L.block / 2 = c by omega] at hm2 hc2
      -- one loader
      obtain ⟨-, -, hp2, hb2⟩ := issue_facts hX ht he2 hm2
      obtain ⟨-, -, -, hbw⟩ := issue_facts hX ht hew' hmw
      obtain ⟨jw1, pw1, qw1, aw1, sw1, -, hw1⟩ := exists_okPoll (X := X) (g := gw) (k := kw)
        (m := (slot L c s).empty ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩) (by omega)
      obtain ⟨jw2, pw2, qw2, aw2, sw2, -, hw2⟩ := exists_okPoll (X := X) (g := g2) (k := k2)
        (m := (slot L c s).empty ⟨g2 / L.block % 2, Nat.mod_lt _ (by decide)⟩) (by omega)
      have hpw : producerThread L c ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩ gw = true := by
        exact hprodw
      have hp2' : producerThread L c ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩ g2 = true := by
        have hfe : (⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
            ⟨g2 / L.block % 2, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by simp only; omega)
        rw [hfe]; exact hp2
      rw [show (⟨g2 / L.block % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
        ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩ from Fin.ext (by simp only; omega)] at hw2 hc2
      have hg2 := (producerOf_eq hX ht hpw hw1).trans (producerOf_eq hX ht hp2' hw2).symm
      subst hg2
      rcases Nat.lt_trichotomy
        (okPolls ((slot L c s).empty ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩)
          ((X.tr gw).take k2))
        (okPolls ((slot L c s).empty ⟨gw / L.block % 2, Nat.mod_lt _ (by decide)⟩)
          ((X.tr gw).take kw)) with hlt | heq | hgt
      · refine .inr (.inl ⟨.inl ⟨Frame.lt_of_get hX hew', Frame.lt_of_get hX hew', rfl⟩, ?_⟩)
        exact copies_chain hpre hX ht (s := s) (j := j2) he2 (by rw [hcw']; exact hm2) hew'
          (by rw [hcw']; exact hlt) (by rw [hcw']; exact hc2) hx hy hz
          hl2 hcb hcW
      · obtain ⟨-, rfl⟩ := issue_inj hX ht he2 hm2 hew' hmw rfl (by omega)
        exact .inl rfl
      · refine .inr (.inr ?_)
        have hsucc := commits_mma_succ (m := (slot L c s).empty 0) (hRi.choose_spec)
        rw [hgc]
        exact ⟨.inr ⟨by rw [← hgc]; exact hpa', .inl (mma_pairTc hX ht hRi)⟩,
          .direct (read_before_copy hpre hX ht (b := b) (Or.inl ⟨dst, sp, acc, mask, hRi⟩)
          he2 hm2 (by rw [hsucc]; omega) hcR hcb).1⟩
    · exact absurd hint.1 (by simp [AsyncCopy.Part.writes])

/-- **The source of an operand byte**: its write by the copy of its element (`pair_copy`). -/
theorem byte_source (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hacc : InputAccessors L X) {g km dst : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, km) dst sp acc mask) (isB : Bool)
    (k : Fin 8192) :
    ∃ src : MmaSources.ByteSource X, X.MmaFootprint (g, km) isB k.val src.loc ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers src.loc →
        w = src.ref ∨ modelCausality L X src.loc w src.ref ∨
          modelCausality L X src.loc (.async (g, km) (.mmaRead isB k.val)) w := by
  have hk := k.isLt
  obtain ⟨copy, o, x, y, hobs, -, hz⟩ := pair_copy hpre hX ht hacc hi isB (m := k.val / 2)
    (by omega)
  have hkk : 2 * (k.val / 2) + k.val % 2 = k.val := by omega
  obtain ⟨l, hbl, hwl, ⟨v, hwb⟩, -, hord⟩ := hz (k.val % 2) (Nat.mod_lt _ (by decide))
  rw [hkk] at hbl hord
  obtain ⟨addr, hTI⟩ := (hX.tensor copy o hobs).1
  have hwr : X.MemWrites (.async copy (.write (.load x y (k.val % 2)))) { loc := l, size := 1 }
    [v] :=
    ⟨o, addr, v, hobs, hTI, hwl, hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨⟨l, _, _, _, hwr, ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩,
    .inl ⟨_, _, _, _, hi, hbl⟩, hord⟩

/-- **The MMAs' operand sources.** Each warp issues its MMAs from one thread, and each MMA reads
8192-byte operands of the input ring's stages, each byte from the write of its production's copy,
which every other write of the byte precedes or follows the read. -/
theorem operandSources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hacc : InputAccessors L X) : OperandSources L X 8192 8192 := by
  refine ⟨fun {i j} ⟨d, sp, acc, mask, hi⟩ ⟨d', sp', acc', mask', hj⟩ hw => ?_, ?_⟩
  · obtain ⟨g, k⟩ := i
    obtain ⟨h, k'⟩ := j
    obtain ⟨s, -, b, -, h2c, hwg, -, hcnt, -⟩ := mma_at ht hX hi
    obtain ⟨s', -, b', -, -, -, -, hcnt', -⟩ := mma_at ht hX hj
    obtain ⟨j1, pc1, q1, a1, s1, -, he1⟩ := exists_okPoll (X := X) (g := g) (k := k)
      (m := (slot L (g / L.block / 2) s).full 0) (by omega)
    obtain ⟨j2, pc2, q2, a2, s2, -, he2⟩ := exists_okPoll (X := X) (g := h) (k := k')
      (m := (slot L (h / L.block / 2) s').full 0) (by omega)
    obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hw
    exact mma_unique hX ht hcta hwarp (by dsimp only; omega) he1 he2 rfl rfl
  · intro i d sp acc mask hi
    obtain ⟨g, k⟩ := i
    obtain ⟨s, jj, b, -, -, -, hsp, -, -⟩ := mma_at ht hX hi
    subst hsp
    refine ⟨mmaDescriptor_valid, (by decide : TcMma.Operand.a.bytes mmaDescriptor = 8192),
      (by decide : TcMma.Operand.b.bytes mmaDescriptor = 8192), rfl, fun isB idx loc hf => ?_,
      fun isB idx => by cases isB <;> exact byte_source hpre hX ht hacc hi _ idx⟩
    rcases hf with ⟨d', sp', acc', mask', hi', hbl⟩ | ⟨a, src, cta, ⟨pc, hc⟩, -⟩
    · obtain ⟨pc, he⟩ := hi
      obtain ⟨pc', he'⟩ := hi'
      rw [he] at he'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
      obtain ⟨-, -, rfl, -, -⟩ := he'
      have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
      have := (mma_byteLoc L (g / L.block) (g % L.block / 32) s.val jj.val _ hsb hbl).1
      split <;> omega
    · obtain ⟨pc', he⟩ := hi
      rw [he] at hc
      simp at hc

/-- **The MMAs' operand copies.** -/
theorem operandCopies (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hacc : InputAccessors L X) : OperandCopies L X :=
  fun ⟨_, _⟩ _ _ _ _ hi isB _ hm =>
    let ⟨copy, o, x, y, hobs, _, hz⟩ := pair_copy hpre hX ht hacc hi isB hm
    ⟨copy, o, x, y, hobs, hz⟩

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
