-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Pairs
public import Lemmas.Protocol.PairTmaRing.Ordered
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Layout

@[expose] public section

/-! # The input ring's order

Two conflicting accesses of an input stage byte are a tensor load writing it and an MMA reading
it, or two tensor loads (`InputAccessors`). A tensor load writes byte `(x, y, z)` of tile `j` of
slot `s` of its loader's CTA (`write_at`); an MMA reads the stage bytes of its slot's tiles of its
warp in both CTAs of its cluster (`read_at`); a byte is one element of one tile
(`stageByte_inj`). Numbering a load by its production `n` (its loader's earlier loads of the slot
over three) and a read by its MMA thread's commits to the slot `p` before it: the load precedes
the read when `n ≤ p` (`copy_before_read`) and follows it when `p < n` (`read_before_copy`). Two
loads of one byte are of one loader, of distinct productions; the earlier one precedes an MMA
read of the byte of its production, which precedes the later one (`copies_chain`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A one-byte access covers only its byte. -/
theorem covers_one {a : Acc} {l : Loc} (hs : a.size = 1) (h : a.Covers l) : l = a.loc := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hs] at h4
  have h5 : l.addr = a.loc.addr := by omega
  obtain ⟨sp, ct, ad⟩ := l
  simp only at h1 h2 h5
  rw [h1, h2, h5]

/-- A slot's empty barrier of the CTA of a loader thread. -/
theorem empty_of_cta (L : Launch) (g : Nat) (s : Fin 4) :
    Loader.emptyOf L g s =
      (slot L (g / L.block / 2) s).empty ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ := by
  simp only [Loader.emptyOf, InputRing.emptyLoc, slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and]
  omega

/-- **A tensor write.** A tensor write covering a byte is a loader's copy into tile `j` of slot
`s` of its CTA, completing on the slot's full barrier, after three of its loads of the slot per
earlier successful poll of the slot's empty barrier, less the batch's loads still to issue; the
byte is the write's element of the tile. -/
theorem write_at (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) {i : EvId}
    {x y z : Nat} {l : Loc} (h : AsyncCovers X i (.write (.load x y z)) l) :
    ∃ (pc a : Nat) (sp : TensorCopy.Spec) (s : Fin 4) (j : Fin 3),
      X.get i = some ⟨pc, .tensorIssue a sp⟩ ∧
      sp.mbar = (slot L (i.1 / L.block / 2) s).full 0 ∧ x < 64 ∧ y < 128 ∧ z < 2 ∧
      l = stageByte (i.1 / L.block) (L.sharedBase + stageOff s.val j.val) x y z ∧
      ((X.tr i.1).take i.2).countP (issuesTo ((slot L (i.1 / L.block / 2) s).full 0)) + 3 =
        3 * okPolls
          ((slot L (i.1 / L.block / 2) s).empty ⟨i.1 / L.block % 2, Nat.mod_lt _ (by decide)⟩)
          ((X.tr i.1).take i.2) + j.val := by
  obtain ⟨g, k⟩ := i
  obtain ⟨acc, w, ⟨-, sp, addr, ⟨pc, hget⟩, hwl, hsz⟩, hcov⟩ := h
  have hg := Frame.lt_of_get hX hget
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
  obtain ⟨ld, b, j, -, -, hm, ⟨base, cls, origin, hsp, -⟩, -, hcnt⟩ :=
    ht.tensor_issue hg hget hσ rfl
  rw [hsp] at hwl
  obtain ⟨hx, hy, hz, hloc⟩ := copy_writeLoc hwl
  refine ⟨pc, addr, sp, slotOf b, j, hget, ?_, hx, hy, hz, ?_, ?_⟩
  · rw [hm, fullLoc_bar]; rfl
  · rw [covers_one hsz hcov, hloc]
  · rw [empty_of_cta] at hcnt
    simp only [Loader.fullOf, fullLoc_bar] at hcnt
    exact hcnt

/-- **An MMA read.** An MMA read covering a byte is an MMA of the MMA thread of selector `b` of
its cluster's leader CTA, at slot `s`, K step `jj`, reading its warp's A tile (`isB` false) or the
B tile of the slot, in the CTA of the pair its row names; the thread has polled the slot's full
barrier once more than it committed to the slot. -/
theorem read_at (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X)
    {i : EvId} {isB : Bool} {idx : Nat} {l : Loc} (h : AsyncCovers X i (.mmaRead isB idx) l) :
    ∃ (dst : Nat) (sp : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (s jj : Fin 4)
      (b : Fin 2), X.MmaIssue i dst sp acc mask ∧
      i.1 = consumerOf L X (i.1 / L.block / 2) s b ∧ 2 * (i.1 / L.block / 2) = i.1 / L.block ∧
      sp.byteLoc (if isB then .b else .a) idx = some l ∧ idx / 32 < 256 ∧
      l = stageByte (i.1 / L.block + idx / 32 / 128)
        (L.sharedBase + stageOff s.val (if isB then 2 else b.val)) (16 * jj.val + idx / 2 % 16)
        (idx / 32 % 128) (idx % 2) ∧
      ((X.tr i.1).take i.2).countP (commitsTo ((slot L (i.1 / L.block / 2) s).empty 0)) + 1 =
        okPolls ((slot L (i.1 / L.block / 2) s).full 0) ((X.tr i.1).take i.2) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨acc, w, ⟨-, hsz, hfp⟩, hcov⟩ := h
  rcases hfp with ⟨dst, sp, a, mask, ⟨pc, hget⟩, hbl⟩ | ⟨a, src, cta, ⟨pc, hget⟩, -⟩
  · have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    obtain ⟨m, s, jj, rfl, -, hlead, hsp, hcnt⟩ := ht.mma_issue hg hget hσ rfl
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
    have hgc := consumerOf_eq hX ht hcons he'
    have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
    have hl := covers_one hsz hcov
    subst hl
    have hbl' := hbl
    rw [hsp] at hbl'
    obtain ⟨hrow, hloc⟩ := mma_byteLoc L (g / L.block) (g % L.block / 32) s.val jj.val _ hsb hbl'
    refine ⟨dst, sp, a, mask, s, jj, ⟨g % L.block / 32 - 8, hb⟩, ⟨pc, hget⟩, hgc,
      by show 2 * (g / L.block / 2) = g / L.block; omega, hbl, hrow, ?_, hcnt⟩
    rw [hloc]
    have h2 : g / L.block / 2 * 2 = g / L.block := by omega
    have hop : opTile (g % L.block / 32) (if isB then .b else .a) =
        (if isB then 2 else g % L.block / 32 - 8) := by
      cases isB
      · simp only [opTile, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [opTile, ↓reduceIte]
    rw [h2, hop]
  · have hg := Frame.lt_of_get hX hget
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget (by simp)
    exact absurd rfl (ht.no_tc_cp hg hget hσ)

/-- A commit's step counts no MMA: the commits to a slot up to an MMA and up to its next event are
the same. -/
theorem commits_mma_succ {g k pc dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {m : Loc} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    ((X.tr g).take (k + 1)).countP (commitsTo m) = ((X.tr g).take k).countP (commitsTo m) := by
  rw [List.take_add_one, show (X.tr g)[k]? = _ from he]
  simp [commitsTo]

/-- **Two loads of one byte.** A tensor load of a byte of tile `j` of slot `s`, by a loader with
`Q` successful empty polls before it, precedes a load of the byte by the same loader with more:
an MMA read of the byte, of the earlier load's production, lies between them, and has read. -/
theorem copies_chain (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {s : Fin 4} {j : Fin 3} {gl kl kl' pc pc' al al' : Nat}
    {sp sp' : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pc, .tensorIssue al sp⟩)
    (hml : sp.mbar = (slot L (gl / L.block / 2) s).full 0)
    (hel' : X.get (gl, kl') = some ⟨pc', .tensorIssue al' sp'⟩)
    (hlt : okPolls ((slot L (gl / L.block / 2) s).empty ⟨gl / L.block % 2,
      Nat.mod_lt _ (by decide)⟩)
        ((X.tr gl).take kl) <
      okPolls ((slot L (gl / L.block / 2) s).empty ⟨gl / L.block % 2, Nat.mod_lt _ (by decide)⟩)
        ((X.tr gl).take kl'))
    (hcnt : ((X.tr gl).take kl).countP (issuesTo ((slot L (gl / L.block / 2) s).full 0)) + 3 =
      3 * okPolls ((slot L (gl / L.block / 2) s).empty ⟨gl / L.block % 2, Nat.mod_lt _ (by decide)⟩)
        ((X.tr gl).take kl) + j.val)
    {x y z : Nat} (hx : x < 64) (hy : y < 128) (hz : z < 2) {l : Loc}
    (hl : l = stageByte (gl / L.block) (L.sharedBase + stageOff s.val j.val) x y z)
    {x' y' z' : Nat} (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (gl, kl') (.write (.load x' y' z')) l) :
    AsyncChain L X l ((gl, kl), .write (.load x y z)) ((gl, kl'), .write (.load x' y' z')) := by
  set c := gl / L.block / 2 with hc
  set a : Fin 2 := ⟨gl / L.block % 2, Nat.mod_lt _ (by decide)⟩ with ha
  obtain ⟨-, -, hprod, -⟩ := issue_facts hX ht hel hml
  rw [← ha] at hprod
  obtain ⟨j0, pc0, p0, acq0, sc0, -, he0⟩ := exists_okPoll (X := X) (g := gl) (k := kl)
    (m := (slot L c s).empty a) (by omega)
  have hg := producerOf_eq hX ht hprod he0
  -- The MMA thread reading the byte's tile, and the operand.
  set bv : Nat := if j.val = 2 then 0 else j.val with hbv
  have hbv2 : bv < 2 := by rw [hbv]; split_ifs <;> omega
  set b : Fin 2 := ⟨bv, hbv2⟩ with hb
  set isB : Bool := decide (j.val = 2) with hisB
  set gm := consumerOf L X c s b with hgm
  -- The MMA thread's commit of the earlier load's production follows its read of the byte.
  have hread : ∀ jc pcc spc, X.get (gm, jc) = some ⟨pcc, .tc (.commit spc)⟩ →
      spc.mbar = (slot L c s).empty 0 →
      ((X.tr gm).take jc).countP (commitsTo ((slot L c s).empty 0)) =
        ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 →
      ∃ kR isB' idx, X.TcAsync (gm, kR) ∧
        ((X.tr gm).take kR).countP (commitsTo ((slot L c s).empty 0)) =
          ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 ∧
        ((X.tr gm).take kR).countP (commitsTo ((slot L c s).empty 0)) + 1 ≤
          okPolls ((slot L c s).full 0) ((X.tr gm).take kR) ∧
        AsyncCovers X (gm, kR) (.mmaRead isB' idx) l ∧
        ∀ w ws, AsyncObserved X (gm, kR) .mmaDone w true ws →
          X.AsyncPresent (gm, kR) (.mmaRead isB' idx) := by
    intro jc pcc spc hec hmc hcjc
    have hgmc : consumerThread L c b gm = true := consumerOf_thread hpre c s b
    simp only [consumerThread, decide_eq_true_eq] at hgmc
    have hgmt := Frame.lt_of_get hX hec
    obtain ⟨dm, hσm⟩ := Frame.event_state ht.sound hX ht.tracked hec (by simp)
    have hmc' : spc.mbar = inputEmpty L (gm / L.block) s.val := by
      rw [hmc, hgmc.1]; rfl
    have htg := ht.commit_ranks s 0 hgmt hec hσm rfl hmc' (by decide)
    obtain ⟨hby, -⟩ := (ht.ring_event hgmt hec hσm).commit spc 0 ⟨.input, s.val, false⟩
      (gm / L.block + 0) rfl htg s.isLt
    obtain ⟨mm, rfl⟩ := hby
    have hmc'' : spc.mbar = ⟨.shared, gm / L.block, L.sharedBase + 40 + 8 * s.val⟩ := by
      rw [hmc]
      simp only [slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and, Fin.val_zero, hgmc.1]
      omega
    obtain ⟨h4, hbatch⟩ := ht.mma_batch hgmt hec hσm rfl hmc''
    set t : Fin 4 := ⟨x / 16, by omega⟩ with ht'
    obtain ⟨pr, dst, acc, mask, her, hcr, hcntR⟩ := hbatch t
    set kR := jc - 4 + t.val with hkR
    have hRi : X.MmaIssue (gm, kR) dst
        (mmaSpec L (gm / L.block) (gm % L.block / 32) s.val t.val) acc mask := ⟨pr, her⟩
    -- The MMA reads the byte.
    set idx := 32 * (128 * (gl / L.block % 2) + y) + 2 * (x % 16) + z with hidx
    have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
    have hbl : (mmaSpec L (gm / L.block) (gm % L.block / 32) s.val t.val).byteLoc
        (if isB then .b else .a) idx = some l := by
      rw [hidx, mma_byteLoc_cover L (gm / L.block) (gm % L.block / 32) s.val t.val _ hsb
        (Nat.mod_lt _ (by decide)) hy (Nat.mod_lt _ (by decide)) hz, hl]
      congr 1
      simp only [stageByte, Loc.mk.injEq, true_and]
      have hx16 : 16 * t.val + x % 16 = x := by simp only [ht']; omega
      have htile : opTile (gm % L.block / 32) (if isB then .b else .a) = j.val := by
        simp only [hisB, opTile]
        by_cases hj : j.val = 2
        · simp [hj]
        · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hw8 : gm % L.block / 32 = 8 + bv := hgmc.2
          have hbvj : bv = j.val := by rw [hbv]; simp [hj]
          omega
      rw [hx16, htile]
      refine ⟨by omega, rfl⟩
    have hcbR : AsyncCovers X (gm, kR) (.mmaRead isB idx) l :=
      ⟨{ loc := l, size := 1 }, false, ⟨rfl, rfl, Or.inl ⟨dst, _, acc, mask, hRi, hbl⟩⟩,
        ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
    -- The read's counts.
    have hfull : (⟨.shared, gm / L.block, L.sharedBase + 8 + 8 * s.val⟩ : Loc) =
        (slot L c s).full 0 := by
      simp only [slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and, hgmc.1]
      omega
    have hloc : (⟨.shared, gm / L.block, L.sharedBase + 40 + 8 * s.val⟩ : Loc) =
        (slot L c s).empty 0 := by
      simp only [slot, Bar.loc, Bar.off, Loc.mk.injEq, true_and, Fin.val_zero, hgmc.1]
      omega
    have hcr' : ((X.tr gm).take kR).countP (commitsTo ((slot L c s).empty 0)) =
        ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 := by
      rw [← hcjc, ← hloc]
      exact hcr
    have hcntR' : ((X.tr gm).take kR).countP (commitsTo ((slot L c s).empty 0)) + 1 =
        okPolls ((slot L c s).full 0) ((X.tr gm).take kR) := by
      rw [← hloc, ← hfull]
      exact hcntR
    refine ⟨kR, isB, idx, Or.inl ⟨dst, _, acc, mask, hRi⟩, hcr', hcntR'.le, hcbR,
      fun w ws hom => PairTmaRing.mmaRead_present hX hom hRi hbl ?_⟩
    have hm2 : gl / L.block % 2 < 2 := Nat.mod_lt _ (by decide)
    have hm16 : x % 16 < 16 := Nat.mod_lt _ (by decide)
    cases isB <;> simp only [mmaSpec, mmaDescriptor, TcMma.Operand.bytes, TcMma.Operand.rows,
      TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width, Bool.false_eq_true, ↓reduceIte] <;>
      simp <;> omega
  have huse : ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 + 1 =
      okPolls ((slot L c s).empty a) ((X.tr gl).take kl) := by omega
  rw [hg] at hel hel' hlt huse hca hcb hread ⊢
  exact PairTmaRing.copies_chain hX (hyp hpre hX ht c s) hel hml hel' hlt huse hca hcb b hread

/-- Every MMA of the kernel is a `cta_group::2` MMA (EXT-PAIR-ASYNC). -/
theorem mma_pairTc (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i dst sp acc mask) : PairTc X i := by
  obtain ⟨pc, he⟩ := id hi
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨_, _, _, -, -, -, hs, -⟩ := ht.mma_issue (Frame.lt_of_get hX he) he hσ rfl
  exact .inl ⟨dst, sp, acc, mask, hi, by rw [hs]; rfl⟩

/-- **A tensor write and an MMA read of one byte** are ordered, one way or the other. -/
theorem write_read (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i i' : EvId} {x y z : Nat} {isB : Bool} {idx : Nat} {l : Loc}
    (hca : AsyncCovers X i (.write (.load x y z)) l) (hcb : AsyncCovers X i' (.mmaRead isB idx) l) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async i' (.mmaRead isB idx)) ∨
      modelCausality L X l (.async i' (.mmaRead isB idx)) (.async i (.write (.load x y z))) := by
  obtain ⟨gl, kl⟩ := i
  obtain ⟨gm, km⟩ := i'
  obtain ⟨pc, al, sp, s, j, hel, hml, hx, hy, hz, hl, hcnt⟩ := write_at ht hX hca
  obtain ⟨dst, msp, acc, mask, s', jj, b, hRi, hgm, h2c, -, hrow, hl', hcntR⟩ :=
    read_at hpre ht hX hcb
  simp only at hel hml hl hcnt hgm h2c hl' hcntR hRi
  obtain ⟨hcta, hss, -, -, -, -⟩ := stageByte_inj s.isLt s'.isLt j.isLt
    (show (if isB then 2 else b.val) < 3 by split_ifs <;> omega) hx (by omega) hy
    (Nat.mod_lt _ (by decide)) hz (Nat.mod_lt _ (by decide)) (hl.symm.trans hl')
  have hs : s = s' := Fin.ext hss
  subst hs
  generalize hc : gm / L.block / 2 = c at hgm h2c hl' hcntR
  have hcl : gl / L.block / 2 = c := by omega
  rw [hcl] at hml hcnt
  subst hgm
  have hj := j.isLt
  have hgm : consumerOf L X c s b < L.threads := by
    obtain ⟨pr, her⟩ := hRi
    exact Frame.lt_of_get hX her
  have hpa : PairAsync L l gl (consumerOf L X c s b) :=
    pairAsync_of_pair hpre (by rw [hl]; rfl) (Frame.lt_of_get hX hel) hgm (.inl (by rw [hl]; rfl))
      (by omega)
  have hpa' : PairAsync L l (consumerOf L X c s b) gl :=
    pairAsync_of_pair hpre (by rw [hl]; rfl) hgm (Frame.lt_of_get hX hel) (.inr (by rw [hl]; rfl))
      (by omega)
  have hpt := mma_pairTc hX ht hRi
  obtain ⟨pr, her⟩ := hRi
  rcases PairTmaRing.copy_read_order hX (hyp hpre hX ht c s) (b := b)
    (Or.inl ⟨dst, msp, acc, mask, pr, her⟩) hcntR.le hel hml hca hcb with h | h
  · exact .inl (modelCausality_pair_direct hpa (.inr hpt) h)
  · exact .inr (modelCausality_pair_direct hpa' (.inl hpt) h)

/-- **Two tensor writes of one byte** are one loader's, of distinct productions, and ordered. -/
theorem write_write (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i i' : EvId} {x y z x' y' z' : Nat} {l : Loc}
    (hne : AsyncCopy.Ref.async i (.write (.load x y z)) ≠ .async i' (.write (.load x' y' z')))
    (hca : AsyncCovers X i (.write (.load x y z)) l)
    (hcb : AsyncCovers X i' (.write (.load x' y' z')) l) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async i' (.write (.load x' y' z'))) ∨
      modelCausality L X l (.async i' (.write (.load x' y' z')))
          (.async i (.write (.load x y z))) := by
  obtain ⟨g1, k1⟩ := i
  obtain ⟨g2, k2⟩ := i'
  obtain ⟨pc1, a1, sp1, s1, j1, he1, hm1, hx1, hy1, hz1, hl1, hc1⟩ := write_at ht hX hca
  obtain ⟨pc2, a2, sp2, s2, j2, he2, hm2, hx2, hy2, hz2, hl2, hc2⟩ := write_at ht hX hcb
  simp only at he1 hm1 hl1 hc1 he2 hm2 hl2 hc2
  obtain ⟨hcta, hss, hjj, hxx, hyy, hzz⟩ := stageByte_inj s1.isLt s2.isLt j1.isLt j2.isLt hx1 hx2
    hy1 hy2 hz1 hz2 (hl1.symm.trans hl2)
  have hs : s1 = s2 := Fin.ext hss
  have hj : j1 = j2 := Fin.ext hjj
  subst hs hj hxx hyy hzz
  -- One loader.
  obtain ⟨-, -, hp1, hb1⟩ := issue_facts hX ht he1 hm1
  obtain ⟨-, -, hp2, hb2⟩ := issue_facts hX ht he2 hm2
  rw [← hcta] at hp2 hb2 hm2 hc2
  obtain ⟨jw1, q1, r1, u1, v1, -, hw1⟩ := exists_okPoll (X := X) (g := g1) (k := k1)
    (m := (slot L (g1 / L.block / 2) s1).empty ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩)
    (by omega)
  obtain ⟨jw2, q2, r2, u2, v2, -, hw2⟩ := exists_okPoll (X := X) (g := g2) (k := k2)
    (m := (slot L (g1 / L.block / 2) s1).empty ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩)
    (by omega)
  have hg := (producerOf_eq hX ht hp1 hw1).trans (producerOf_eq hX ht hp2 hw2).symm
  subst hg
  rcases Nat.lt_trichotomy
    (okPolls ((slot L (g1 / L.block / 2) s1).empty ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩)
      ((X.tr g1).take k1))
    (okPolls ((slot L (g1 / L.block / 2) s1).empty ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩)
      ((X.tr g1).take k2)) with hlt | heq | hgt
  · exact .inl ⟨.inl ⟨Frame.lt_of_get hX he1, Frame.lt_of_get hX he1, rfl⟩,
      copies_chain hpre hX ht he1 hm1 he2 hlt hc1 hx1 hy1 hz1 hl1 hca hcb⟩
  · obtain ⟨-, rfl⟩ := issue_inj hX ht he1 hm1 he2 hm2 rfl (by omega)
    exact absurd rfl hne
  · exact .inr ⟨.inl ⟨Frame.lt_of_get hX he1, Frame.lt_of_get hX he1, rfl⟩,
      copies_chain hpre hX ht he2 hm2 he1 hgt hc2 hx1 hy1 hz1 hl1 hcb hca⟩

/-- **The input ring is ordered.** Two conflicting accesses of an input stage byte, all of whose
accesses are tensor loads and MMA reads, are ordered at the byte, one way or the other. -/
theorem inputOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hacc : InputAccessors L X) : InputOrdered L X := by
  intro e f a b l hconf hal hbl hin
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := hconf
  rcases hacc e a we l hie hal hin with ⟨i, x, y, z, rfl⟩ | ⟨i, isB, idx, rfl⟩ <;>
    rcases hacc f b wf l hif hbl hin with ⟨i', x', y', z', rfl⟩ | ⟨i', isB', idx', rfl⟩
  · exact write_write hpre hX ht hne ⟨a, we, hie, hal⟩ ⟨b, wf, hif, hbl⟩
  · exact write_read hpre hX ht ⟨a, we, hie, hal⟩ ⟨b, wf, hif, hbl⟩
  · exact (write_read hpre hX ht ⟨b, wf, hif, hbl⟩ ⟨a, we, hie, hal⟩).symm
  · have h1 : we = false := hie.1
    have h2 : wf = false := hif.1
    subst h1 h2
    simp at hw

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
