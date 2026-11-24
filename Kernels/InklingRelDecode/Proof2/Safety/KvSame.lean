-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.ProShfl
public import Lemmas.Flow.SameCount

@[expose] public section

/-! # The kv region on the role table

A byte of the K and V rings above the base word (`InKv`) has no thread access (`thread_notKv`);
its asynchronous accesses are the tensor copies' writes and the MMAs' B operand reads. A copy and
a read are ordered by `copy_read_ordered`, two copies of different uses of the slot by
`copies_diff_ordered`. This file adds the last case and assembles the region:

* **Boxes.** A copy on `kv_ready s` writes one of the slot's eight 8192-byte boxes, numbered
  `4 slab + 2 isV + hh` (`boxLo`). The loader's copy at a copy site writes the box `cpDoneS` of
  the site; the prologue's copy `j` of block `b` the box `4 (j / 2) + 2 (j % 2) + warp % 2`
  (`pro_half`: the half is the warp's).
* **Counts.** The loader's lane leads its elections (`ld_cp_elected`), so its copies to
  `kv_ready s` before a copy site are exactly `8 slotCnt + cpDoneS` (`LdCnt.CE`); a prologue copy
  site fires once (`pro_copy_once`).
* `copy_same_use`: two copies' writes of one byte in one use of the slot are one write of one
  element: two loader copies have one count (`same_count`), two prologue copies one site and one
  warp, and a prologue copy (use 0) is never in the use of a loader copy (at least 1).
* `kv_ordered : ConflictsOrdered L X (InKv L)`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The slot's boxes -/

/-- The first byte of box `B = 4 slab + 2 isV + hh` of slot `s`. -/
def boxLo (L : Launch) (s B : Nat) : Nat :=
  L.sharedBase + 32768 * s + 98304 * (B / 2 % 2) + 8192 * (B / 4) + 16384 * (B % 2)

theorem boxLo_inj {s B B' a : Nat} (hB : B < 8) (hB' : B' < 8) (h1 : boxLo L s B ≤ a)
    (h2 : a < boxLo L s B + 8192) (h1' : boxLo L s B' ≤ a) (h2' : a < boxLo L s B' + 8192) :
    B = B' := by
  unfold boxLo at *
  interval_cases B <;> interval_cases B' <;> omega

theorem boxLo_slot {s B a : Nat} (hB : B < 8) (h1 : boxLo L s B ≤ a)
    (h2 : a < boxLo L s B + 8192) : InSlot L s a := by
  unfold boxLo at *
  unfold InSlot
  interval_cases B <;> simp at h1 h2 <;> omega

theorem ldBox_cp {s : Proof.Loader.Site} {v : Bool} {sl hh : Nat}
    (h : Proof.EvW.ldBox s = some (v, sl, hh)) :
    cpDoneS s = 4 * sl + 2 * (if v then 1 else 0) + hh ∧ sl ≤ 1 ∧ hh ≤ 1 := by
  cases s <;> simp [Proof.EvW.ldBox] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [cpDoneS]

/-! ### A copy's box and count -/

/-- **A copy**: its spec is a KV copy's; it is the loader's at a copy site, with its exact count
of earlier copies to the slot's `kv_ready` and its box, or the prologue's copy `j` of block `b`
by a lane of warp 0 or 1, with its box. -/
theorem copy_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc a : Nat} {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    (∃ cta col row dst bar, sp = Proof.EvW.kvCopySpec Q cta col row dst bar) ∧
    ((∃ (w : Value) (d : Proof.Loader.D) (P : Proof.Loader.Pro) (n : Cls → Nat),
        Frame.stateAt (thread Q L) X g k =
          some (some (.inr ⟨.inl (.worker w), .loader d P⟩, n)) ∧
        g % L.block / 32 = 6 ∧ cpDoneS d.site < 8 ∧
        ((X.tr g).take k).countP (issuesTo (Proof.EvW.kvReady L (g / L.block) (d.i % 3))) =
          8 * slotCnt (npOf Q L g) d.i (d.i % 3) + cpDoneS d.site ∧
        ∀ x y z l, TensorCopy.writeLoc sp x y z = some l →
          boxLo L (d.i % 3) (cpDoneS d.site) ≤ l.addr ∧
            l.addr < boxLo L (d.i % 3) (cpDoneS d.site) + 8192) ∨
      (∃ (tm : Nat) (bw : Value) (d : ProA.D) (n : Cls → Nat) (b : Fin 3) (j : Fin 4),
        Frame.stateAt (thread Q L) X g k =
          some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)) ∧
        d.site = .ptc b j ∧ g % L.block / 32 < 2 ∧
        ∀ x y z l, TensorCopy.writeLoc sp x y z = some l →
          boxLo L b (4 * (j.val / 2) + 2 * (j.val % 2) + g % L.block / 32 % 2) ≤ l.addr ∧
            l.addr < boxLo L b (4 * (j.val / 2) + 2 * (j.val % 2) + g % L.block / 32 % 2) +
              8192)) := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hop : tensorOp ins.op = true := by
      cases hq : tensorOp ins.op
      · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a sp)
      · rfl
    have hpc := OpPcsFast.mem kernel_copy_pcs hc hop
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_copy st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · obtain ⟨b, j, hs⟩ := proA_copy d.site hpc
          have hx' : d.site ≠ .exit := by rw [hs]; simp
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx' hat hi.1 hc hf
          obtain ⟨-, -, hP, -⟩ := (hJ : ProRef Q L g tm bw d n)
          have hmap : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0 := by
            rw [hP.pro]; rfl
          have hi12 : 4 * b.val + j.val < 12 := by omega
          have he' := Proof.ProA.ptc_event_map hp (i := 4 * b.val + j.val) hi12 hmap hF
            (by simp only [ProA.D.old, hs, ptc_old])
          simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at he'
          obtain ⟨-, -, rfl⟩ := he'
          obtain ⟨-, -, h64, -⟩ := pro_ptc_info hp hX he hσ hs
          have hh := pro_half hp hX hg hlen hσ hs
          refine ⟨⟨_, _, _, _, _, rfl⟩, .inr ⟨tm, bw, d, n, b, j, hσ, hs, by omega,
            fun x y z l hl => ?_⟩⟩
          obtain ⟨-, -, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q _ _ _ _ _ hl
          have hsb : Proof.ProA.SbRoom L := by
            have := hp.sharedRange; unfold sharedBytes at this; unfold Proof.ProA.SbRoom; omega
          rw [show (ProA.D.old d).dt = d.dt from rfl, Proof.ProA.copyDst_form L g d.dt hsb hi12,
            show (4 * b.val + j.val) / 4 = b.val by omega, hh] at h3 h4
          have hj4 := j.isLt
          have hw2 : g % L.block / 32 % 2 < 2 := Nat.mod_lt _ (by omega)
          have e1 : (4 * b.val + j.val) % 2 = j.val % 2 := by omega
          have e2 : (4 * b.val + j.val) % 4 / 2 = j.val / 2 := by omega
          have e3 : (4 * (j.val / 2) + 2 * (j.val % 2) + g % L.block / 32 % 2) / 2 % 2 =
              j.val % 2 := by omega
          have e4 : (4 * (j.val / 2) + 2 * (j.val % 2) + g % L.block / 32 % 2) / 4 =
              j.val / 2 := by omega
          have e5 : (4 * (j.val / 2) + 2 * (j.val % 2) + g % L.block / 32 % 2) % 2 =
              g % L.block / 32 % 2 := by omega
          rw [e1, e2] at h3 h4
          unfold boxLo
          rw [e3, e4, e5]
          constructor <;> omega
        · exfalso
          cases τ with
          | sm d => exact sm_copy d.site hpc
          | epi d => exact epi_copy d.site hpc
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_cp_site d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          have hev : ∃ bx, Proof.EvW.ldBox d.site = some bx ∧
              (⟨pc, .tensorIssue a sp⟩ : Event) =
                ⟨d.site.pc, .tensorIssue Q.kvMap (Proof.EvW.ldCopy Q L g d bx)⟩ := by
            unfold Proof.EvW.LdShape at hsh
            cases hst : d.site <;> rw [hst] at hsh hs <;> first
              | (simp [isCpS] at hs; done)
              | exact hsh
          obtain ⟨⟨v, sl, hh⟩, hbx, hk⟩ := hev
          simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hk
          obtain ⟨-, -, rfl⟩ := hk
          obtain ⟨hcd, hsl, hhh⟩ := ldBox_cp hbx
          have hel := ld_cp_elected hp hX hg k hlen.le _ hσ hs
          have h6 : g % L.block / 32 = 6 := role_warp hp hX hg k hlen _ hσ
          have hK : LdCnt Q L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
          have hin : d.site.inLoop = true := by
            cases hst : d.site <;> rw [hst] at hs <;> first | (simp [isCpS] at hs; done) | rfl
          have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
          have hCE := hK.CE hin _ hm3 ((Proof.Interface.electLead_of_elected hX hel).take k)
          simp only [ite_true] at hCE
          refine ⟨⟨_, _, _, _, _, rfl⟩, .inl ⟨w, d, P, n, hσ, h6, by rw [hcd]; cases v <;> simp <;>
            omega, hCE, fun x y z l hl => ?_⟩⟩
          unfold Proof.EvW.ldCopy at hl
          obtain ⟨-, -, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q _ _ _ _ _ hl
          unfold Proof.EvW.ldDst at h3 h4
          simp only at h3 h4
          unfold boxLo
          rw [hcd]
          cases v <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h3 h4 ⊢ <;>
            constructor <;> omega
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

/-! ### Two copies of one use -/

/-- The preloading copy `i` is by a lane of warp `i / 4`. -/
theorem preCp_warp (hp : Pre Q L m) {c s : Nat} (hc : c < L.grid) {i : Nat} (hi : i < 8) :
    (preCp L X c s i).1 % L.block / 32 = i / 4 ∧ (preCp L X c s i).1 = leadT L X c (i / 4) :=
  ⟨(leadT_cta (X := X) hc (w := i / 4) (by omega) hp.block).2.2, rfl⟩

/-- **The use of a copy by the loader's lane**: its earlier copies to the slot's barrier divided
by 8, plus the slot's preload. -/
theorem use_ld (hp : Pre Q L m) {c s : Nat} (hc : c < L.grid) (hs : s < 3) {h k : Nat}
    (hw : h % L.block / 32 = 6) :
    SingleTmaRing.copyUse X ((kvDecl Q L X c).slot ⟨s, hs⟩) (h, k) =
      ((X.tr h).take k).countP (issuesTo (Proof.EvW.kvReady L c s)) / 8 +
        (kvDecl Q L X c).δ ⟨s, hs⟩ := by
  unfold SingleTmaRing.copyUse
  split
  swap
  · rfl
  exfalso
  rename_i hcond
  obtain ⟨-, i, hi⟩ := hcond
  have hi' : (h, k) = preCp L X c s i.val := hi
  have := (preCp_warp (X := X) (s := s) hp hc (i := i.val) i.isLt).1
  rw [← hi'] at this
  simp only at this
  have hi8 : i.val < 8 := i.isLt
  omega

/-- **Two copies' writes of one ring byte in one use of its slot are one write of one
element.** -/
theorem copy_same_use (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g1 k1 g2 k2 x y z x' y' z' : Nat} {l : Loc}
    (hca : AsyncCovers X (g1, k1) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l) {s : Nat} (hs : s < 3)
    (hsl : InSlot L s l.addr)
    (heq : SingleTmaRing.copyUse X ((kvDecl Q L X (g1 / L.block)).slot ⟨s, hs⟩) (g1, k1) =
      SingleTmaRing.copyUse X ((kvDecl Q L X (g1 / L.block)).slot ⟨s, hs⟩) (g2, k2)) :
    (g1, k1) = (g2, k2) ∧ x = x' ∧ y = y' ∧ z = z' := by
  have hb : L.block = 256 := hp.block
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hca
  obtain ⟨pc2, a2, sp2, he2, hl2⟩ := copy_write_at hcb
  obtain ⟨⟨-, s1, hs1, hm1, hreg1, -⟩, -⟩ := copy_ring_ev hp hX he1
  obtain ⟨⟨-, s2, hs2, hm2, hreg2, -⟩, -⟩ := copy_ring_ev hp hX he2
  obtain ⟨-, hc1, hsl1⟩ := hreg1 x y z l hl1
  obtain ⟨-, hc2, hsl2⟩ := hreg2 x' y' z' l hl2
  have e1 : s1 = s := inSlot_unique hs1 hs hsl1 hsl
  have e2 : s2 = s := inSlot_unique hs2 hs hsl2 hsl
  subst s1 s2
  have hg1 := Frame.lt_of_get hX he1
  have hg2 := Frame.lt_of_get hX he2
  set c := g1 / L.block with hcdef
  have hc12 : g2 / L.block = c := by rw [← hc2, hc1]
  rw [hc12] at hm2
  have hcg : c < L.grid := NamedBar.cta_lt hg1
  have H := kv_events hp hX hcg
  obtain ⟨-, hI1⟩ := H.issue ⟨s, hs1⟩ he1 hm1
  obtain ⟨-, hI2⟩ := H.issue ⟨s, hs1⟩ he2 hm2
  obtain ⟨h6c, -, h6w⟩ := leadT_cta (X := X) hcg (w := 6) (by omega) hb
  -- the use of a preloading copy
  have hpre : ∀ {h k : Nat}, h % L.block / 32 < 2 →
      ((h = (kvDecl Q L X c).cp ∧ ((X.tr h).take k).countP (issuesTo
          ((kvDecl Q L X c).full ⟨s, hs1⟩)) + 1 ≤ (kvDecl Q L X c).n *
          okPolls ((kvDecl Q L X c).empty ⟨s, hs1⟩) ((X.tr h).take k)) ∨
        ((kvDecl Q L X c).δ ⟨s, hs1⟩ = 1 ∧ ∃ i, (h, k) = (kvDecl Q L X c).pCp ⟨s, hs1⟩ i)) →
      (kvDecl Q L X c).δ ⟨s, hs1⟩ = 1 ∧
        SingleTmaRing.copyUse X ((kvDecl Q L X c).slot ⟨s, hs1⟩) (h, k) = 0 ∧
        ∃ i : Fin 8, h = leadT L X c (i.val / 4) := by
    intro h k hw hI
    rcases hI with ⟨rfl, -⟩ | ⟨hδ, i, hi⟩
    · exfalso
      have : (kvDecl Q L X c).cp % L.block / 32 = 6 := h6w
      omega
    · refine ⟨hδ, ?_, i, ?_⟩
      · unfold SingleTmaRing.copyUse
        split
        · rfl
        · rename_i hcond
          exact absurd ⟨hδ, i, hi⟩ hcond
      · have hi' : (h, k) = preCp L X c s i.val := hi
        have := congrArg Prod.fst hi'
        simpa [preCp] using this
  suffices hid : (g1, k1) = (g2, k2) by
    refine ⟨hid, ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hid
    rw [he1] at he2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he2
    obtain ⟨-, -, rfl⟩ := he2
    obtain ⟨⟨cta, col, row, dst, bar, rfl⟩, -⟩ := copy_info hp hX he1
    exact Proof.Ring.Foot.kv_elem hl1 hl2
  obtain ⟨-, hk1⟩ := copy_info hp hX he1
  obtain ⟨-, hk2⟩ := copy_info hp hX he2
  rcases hk1 with ⟨w1, d1, P1, n1, hσ1, h61, hB1, hcnt1, hbx1⟩ |
      ⟨tm1, bw1, d1, n1, b1, j1, hσ1, hs1', hw1, hbx1⟩ <;>
    rcases hk2 with ⟨w2, d2, P2, n2, hσ2, h62, hB2, hcnt2, hbx2⟩ |
      ⟨tm2, bw2, d2, n2, b2, j2, hσ2, hs2', hw2, hbx2⟩
  · -- two loader copies: one thread, one box, one count
    obtain ⟨lo1, hi1⟩ := hbx1 x y z l hl1
    obtain ⟨lo2, hi2⟩ := hbx2 x' y' z' l hl2
    have hd1 : d1.i % 3 = s := inSlot_unique (Nat.mod_lt _ (by omega)) hs1
      (boxLo_slot hB1 lo1 hi1) hsl1
    have hd2 : d2.i % 3 = s := inSlot_unique (Nat.mod_lt _ (by omega)) hs1
      (boxLo_slot hB2 lo2 hi2) hsl1
    rw [hd1] at lo1 hi1 hcnt1
    rw [hd2] at lo2 hi2 hcnt2
    have hBB := boxLo_inj hB1 hB2 lo1 hi1 lo2 hi2
    have ht1 : g1 = (kvDecl Q L X c).cp := by
      rcases hI1 with ⟨h, -⟩ | ⟨-, i, hi⟩
      · exact h
      · exfalso
        have hi' : (g1, k1) = preCp L X c s i.val := hi
        have := (preCp_warp (X := X) (s := s) hp hcg (i := i.val) i.isLt).1
        rw [← hi'] at this
        have hi8 : i.val < 8 := i.isLt
        simp only at *; omega
    have ht2 : g2 = (kvDecl Q L X c).cp := by
      rcases hI2 with ⟨h, -⟩ | ⟨-, i, hi⟩
      · exact h
      · exfalso
        have hi' : (g2, k2) = preCp L X c s i.val := hi
        have := (preCp_warp (X := X) (s := s) hp hcg (i := i.val) i.isLt).1
        rw [← hi'] at this
        have hi8 : i.val < 8 := i.isLt
        simp only at *; omega
    have hgg : g1 = g2 := ht1.trans ht2.symm
    subst hgg
    rw [use_ld hp hcg hs1 h61, use_ld hp hcg hs1 h61] at heq
    rw [← hcdef] at hcnt1 hcnt2
    rw [hcnt1, hcnt2] at heq
    have hq : 8 * slotCnt (npOf Q L g1) d1.i s + cpDoneS d1.site =
        8 * slotCnt (npOf Q L g1) d2.i s + cpDoneS d2.site := by
      have e1 : (8 * slotCnt (npOf Q L g1) d1.i s + cpDoneS d1.site) / 8 =
          slotCnt (npOf Q L g1) d1.i s := by omega
      have e2 : (8 * slotCnt (npOf Q L g1) d2.i s + cpDoneS d2.site) / 8 =
          slotCnt (npOf Q L g1) d2.i s := by omega
      rw [e1, e2] at heq
      omega
    have hi1 : issuesTo (Proof.EvW.kvReady L c s) ⟨pc1, .tensorIssue a1 sp1⟩ = true := by
      rw [issuesTo_tensorIssue, hm1]; simp
    have hi2 : issuesTo (Proof.EvW.kvReady L c s) ⟨pc2, .tensorIssue a2 sp2⟩ = true := by
      rw [issuesTo_tensorIssue, hm2]; simp
    rw [same_count he1 he2 hi1 hi2 (hcnt1.trans (hq.trans hcnt2.symm))]
  · -- a loader copy and a preloading copy: uses at least 1 and 0
    exfalso
    obtain ⟨hδ, hu2, -⟩ := hpre hw2 hI2
    rw [use_ld hp hcg hs1 h61, hu2, hδ] at heq
    omega
  · exfalso
    obtain ⟨hδ, hu1, -⟩ := hpre hw1 hI1
    rw [use_ld hp hcg hs1 h62, hu1, hδ] at heq
    omega
  · -- two prologue copies: one site, one warp, so one thread and one position
    obtain ⟨lo1, hi1⟩ := hbx1 x y z l hl1
    obtain ⟨lo2, hi2⟩ := hbx2 x' y' z' l hl2
    have hj1 := j1.isLt
    have hj2 := j2.isLt
    have hB1 : 4 * (j1.val / 2) + 2 * (j1.val % 2) + g1 % L.block / 32 % 2 < 8 := by omega
    have hB2 : 4 * (j2.val / 2) + 2 * (j2.val % 2) + g2 % L.block / 32 % 2 < 8 := by omega
    have hb1 : b1.val = s := inSlot_unique b1.isLt hs1 (boxLo_slot hB1 lo1 hi1) hsl1
    have hb2 : b2.val = s := inSlot_unique b2.isLt hs1 (boxLo_slot hB2 lo2 hi2) hsl1
    rw [hb1] at lo1 hi1
    rw [hb2] at lo2 hi2
    have hBB := boxLo_inj hB1 hB2 lo1 hi1 lo2 hi2
    have hjj : j1 = j2 := Fin.ext (by omega)
    have hww : g1 % L.block / 32 = g2 % L.block / 32 := by omega
    have hbb : b1 = b2 := Fin.ext (hb1.trans hb2.symm)
    obtain ⟨-, -, i1, hl1'⟩ := hpre hw1 hI1
    obtain ⟨-, -, i2, hl2'⟩ := hpre hw2 hI2
    have hgg : g1 = g2 := by
      have e1 := (leadT_cta (X := X) hcg (w := i1.val / 4) (by omega) hb).2.2
      have e2 := (leadT_cta (X := X) hcg (w := i2.val / 4) (by omega) hb).2.2
      rw [← hl1'] at e1
      rw [← hl2'] at e2
      rw [hl1', hl2', show i1.val / 4 = i2.val / 4 by omega]
    subst hgg
    rw [pro_copy_once hp hX he1 he2 ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ hσ1 hσ2
      (by rw [hs1', hs2', hjj, hbb])]

/-! ### The rings' asynchronous accesses; the kv region -/

/-- **Two conflicting asynchronous accesses of a byte of the rings are ordered**: a copy and a
read by `copy_read_ordered`, two copies by their uses (`copies_diff_ordered`, `copy_same_use`),
two reads do not conflict. -/
theorem ring_async (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {i j : EvId} {p q : AsyncCopy.Part} {a b : Acc} {l : Loc}
    (hc : Conflict X (.async i p) (.async j q) a b) (ha : a.Covers l) (hb : b.Covers l)
    (hsp : l.space = .shared) (hhi : l.addr < L.sharedBase + 196608) :
    modelCausality L X l (.async i p) (.async j q) ∨
      modelCausality L X l (.async j q) (.async i p) := by
  obtain ⟨hne, we, wf, hie, hif, hw, -⟩ := hc
  have hca : AsyncCovers X i p l := ⟨a, we, hie, ha⟩
  have hcb : AsyncCovers X j q l := ⟨b, wf, hif, hb⟩
  obtain ⟨-, -, -, h1⟩ := async_shared hp hX hie ha hsp
  obtain ⟨-, -, -, h2⟩ := async_shared hp hX hif hb hsp
  rcases h1 with ⟨isB, idx, rfl, -⟩ | ⟨x, y, z, rfl, -⟩ <;>
    rcases h2 with ⟨isB', idx', rfl, -⟩ | ⟨x', y', z', rfl, -⟩
  · exfalso
    have h1 : we = false := hie.1
    have h2 : wf = false := hif.1
    rcases hw with h | h <;> simp_all
  · exact (copy_read_ordered hp hX hcb hca hsp hhi).symm
  · exact copy_read_ordered hp hX hca hcb hsp hhi
  · obtain ⟨g1, k1⟩ := i
    obtain ⟨g2, k2⟩ := j
    obtain ⟨pc1, a1, sp1, he1, -⟩ := copy_write_at hca
    obtain ⟨pc2, a2, sp2, he2, -⟩ := copy_write_at hcb
    have hg1 := Frame.lt_of_get hX he1
    have hg2 := Frame.lt_of_get hX he2
    obtain ⟨c, s, hs, hc1, hc2, hsl, hch⟩ := copies_diff_ordered hp hX hca hcb hsp
    obtain ⟨c', s', hs', hc1', hc2', hsl', hch'⟩ := copies_diff_ordered hp hX hcb hca hsp
    have hcc : c' = c := by rw [← hc1', hc2]
    obtain rfl := hcc
    obtain rfl := inSlot_unique hs' hs hsl' hsl
    rcases Nat.lt_trichotomy
      (SingleTmaRing.copyUse X ((kvDecl Q L X c').slot ⟨s', hs⟩) (g1, k1))
      (SingleTmaRing.copyUse X ((kvDecl Q L X c').slot ⟨s', hs⟩) (g2, k2)) with h | h | h
    · exact .inl ⟨.inl ⟨hg1, hg2, by rw [hc1, hc2]⟩, hch h⟩
    · exfalso
      rw [← hc1] at h
      obtain ⟨hid, rfl, rfl, rfl⟩ := copy_same_use hp hX hca hcb hs hsl h
      exact hne (by rw [hid])
    · exact .inr ⟨.inl ⟨hg2, hg1, by rw [hc1, hc2]⟩, hch' h⟩

/-- **`SharedOrder.kv` on the role table.** -/
theorem kv_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ConflictsOrdered L X (Proof.Safety.InKv L) := by
  intro e f a b l hc ha hb hl
  obtain ⟨-, we, wf, hie, hif, -, -⟩ := id hc
  have hl' := hl
  obtain ⟨hsp, hlo, hhi⟩ := hl
  rcases e with ⟨g, k⟩ | ⟨i, p⟩
  · exact (thread_notKv hp hX hie ha hl').elim
  rcases f with ⟨g', k'⟩ | ⟨j, q⟩
  · exact (thread_notKv hp hX hif hb hl').elim
  exact ring_async hp hX hc ha hb hsp hhi

end
end PTX.Kernels.InklingRelDecode.Proof2
