-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.LdPage
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox

@[expose] public section

/-! # The copies' boxes are inside the map

* `pp_inv`: every prologue state's loaded block-table words are the pages of their slabs (the
  prologue's `lb` loads of a preloaded block return the page, `lb_bytes`; the other steps keep the
  words, `ProA.btW_next`, `ProA.next_lb`).
* `pro_copy_page`: at a prologue copy site of copy `i`, block `i / 4` exists (the gate of the
  prologue's reference, `ProA.gate_iters`) and the word of the copy's slab is its page.
* `boxInBounds : Safety.BoxInBounds X`: a prologue copy by `ptc_kvspec` and `kvbox_noOob`, a loader
  copy by `loader_box_ok` with `ld_page`, `ld_copy_page`, `ww_inv` and `ld_rng`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Interface (LoaderPage)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The page of block-table word `k` of thread `g`'s CTA. -/
abbrev pageK (Q : Params) (L : Launch) (g k : Nat) : Nat :=
  Q.page (Proof.ProA.cta L g .z) (2 * (Proof.ProA.cta L g .x + k / 2 * Q.splits) + k % 2)

/-- A prologue state's loaded block-table words are pages. -/
def PPd (Q : Params) (L : Launch) (g : Nat) (d : ProA.D) : Prop :=
  ∀ k < 6, d.site.old ∈ Proof.ProA.lbAfter k → Proof.ProA.btW d.dt k = pageK Q L g k

theorem lbSite_of_mem {s : Proof.ProA.Site} (h : s ∈ Proof.ProA.lbSites) :
    ∃ k < 6, s = Proof.ProA.lbSite k := by
  simp only [Proof.ProA.lbSites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨4, by norm_num, rfl⟩
  · exact ⟨5, by norm_num, rfl⟩

theorem lbSite_notAfter {k : Nat} (hk : k < 6) : Proof.ProA.lbSite k ∉ Proof.ProA.lbAfter k := by
  interval_cases k <;> decide

theorem el0_notAfter {k : Nat} (hk : k < 6) : Proof.ProA.Site.el0 ∉ Proof.ProA.lbAfter k := by
  interval_cases k <;> decide

theorem lbAfter_pc {k : Nat} (hk : k < 6) {s : Proof.ProA.Site} (hs : s ∈ Proof.ProA.lbAfter k) :
    s.pc ≠ 27 := by
  revert s
  interval_cases k <;> decide

theorem lb_ofOld {k : Nat} (hk : k < 6) :
    ProA.Site.ofOld (Proof.ProA.lbSite k) = .lb ⟨k / 2, by omega⟩ ⟨k % 2, by omega⟩ := by
  interval_cases k <;> rfl

/-- **One prologue step keeps the words.** -/
theorem pp_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d d'' : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hR : ProA.PRef Q L g tm bw d) (hP : PPd Q L g d)
    (hn : ProA.next L g d e = some (some d'')) (hx : d''.site ≠ .exit) : PPd Q L g d'' := by
  obtain ⟨s, dt⟩ := d
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at hn
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d'') := by simpa [ProA.next, hk] using hn
  by_cases h1 : s = .bar18
  · subst h1
    simp only [ProA.next0, Option.some.injEq] at h'
    exact absurd (by rw [← h']) hx
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    have hs := ld2_succ h'
    intro j hj hm
    rw [hs] at hm
    exact absurd hm (el0_notAfter hj)
  have hf : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d'')) :=
    ProA.next0_flat h1 h2 h3 h'
  intro j hj hm
  rcases Proof.ProA.lbAfter_next hf j hj hm with hs | hs
  · have hb := hP j hj hs
    by_cases hlb : s.old ∈ Proof.ProA.lbSites
    · obtain ⟨k', hk'6, hk'⟩ := lbSite_of_mem hlb
      rw [hk'] at hf
      obtain ⟨_, _, _, _, -, -, -, -, -, hkeep⟩ := Proof.ProA.next_lb hk'6 hf
      have hne : j ≠ k' := by
        rintro rfl
        rw [hk'] at hs
        exact lbSite_notAfter hj hs
      exact (hkeep j hj hne).trans hb
    · exact (Proof.ProA.btW_next hf hlb j).trans hb
  · rw [hs] at hf
    obtain ⟨a, bs, v, x, hk', hrb, hw, hbt, -, -⟩ := Proof.ProA.next_lb hj hf
    have hsl : (⟨s, dt⟩ : ProA.D).site = .lb ⟨j / 2, by omega⟩ ⟨j % 2, by omega⟩ := by
      show s = _
      rw [← ProA.ofOld_old s h2, hs, lb_ofOld hj]
    obtain ⟨hpg, hbs⟩ := lb_bytes hp hX he hσ hR hsl
    have e2 : 2 * (j / 2) + j % 2 = j := by omega
    simp only [e2] at hpg hbs
    have hbs' := hbs a bs hk'
    rw [hbs', rebuild_b32] at hrb
    cases hrb
    rw [Proof.ProA.word32_b32 hpg] at hw
    cases hw
    exact hbt

/-- The prologue states of the thread machine. -/
def PP (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _) => PPd Q L g d
  | _ => True

/-- **Every prologue state's loaded block-table words are pages.** -/
theorem pp_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      PP Q L g σ := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hget : X.get (g, k) = some e := he
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, dd⟩
      · -- the startup enters the prologue at pc 27, which no loaded site has
        rw [next_start] at hn
        obtain ⟨s', -, hs'⟩ := mm_some hn
        cases hxo : Startup.enterOf s' with
        | none =>
          rw [enter_inl hxo] at hs'
          subst hs'
          trivial
        | some r =>
          cases hsel : sel L g r s' with
          | none =>
            rw [Code.enter_some (i := Sum.inr r) (by simp [Code.gatedExit, hxo, hsel])] at hs'
            subst hs'
            trivial
          | some ro =>
            rw [Code.enter_some (i := Sum.inl ro) (by simp [Code.gatedExit, hxo, hsel])] at hs'
            cases ro with
            | worker w => subst hs'; trivial
            | dp tm1 bw1 =>
              obtain ⟨x', n'⟩ := σ'
              rcases x' with s2 | ⟨_ | r2, d2⟩
              · simp at hs'
              · rename_i i2
                cases i2 with
                | worker w2 => trivial
                | dp tm2 bw2 =>
                  rcases d2 with d2 | τ
                  · intro j hj hm
                    exfalso
                    have h1 := congrArg (thread Q L g).pc hs'
                    change 27 = d2.site.pc at h1
                    have hx2 : d2.site ≠ .exit := by
                      intro h; rw [h] at h1; exact absurd h1 (by decide)
                    rw [ProA.pc_old _ hx2] at h1
                    exact lbAfter_pc hj hm h1.symm
                  · trivial
              · trivial
      · rename_i i
        obtain ⟨d2, hd2⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd2
        subst hd2
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases dd with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            cases hxo : ProA.exitOf d'' with
            | some v =>
              cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                rw [← he''.1]
                trivial
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                rw [← he''.1]
                trivial
            | none =>
              rw [Code.enter_none (by simp [Code.gatedExit, hxo])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                true_and] at he''
              rw [← he''.1]
              have hx : d''.site ≠ .exit := by
                intro h; simp [ProA.exitOf, h] at hxo
              obtain ⟨-, -, hP, -⟩ := (hJ : ProRef Q L g tm bw d n)
              exact pp_step hp hX hget hk0 hP hR0 hd'' hx
          · rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
              true_and] at he''
            rw [← he''.1]
            trivial
          · exact hJ.elim
      · exact hJ.elim


/-! ### The prologue's copies -/

/-- **A prologue copy's block exists and its slab's word is the page.** -/
theorem pro_copy_page (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    {b : Fin 3} {j : Fin 4} (hs : d.site = .ptc b j) :
    (4 * b.val + j.val) / 4 < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) ∧
      Proof.ProA.btW d.dt (2 * ((4 * b.val + j.val) / 4) + (4 * b.val + j.val) % 4 / 2) =
        Q.page (Proof.ProA.cta L g .z) (2 * (Proof.ProA.cta L g .x +
          (4 * b.val + j.val) / 4 * Q.splits) + (4 * b.val + j.val) % 4 / 2) := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hJ := (good_all' hp hX hg k).2 _ hσ
  obtain ⟨-, -, hR, -⟩ := (hJ : ProRef Q L g tm bw d n)
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have ha : Proof.ProA.ArgsOk L g d.dt.pro := hi.1.args
  have hspl := hp.splitsRange
  have hw : d.dt.pro.w71 = Q.splits := by
    rw [hR.pro]; exact Nat.mod_eq_of_lt (by omega)
  have hi12 : 4 * b.val + j.val < 12 := by omega
  have hold : d.site.old = Proof.ProA.ptcSite (4 * b.val + j.val) := by rw [hs]; exact ptc_old b j
  have hmem : ∀ i < 12, Proof.ProA.ptcSite i ∈ Proof.ProA.blkSites (i / 4) ∧
      Proof.ProA.ptcSite i ∈ Proof.ProA.lbAfter (2 * (i / 4) + i % 4 / 2) ∧
      (Proof.ProA.ptcSite i).afterSk = true ∧ Proof.ProA.ptcSite i ≠ .sMax ∧
      Proof.ProA.ptcSite i ≠ .ldCu0 := by
    intro i hi
    interval_cases i <;> decide
  obtain ⟨hb1, hb2, hb3, hn1, hn2⟩ := hmem _ hi12
  obtain ⟨w0, w1, w2⟩ := hR.words
  have hdold : (ProA.D.old d).site = Proof.ProA.ptcSite (4 * b.val + j.val) := hold
  rw [hdold] at w0 w1 w2
  have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) d.dt :=
    ⟨w0 hn1 hn2, w1 (.inl hb3), w2 hb3⟩
  obtain ⟨c0, c1, c2⟩ := Proof.ProA.gate_iters hp hg ha hw hm
  obtain ⟨g0, g1, g2⟩ := hR.gate
  rw [hold] at g0 g1 g2
  refine ⟨?_, ?_⟩
  · have hb3' : (4 * b.val + j.val) / 4 < 3 := by omega
    rcases (by omega : (4 * b.val + j.val) / 4 = 0 ∨ (4 * b.val + j.val) / 4 = 1 ∨
      (4 * b.val + j.val) / 4 = 2) with h | h | h <;> rw [h] at hb1 ⊢
    · exact c0 (g0 hb1)
    · exact c1 (g1 hb1).1 (g1 hb1).2
    · exact c2 (g2 hb1).1 (g2 hb1).2.1 (g2 hb1).2.2
  · have hP : PPd Q L g d := pp_inv hp hX hg k hlen _ hσ
    have := hP (2 * ((4 * b.val + j.val) / 4) + (4 * b.val + j.val) % 4 / 2) (by omega)
      (by rw [hold]; exact hb2)
    have e1 : (2 * ((4 * b.val + j.val) / 4) + (4 * b.val + j.val) % 4 / 2) / 2 =
        (4 * b.val + j.val) / 4 := by omega
    have e2 : (2 * ((4 * b.val + j.val) / 4) + (4 * b.val + j.val) % 4 / 2) % 2 =
        (4 * b.val + j.val) % 4 / 2 := by omega
    simp only [pageK, e1, e2] at this
    exact this

/-! ### The boxes -/

/-- **Every tensor copy is a K or V box of an existing slab.** -/
theorem copy_form (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc a : Nat} {s : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) :
    ∃ r sl kvh isV hh dst bar, r < Q.b ∧ sl < 2 * Q.blocks r ∧ kvh < kvHeads ∧ isV ≤ 1 ∧
      hh ≤ 1 ∧ s = Proof.EvW.kvCopySpec Q (g / L.block) (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hx, hy, hz⟩ := Proof.ProA.cta_lt hp hg
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hop : tensorOp ins.op = true := by
      cases hq : tensorOp ins.op
      · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a s)
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
          obtain ⟨hlt, hpage⟩ := pro_copy_page hp hX he hσ hs
          have hblk := Proof.Result.Mma.blk_lt hp.splitsPos hlt
          have hw3 : d.dt.pro.w68 = Q.pageRows % 2 ^ 32 ∧ d.dt.pro.w69 = Q.headRows % 2 ^ 32 ∧
              d.dt.pro.w70 = Q.headCols % 2 ^ 32 := by
            rw [hP.pro]; exact ⟨rfl, rfl, rfl⟩
          rw [Proof.Interface.ptc_kvspec (d := ProA.D.old d) hp hw3 hi12 _ hpage]
          exact ⟨_, _, _, _, _, _, _, hz, by omega, hy, by omega,
            Nat.le_of_lt_succ (Proof.ProA.half_lt _ _), rfl⟩
        · cases τ with
          | sm d => exact (sm_copy d.site hpc).elim
          | epi d => exact (epi_copy d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hne : ¬ Ends (⟨pc, .tensorIssue a s⟩ : Event) := by simp [Ends]
          have h' := ld_shape hp hX he hne hσ
          have hpro : Proof.Loader.ProEq L g P d := (hi : Proof.WComp.Inv L g (.loader d P)).2.1
          have hm : Proof.EvW.Words Q P := ww_inv hp hX hg k hlen.le _ hσ
          have hrg : Proof.Loader.Rng d := ld_rng hp hX hg k hlen _ hσ
          have hpg : LoaderPage Q L g d := ld_page hp hX hg k hlen _ hσ
          unfold Proof.EvW.LdShape at h'
          split at h'
          all_goals try (exfalso; revert h'; simp; done)
          all_goals
            obtain ⟨⟨b1, b2, b3⟩, hb, h'⟩ := h'
            simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h'
            obtain ⟨-, -, rfl⟩ := h'
            rename_i hsite
            have hinLoop : d.site.inLoop = true := by rw [hsite]; rfl
            have hpre' : Proof.Interface.preLoop d.site = false := by rw [hsite]; rfl
            have hi' : d.i < Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) := by
              rw [← hpg.1 hpre']; exact hrg.loop hinLoop
            have hpage := ld_copy_page hp hX hlen hg hσ hb
            rw [hsite] at hb
            simp only [Proof.EvW.ldBox, Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨hb1, hb2, hb3⟩ := hb
            have hs2 : b2 ≤ 1 := by omega
            have hh2 : b3 ≤ 1 := by omega
            have hblk := Proof.Result.Mma.blk_lt hp.splitsPos hi'
            have hsl : 2 * Proof.Result.Mma.blkOf Q L g d.i + b2 <
                2 * Q.blocks (Proof.ProA.cta L g .z) := by
              unfold Proof.Result.Mma.blkOf Proof.Result.Mma.splitOf; omega
            cases b1
            · first
                | exact absurd hb1 (by decide)
                | (have hc := Proof.Result.Mma.loader_copy_spec hm hpro (isV := 0) (hh := b3)
                     (by norm_num) hpage
                   simp only [show decide ((0 : Nat) = 1) = false by decide] at hc
                   exact ⟨_, _, _, 0, b3, _, _, hz, hsl, hy, by norm_num, hh2, hc⟩)
            · first
                | exact absurd hb1 (by decide)
                | (have hc := Proof.Result.Mma.loader_copy_spec hm hpro (isV := 1) (hh := b3)
                     (by norm_num) hpage
                   exact ⟨_, _, _, 1, b3, _, _, hz, hsl, hy, le_refl _, hh2, hc⟩)
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

/-- **Every tensor copy's box is inside the map** (`Safety.BoxInBounds`). -/
theorem box_in_bounds (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ {g k pc a : Nat} {s : TensorCopy.Spec},
      X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ → ¬ TensorHasOob s.descriptor s.origin s.rows := by
  intro g k pc a s he
  obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hk, hV, hH, rfl⟩ := copy_form hp hX he
  exact Proof.Interface.kvbox_noOob hp hr hs hk hV hH _ _ _
end
end PTX.Kernels.InklingRelDecode.Proof2
