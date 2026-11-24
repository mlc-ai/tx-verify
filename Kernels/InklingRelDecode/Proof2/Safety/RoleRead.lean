-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.WBar1
public import Kernels.InklingRelDecode.Proof2.Safety.Async
public import Kernels.InklingRelDecode.Proof2.Lib.ReadSame
public import Kernels.InklingRelDecode.Proof.Thread.ScFence

@[expose] public section

/-! # The role byte's reads

A dispatch read of the role byte of warp `w` (4 to 7) at a barrier-1 count of 1 returns byte
`w - 4` of the prologue's `st8` word `0x01000202` (the role: 2 idle, 0 loader, 1 MMA); at a count
of 4 or more, byte `w - 4` of the epilogue's `stTab` word `0x03030303` (the exit path). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **No step of the flat prologue goes past its role-word store except the store's own.** -/
theorem old_next_cross_st8 {s : Proof.ProA.Site} {dt : Proof.ProA.Dat} {d' : Proof.ProA.D}
    {e : Event} (h : Proof.ProA.next L g ⟨s, dt⟩ e = some (some d'))
    (hs : s.pc ≤ Proof.ProA.Site.st8.pc) (hd : Proof.ProA.Site.st8.pc < d'.site.pc) :
    s = .st8 := by
  cases s <;> first
    | rfl
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Proof.ProA.next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            exfalso
            simp only at hd
            first
              | (revert hd; decide +kernel)
              | exact absurd hd (Nat.not_lt.mpr (le_trans (Proof.ProA.qSite_pc_le _ _ _ _)
                  (by decide +kernel)))))

/-- **No step of the prologue goes past its role-word store except the store's own.** -/
theorem cross_st8 {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (hs : d.site.pc ≤ 570) (hd : 570 < d'.site.pc) : d.site = .st8 := by
  obtain ⟨s, dt⟩ := d
  simp only at hs ⊢
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1; exact absurd hs (by decide)
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    rw [ld2_succ h'] at hd
    exact absurd hd (by decide)
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hx' : d'.site ≠ .exit := fun hx => h1 (exit_from_bar18 h hx)
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  have hc := old_next_cross_st8 hf' (by rw [← ProA.pc_old s h2]; exact hs)
    (by show Proof.ProA.Site.st8.pc < d'.site.old.pc; rw [← ProA.pc_old _ hx']; exact hd)
  rw [← ProA.ofOld_old s h2, hc]
  rfl

/-- **A prologue state past the role-word store has the store's state earlier.** -/
theorem st8_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ tm bw d n,
      Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)) →
      570 < d.site.pc → ∃ j < k, ∃ d0 n0,
        Frame.stateAt (thread Q L) X g j = some (some (.inr ⟨.inl (.dp tm bw), .inl d0⟩, n0)) ∧
        d0.site = .st8 := by
  intro k
  induction k with
  | zero =>
    intro _ tm bw d n hσ _
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    simp at hσ
  | succ k ih =>
    intro hk tm bw d' n' hσ' hpc
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some (.inr ⟨.inl (.dp tm bw), .inl d'⟩, n')) :=
        hσ'
      have hJ := hF.2 σ hk0
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, dd⟩
      · -- the startup enters the prologue at its first site
        exfalso
        rw [next_start] at hn
        obtain ⟨s', -, hs'⟩ := mm_some hn
        cases hx : Startup.enterOf s' with
        | none =>
          rw [enter_inl hx] at hs'
          simp at hs'
        | some r =>
          cases hsel : sel L g r s' with
          | none =>
            rw [Code.enter_some (i := Sum.inr r) (by simp [Code.gatedExit, hx, hsel])] at hs'
            simp at hs'
          | some ro =>
            rw [Code.enter_some (i := Sum.inl ro) (by simp [Code.gatedExit, hx, hsel])] at hs'
            cases ro with
            | worker w => simp at hs'
            | dp tm1 bw1 =>
              have h1 := congrArg (thread Q L g).pc hs'
              change 27 = d'.site.pc at h1
              omega
      · rename_i i
        obtain ⟨d2, hd2⟩ := next_same_role hn
        simp only [Sum.inr.injEq] at hd2
        cases i with
        | dp tm0 bw0 =>
          obtain ⟨h1, h2⟩ : tm0 = tm ∧ bw0 = bw := by
            have := (Sigma.mk.inj hd2).1
            simp only [Sum.inl.injEq, Role.dp.injEq] at this
            exact ⟨this.1.symm, this.2.symm⟩
          cases h1
          cases h2
          rcases dd with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hx : ProA.exitOf d'' = none := by
              cases hxo : ProA.exitOf d'' with
              | none => rfl
              | some v =>
                exfalso
                cases hsel : ProA.selTail Q L g v d'' with
                | some dt' =>
                  rw [Code.enter_some (i := Sum.inl dt')
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp at he''
                | none =>
                  rw [Code.enter_some (i := Sum.inr ())
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp at he''
            rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and,
              Sum.inl.injEq] at he''
            obtain ⟨rfl, -⟩ := he''
            by_cases hle : d.site.pc ≤ 570
            · have hs8 := cross_st8 hd'' hle hpc
              exact ⟨k, by omega, d, n, hk0, hs8⟩
            · obtain ⟨j, hj, d0, n0, h0, h8⟩ := ih hlt _ _ d n hk0 (by omega)
              exact ⟨j, by omega, d0, n0, h0, h8⟩
          · exfalso
            rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp at he''
          · exact hJ.elim
        | worker w =>
          exfalso
          have := (Sigma.mk.inj hd2).1
          simp at this
      · exact hJ.elim

/-- A byte of a CTA's role word. -/
def InRoleWord (L : Launch) (c : Nat) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = c ∧ L.sharedBase + 213336 ≤ l.addr ∧ l.addr < L.sharedBase + 213340

/-- **A write of a role-word byte is the prologue's `st8` at barrier-1 count 0 or the epilogue's
`stTab` at count 3**, of a default-partition thread of the CTA. -/
theorem role_wr_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, j) = some ⟨pc, .wr a bs⟩)
    {l : Loc} (hl : a.Covers l) (hr : InRoleWord L (h / L.block) l) :
    a = Proof.EvD.wordAcc ⟨.shared, h / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩ ∧
      h % L.block < 128 ∧
      ((∃ v, storeValue 32 (b32 16777730) = .ok v ∧ bs = v.toBytes ∧
          ((X.tr h).take j).countP (Execution.isBarId 1) = 0) ∨
        (∃ v, storeValue 32 (b32 50529027) = .ok v ∧ bs = v.toBytes ∧
          ((X.tr h).take j).countP (Execution.isBarId 1) = 3)) := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨hs1, hc1, hlo, hhi⟩ := hl
  obtain ⟨hrs, hrc, hrlo, hrhi⟩ := hr
  have hm : ∀ c, c ≤ 213340 → (L.sharedBase + c) % 2 ^ 32 = L.sharedBase + c := fun c hc =>
    Nat.mod_eq_of_lt (by omega)
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hlen : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hC := c1_inv hp hX hg j hlen σ hσ
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := OpPcsFast.mem kernel_wr_pcs hc (fires_write_op hf rfl)
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exfalso
      rcases startup_wr st.site hpc with hs | hs
      · have h' : Startup.Ev L h st ⟨pc, .wr a bs⟩ := hev
        simp [Startup.Ev, hs] at h'
      · have h' : Startup.Ev L h st ⟨pc, .wr a bs⟩ := hev
        simp only [Startup.Ev, hs] at h'
        obtain ⟨col, -, h'⟩ := h'
        simp only [Event.mk.injEq, Kind.wr.injEq] at h'
        obtain ⟨-, rfl, -⟩ := h'
        simp only at hlo hhi
        omega
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hx : d.site ≠ .exit := by
            rcases proA_wr d.site hpc with ⟨_, _, hs⟩ | hs | ⟨_, hs⟩ <;> rw [hs] <;> simp
          have hF := ProA.fired_old (P := Startup.inh L h Q tm) hx hat hi.1 hc hf
          have htid : h % L.block < 128 := hi.1.args.tid
          rcases proA_wr d.site hpc with ⟨i, jj, hs⟩ | hs | ⟨jj, hs⟩
          · exfalso
            have hsr' : Proof.ProA.SbRoom L := by unfold Proof.ProA.SbRoom; omega
            obtain ⟨v, bs', a', -, he', hl', hz, h1, h2⟩ := Proof.ProA.shape_stq_foot
              (m := i.val) (w := jj.val) i.isLt jj.isLt htid hsr' hF
              (by simp only [ProA.D.old, hs, stq_old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            rw [hz] at hhi
            omega
          · obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st8 hF
              (by simp [ProA.D.old, hs, ProA.Site.old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            refine ⟨rfl, htid, .inl ⟨v, hv, rfl, ?_⟩⟩
            have hC' : _ = proPh d := hC
            rw [hC']
            simp [proPh, hs]
          · exfalso
            fin_cases jj
            · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_0 hF
                (by simp [ProA.D.old, hs, ProA.Site.old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              simp only [Proof.EvD.wordAcc, hm 212992 (by omega)] at hlo hhi
              omega
            · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_1 hF
                (by simp [ProA.D.old, hs, ProA.Site.old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              simp only [Proof.EvD.wordAcc, hm 212992 (by omega)] at hlo hhi
              omega
        · cases τ with
          | sm d =>
            exfalso
            have hs := sm_wr d.site hpc
            obtain ⟨bs', he'⟩ := Proof.Sm.shape_store10_foot (Proof.ProA.sharedOk_of_pre hp)
              (sm_fired hat hi hc hf) hs
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            simp only [Proof.EvD.wordAcc] at hlo hhi
            have hw : h % L.block / 32 % 4 < 4 := Nat.mod_lt _ (by omega)
            omega
          | epi d =>
            have h' : Proof.Epi.Shape L h d ⟨pc, .wr a bs⟩ := hev
            have hC' : _ = epiPh d := hC
            have htid : h % L.block < 128 := by
              have hw : d.pr.w = h % L.block / 32 := hi.2
              have hw4 := (hi.1 : Proof.Epi.Inv d).ok.w
              omega
            unfold Proof.Epi.Shape at h'
            split at h'
            all_goals first
              | exact h'.elim
              | (simp only [Event.mk.injEq, reduceCtorEq, and_false, exists_false] at h'; done)
              | (rename_i hs
                 obtain ⟨v, hv, h'⟩ := h'
                 simp only [Event.mk.injEq, Kind.wr.injEq] at h'
                 obtain ⟨-, rfl, rfl⟩ := h'
                 first
                   | (refine ⟨rfl, htid, .inr ⟨v, hv, rfl, ?_⟩⟩
                      rw [hC', show epiPh d = 3 by simp [epiPh, hs]])
                   | (exfalso; simp [Proof.EvD.wordAcc] at hs1 hrs; simp_all))
        · exact hJ.elim
      | worker w =>
        exfalso
        cases d with
        | worker w => exact worker_wr w.site hpc
        | idle d => exact idle_wr d.site hpc
        | loader d P => exact loader_wr d.site hpc
        | mma d P => exact mma_wr d.site hpc
        | exit x => exact exitsite_wr x.site hpc
    · exact hJ.elim

/-- The role word's access of a CTA. -/
abbrev roleAcc (L : Launch) (c : Nat) : Acc :=
  Proof.EvD.wordAcc ⟨.shared, c, (L.sharedBase + 213336) % 2 ^ 32⟩

theorem countP_take_mono (P : Event → Bool) (l : List Event) {i j : Nat} (h : i ≤ j) :
    (l.take i).countP P ≤ (l.take j).countP P := by
  have := (List.take_sublist_take_left (l := l) h).countP_le (p := P)
  exact this

/-- **The CTA's thread 0 was at its `st8` state before its first barrier-1 arrival** (at
position `i0`, with no barrier-1 event before it), once a thread of the CTA has passed its first
barrier-1 event. -/
theorem st8_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j0 pc0 : Nat} (hb0 : X.IsBarrier (g, j0) 1 none pc0)
    (hpass : j0 + 1 < (X.tr g).length)
    (h0c : ((X.tr g).take j0).countP (Execution.isBarId 1) = 0) :
    ∃ i0 j8 tm bw d8 n8, j8 < i0 ∧ i0 < (X.tr (g / L.block * L.block)).length ∧
      ((X.tr (g / L.block * L.block)).take i0).countP (Execution.isBarId 1) = 0 ∧
      (∃ ev, X.get (g / L.block * L.block, i0) = some ev ∧ Execution.isBarId 1 ev = true) ∧
      Frame.stateAt (thread Q L) X (g / L.block * L.block) j8 =
        some (some (.inr ⟨.inl (.dp tm bw), .inl d8⟩, n8)) ∧ d8.site = .st8 := by
  have hb : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg : g < L.threads := Frame.lt_of_get hX hb0
  set h0 := g / L.block * L.block with hh0
  have hh0t : h0 < L.threads := lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hh0c : h0 / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  have hh0w : h0 % L.block = 0 := Nat.mul_mod_left _ _
  have hw1 : (h0 % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
    rw [hh0w]; simp [CtaBarrier.warps, hb]
  obtain ⟨i0, pci, mi, hi0, hci⟩ := (bar1_sources hp hX).member_arrival_any hX (bar1_shape hp)
    hb0 hpass hh0c hw1 (fun hex => by
      obtain ⟨i, pc', hIs, hord⟩ := bar1Exits hp hX hb0 hpass hh0c hex
      exact ⟨i, pc', .sync, hIs, hord⟩)
  simp only at hci
  rw [h0c] at hci
  have hlen0 : i0 < (X.tr h0).length := (List.getElem?_eq_some_iff.mp hi0).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hi0 (fun f h => by cases h)
  have hC := c1_inv hp hX hh0t i0 hlen0 σ hσ
  have hS := (tm_inv hp hX hh0t i0 hlen0 σ hσ).2
  have hpc := bar1_pc hc hf rfl (by omega)
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exact (startup_bar1 st.site hpc).elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · have hs := proA_site_bar1 d.site hpc
        have hpc8 : 570 < d.site.pc := by rw [hs]; decide
        obtain ⟨j8, hj8, d8, n8, h8σ, h8s⟩ := st8_before hp hX hh0t i0 hlen0 tm bw d n hσ hpc8
        exact ⟨i0, j8, tm, bw, d8, n8, hj8, hlen0, hci, ⟨_, hi0, by simp [Execution.isBarId]⟩,
          h8σ, h8s⟩
      · exfalso
        cases τ with
        | sm d =>
          have hC' : _ = smPh d := hC
          have : 1 ≤ smPh d := by unfold smPh; split <;> omega
          omega
        | epi d =>
          have hC' : _ = epiPh d := hC
          have : 2 ≤ epiPh d := by unfold epiPh; split <;> omega
          omega
      · exact hJ.elim
    | worker w =>
      exfalso
      have : 4 ≤ h0 % L.block / 32 := hS
      omega
  · exact hJ.elim

/-- **The CTA's thread 0 made its `st8` store before its first barrier-1 arrival**, once a
thread of the CTA has passed its first barrier-1 event. -/
theorem st8_exists (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j0 pc0 : Nat} (hb0 : X.IsBarrier (g, j0) 1 none pc0)
    (hpass : j0 + 1 < (X.tr g).length)
    (h0c : ((X.tr g).take j0).countP (Execution.isBarId 1) = 0) :
    ∃ j8 pc8 v, storeValue 32 (b32 16777730) = .ok v ∧
      X.get (g / L.block * L.block, j8) =
        some ⟨pc8, .wr (roleAcc L (g / L.block)) v.toBytes⟩ ∧
      ((X.tr (g / L.block * L.block)).take (j8 + 1)).countP (Execution.isBarId 1) = 0 := by
  have hb : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg : g < L.threads := Frame.lt_of_get hX hb0
  obtain ⟨i0, j8, tm, bw, d8, n8, hj8, hlen0, hci, -, h8σ, h8s⟩ := st8_state hp hX hb0 hpass h0c
  have hh0t : (g / L.block * L.block) < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hh0c : (g / L.block * L.block) / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  have hl8 : j8 < (X.tr (g / L.block * L.block)).length := by omega
  obtain ⟨e8, he8⟩ : ∃ e, X.get ((g / L.block * L.block), j8) = some e :=
    ⟨_, List.getElem?_eq_getElem hl8⟩
  obtain ⟨t8, ins8, o8, hat8, hi8, hc8, hf8⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he8 h8σ
  cases o8 with
  | none =>
    exfalso
    have hE := fires_none_ends hf8
    obtain ⟨r8, hr8⟩ := hX.thr (g / L.block * L.block) hh0t
    have := Flow.Run.end_last hr8 he8 hE
    omega
  | some u8 =>
    have hx8 : d8.site ≠ .exit := by rw [h8s]; simp
    have hF8 := ProA.fired_old (P := Startup.inh L (g / L.block * L.block) Q tm) hx8 hat8 hi8.1
      hc8 hf8
    obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st8 hF8
      (by simp [ProA.D.old, h8s, ProA.Site.old])
    refine ⟨j8, _, v, hv, by rw [he8, he', hh0c], ?_⟩
    have hle := countP_take_mono (Execution.isBarId 1) (X.tr (g / L.block * L.block))
      (show j8 + 1 ≤ i0 by omega)
    omega

/-- **The first read of the role byte**: a dispatch read at barrier-1 count 1 returns the byte
of the prologue's `st8` word at its address. -/
theorem role_read1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    {w : Value} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker w), .worker ⟨.ldRole, P⟩⟩, n)))
    (h1 : ((X.tr g).take k).countP (Execution.isBarId 1) = 1) :
    ∃ v, storeValue 32 (b32 16777730) = .ok v ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 213332 + g % L.block / 32⟩ ∧
      bs = [wbyte (roleAcc L (g / L.block)) v.toBytes a.loc] := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- the read's footprint
  have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
  have hw8 : g % L.block / 32 < 8 := by
    have := Nat.mod_lt g (show 0 < L.block by omega)
    omega
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u => exact ⟨u, rfl⟩
  have hF : (Proof.WComp.code L g Q).toMachine.Fired (some (.worker ⟨.ldRole, P⟩))
      ⟨pc, .rd a bs⟩ (some u) := by
    refine ⟨t, ⟨hat, hi⟩, ?_⟩
    have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.worker ⟨.ldRole, P⟩)]? = some ins := hc
    show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.worker ⟨.ldRole, P⟩)) t) _ (some u)
    simp only [Code.tmpl]
    rw [hc', hat.1]
    exact hf
  obtain ⟨ac, bs', he', hl, hz⟩ := Proof.Worker.shape_ldRole hp
    (by rw [hb]; exact Nat.mod_lt _ (by omega)) rfl hF
  simp only [Event.mk.injEq, Kind.rd.injEq] at he'
  obtain ⟨-, rfl, rfl⟩ := he'
  have hwo : Proof.Worker.warpOf L g = g % L.block / 32 := rfl
  rw [hwo] at hl
  -- the reader's first barrier-1 event
  obtain ⟨j0, ev0, hj0, hb0e, hc0⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 1)
    (show 0 + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) by omega)
  have hj0k : j0 < k := by
    have := (List.getElem?_eq_some_iff.mp hj0).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hj0k.le] at hc0
  have hget0 : X.get (g, j0) = some ev0 := by
    change (X.tr g)[j0]? = some ev0
    rw [← hj0, List.getElem?_take, ite_eq_left hj0k]
  obtain ⟨pc0, k0⟩ := ev0
  obtain ⟨cnt0, md0, hk0⟩ := isBarId1_kind hb0e
  simp only at hk0
  subst hk0
  obtain ⟨hmd, hcnt⟩ := bar_event_static hX (by omega) hget0
  rcases hcnt with ⟨hcn, -⟩ | ⟨h01, -⟩
  · subst hmd hcn
    obtain ⟨j8, pc8, v, hv, hget8, hc8⟩ := st8_exists hp hX hget0 (by omega) hc0
    refine ⟨v, hv, hl, ?_⟩
    -- the store is before the read
    have hg0t : g / L.block * L.block < L.threads :=
      lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
    have hcta0 : g / L.block * L.block / L.block = g / L.block :=
      Nat.mul_div_cancel _ (by omega)
    have hw0 : ((g / L.block * L.block) % L.block) / 32 ∈
        Finset.range (CtaBarrier.warps L.block) := by
      rw [Nat.mul_mod_left]; simp [CtaBarrier.warps, hb]
    have hbc8 : baseCausality L X (g / L.block * L.block, j8) (g, k) :=
      bar1_handoff hp hX _ _ j8 k ⟨⟨hg0t, hg, hcta0⟩, hw0, trivial⟩ hlen
        (by simp only; rw [hc8, h1]; omega)
    -- the read of the one byte
    have hrd : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
    have hac : a.size = 1 := hz
    have hbl : bs.length = 1 := by rw [← hac]; exact (hX.rf _ _ _ hrd).1
    have hl0 : a.loc.at 0 = a.loc := by simp [Loc.at]
    have hrole : InRoleWord L (g / L.block) a.loc := by
      rw [hl]; exact ⟨rfl, rfl, by simp only; omega, by simp only; omega⟩
    have hbyte := read_byte_of_writers hX hrd (k := 0) (by omega)
      (fun ref => ∃ i pc', ref = .thread i ∧
        X.get i = some ⟨pc', .wr (roleAcc L (g / L.block)) v.toBytes⟩)
      (wbyte (roleAcc L (g / L.block)) v.toBytes a.loc)
      ⟨.thread (g / L.block * L.block, j8), roleAcc L (g / L.block), v.toBytes,
        ⟨_, pc8, rfl, hget8⟩, Or.inl ⟨pc8, hget8⟩, ?_, .direct (.inl hbc8)⟩
      (fun w dst written hW hm hcov => by
        obtain ⟨i, pc', rfl, hgi⟩ := hW
        rcases hm with ⟨pcm, hm⟩ | ⟨old, pcm, hm⟩
        · rw [hgi] at hm
          simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hm
          obtain ⟨-, rfl, rfl⟩ := hm
          rw [hl0]
        · rw [hgi] at hm; simp at hm)
      (fun w' dst' bytes hm hcov => by
        rw [hl0] at hcov
        rcases w' with ⟨h, j⟩ | ⟨i, p⟩
        · obtain ⟨⟨pcw, hgw⟩, hctw⟩ := thread_write_cta hp hX hm
          have hhc : h / L.block = g / L.block := by
            rw [← hctw (hcov.1.symm.trans hrole.1), ← hcov.2.1, hrole.2.1]
          have hr' : InRoleWord L (h / L.block) a.loc := by rw [hhc]; exact hrole
          obtain ⟨hdst, -, hcase⟩ := role_wr_info hp hX hgw hcov hr'
          rcases hcase with ⟨v', hv', hbs', -⟩ | ⟨v', hv', hbs', hc3⟩
          · left
            rw [hv] at hv'
            injection hv' with hvv
            subst hvv
            refine ⟨(h, j), pcw, rfl, ?_⟩
            rw [hgw, hdst, hbs', hhc]
          · right
            have hh := Frame.lt_of_get hX hgw
            have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hgw).1
            have hwg : (g % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
              simp [CtaBarrier.warps, hb]; omega
            have hup : ((X.tr g).take (k + 1)).countP (Execution.isBarId 1) = 1 := by
              rw [List.take_add_one, show (X.tr g)[k]? = _ from he, Option.toList_some,
                countP_snoc, h1]
              simp [Execution.isBarId]
            exact .direct (.inl (bar1_handoff hp hX g h k j ⟨⟨hg, hh, hhc.symm⟩, hwg, trivial⟩
              hjl (by simp only; rw [hup, hc3]; omega)))
        · exfalso
          obtain ⟨-, -, hfar⟩ := async_write_loc hp hX hm hcov
          rcases hfar with hfar | hfar
          · have := hrole.2.2.1; omega
          · have := hrole.2.2.2; omega)
    · apply List.ext_getElem?
      intro i
      rcases i with _ | i
      · rw [hbyte]; rfl
      · rw [List.getElem?_eq_none (by omega)]; rfl
    · rw [hl0]
      exact ⟨hrole.1, hrole.2.1, by
        simp only [roleAcc, Proof.EvD.wordAcc]
        rw [Nat.mod_eq_of_lt (by omega)]; exact hrole.2.2.1, by
        simp only [roleAcc, Proof.EvD.wordAcc]
        rw [Nat.mod_eq_of_lt (by omega)]; have := hrole.2.2.2; omega⟩
  · exact absurd h01 (by omega)

theorem epi_pred_bar2 {d d' : Proof.Epi.D} {e : Event} (h : Proof.Epi.next d e = some (some d'))
    (hs : d'.site = .bar2) : d.site = .stTab := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (rename_i hd; exact hd)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [Proof.Epi.D.stores, Proof.Epi.stNext]
       split_ifs at hs)

/-- **The CTA's thread 0 made its `stTab` store before its fourth barrier-1 arrival**, once a
thread of the CTA has passed its fourth barrier-1 event. -/
theorem stTab_exists (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j3 pc3 : Nat} (hb3 : X.IsBarrier (g, j3) 1 none pc3)
    (hpass : j3 + 1 < (X.tr g).length)
    (h3c : ((X.tr g).take j3).countP (Execution.isBarId 1) = 3) :
    ∃ jT pcT v, storeValue 32 (b32 50529027) = .ok v ∧
      X.get (g / L.block * L.block, jT) =
        some ⟨pcT, .wr (roleAcc L (g / L.block)) v.toBytes⟩ ∧
      ((X.tr (g / L.block * L.block)).take (jT + 1)).countP (Execution.isBarId 1) = 3 := by
  have hb : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg : g < L.threads := Frame.lt_of_get hX hb3
  set h0 := g / L.block * L.block with hh0
  have hh0t : h0 < L.threads := lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hh0c : h0 / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  have hh0w : h0 % L.block = 0 := Nat.mul_mod_left _ _
  have hw1 : (h0 % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
    rw [hh0w]; simp [CtaBarrier.warps, hb]
  obtain ⟨i3, pci, mi, hi3, hci⟩ := (bar1_sources hp hX).member_arrival_any hX (bar1_shape hp)
    hb3 hpass hh0c hw1 (fun hex => by
      obtain ⟨i, pc', hIs, hord⟩ := bar1Exits hp hX hb3 hpass hh0c hex
      exact ⟨i, pc', .sync, hIs, hord⟩)
  simp only at hci
  rw [h3c] at hci
  have hlen3 : i3 < (X.tr h0).length := (List.getElem?_eq_some_iff.mp hi3).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hi3 (fun f h => by cases h)
  have hC := c1_inv hp hX hh0t i3 hlen3 σ hσ
  have hS := (tm_inv hp hX hh0t i3 hlen3 σ hσ).2
  have hpc := bar1_pc hc hf rfl (by omega)
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exact (startup_bar1 st.site hpc).elim
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | dt, τ⟩
      · exfalso
        have hC' : _ = proPh d := hC
        have : proPh d ≤ 1 := by unfold proPh; split <;> omega
        omega
      · cases τ with
        | sm d =>
          exfalso
          have hC' : _ = smPh d := hC
          have : smPh d ≤ 2 := by unfold smPh; split <;> omega
          omega
        | epi d =>
          have hC' : _ = epiPh d := hC
          have hs2 : d.site = .bar2 := by
            rcases epi_bar1 d.site hpc with h' | h'
            · exfalso; rw [show epiPh d = 2 by simp [epiPh, h']] at hC'; omega
            · exact h'
          -- the step before
          obtain ⟨i2, rfl⟩ : ∃ i2, i3 = i2 + 1 := by
            rcases i3 with _ | i2
            · exfalso
              rw [Frame.stateAt_zero, thread_init_eq] at hσ
              simp at hσ
            · exact ⟨i2, rfl⟩
          have hl2 : i2 < (X.tr h0).length := by omega
          obtain ⟨e2, he2⟩ : ∃ e, (X.tr h0)[i2]? = some e := ⟨_, List.getElem?_eq_getElem hl2⟩
          have hσ' := hσ
          rw [Frame.stateAt_succ he2] at hσ'
          have hF := good_all' hp hX hh0t i2
          rcases hk2 : Frame.stateAt (thread Q L) X h0 i2 with _ | _ | σ2
          · rw [hk2] at hσ'; cases hσ'
          · exact absurd hk2 hF.1
          · rw [hk2] at hσ'
            have hn : (thread Q L h0).next σ2 e2 = some (some _) := hσ'
            obtain ⟨x2, n2⟩ := σ2
            rcases x2 with st2 | ⟨_ | r2, d2⟩
            · exfalso
              rw [next_start] at hn
              obtain ⟨s', -, hs'⟩ := mm_some hn
              cases hx : Startup.enterOf s' with
              | none => rw [enter_inl hx] at hs'; simp at hs'
              | some r =>
                cases hsel : sel L h0 r s' with
                | none =>
                  rw [Code.enter_some (i := Sum.inr r)
                    (by simp [Code.gatedExit, hx, hsel])] at hs'
                  simp at hs'
                | some ro =>
                  rw [Code.enter_some (i := Sum.inl ro)
                    (by simp [Code.gatedExit, hx, hsel])] at hs'
                  cases ro with
                  | worker w => simp at hs'
                  | dp tm1 bw1 =>
                    have h1 := congrArg (thread Q L h0).pc hs'
                    change 27 = d.site.pc at h1
                    rw [hs2] at h1
                    exact absurd h1 (by decide)
            · rename_i i2'
              obtain ⟨d2', hd2'⟩ := next_same_role hn
              have hrole := (Sigma.mk.inj (Sum.inr.inj hd2')).1
              simp only [Sum.inl.injEq] at hrole
              cases i2' with
              | worker w2 => cases hrole
              | dp tm2 bw2 =>
                cases hrole
                rcases d2 with d2 | ⟨_ | dt2, τ2⟩
                · exfalso
                  rw [next_pro] at hn
                  obtain ⟨d'', -, he''⟩ := mm_some hn
                  cases hxo : ProA.exitOf d'' with
                  | none =>
                    rw [Code.enter_none (by simp [Code.gatedExit, hxo])] at he''
                    simp at he''
                  | some v =>
                    cases hsel : ProA.selTail Q L h0 v d'' with
                    | some dt' =>
                      rw [Code.enter_some (i := Sum.inl dt')
                        (by simp [Code.gatedExit, hxo, hsel])] at he''
                      simp at he''
                    | none =>
                      rw [Code.enter_some (i := Sum.inr ())
                        (by simp [Code.gatedExit, hxo, hsel])] at he''
                      simp at he''
                · rw [next_tail] at hn
                  obtain ⟨τ', hτ, he''⟩ := mm_some hn
                  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
                    true_and] at he''
                  obtain ⟨he1, -⟩ := he''
                  cases τ2 with
                  | sm ds =>
                    exfalso
                    simp only [Tail.next] at hτ
                    split at hτ
                    · simp only [Tail.exitNext] at hτ
                      split at hτ
                      · simp only [Option.some.injEq] at hτ
                        subst hτ
                        simp only [Sum.inl.injEq, Tail.St.epi.injEq] at he1
                        rw [← he1.2] at hs2
                        simp [Proof.Epi.D.entry] at hs2
                      · cases hτ
                    · obtain ⟨_, -, rfl⟩ := mm_some hτ
                      simp at he1
                  | epi de =>
                    simp only [Tail.next] at hτ
                    obtain ⟨d3, hd3, rfl⟩ := mm_some hτ
                    simp only [Sum.inl.injEq, Tail.St.epi.injEq] at he1
                    obtain ⟨-, he1⟩ := he1
                    subst he1
                    have hsT := epi_pred_bar2 hd3 hs2
                    have hJ2 := hF.2 _ hk2
                    obtain ⟨t2, ins2, o2, hat2, hi2, hc2, hf2⟩ :=
                      Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := i2) he2 hk2
                    cases o2 with
                    | none =>
                      exfalso
                      have hE := fires_none_ends hf2
                      obtain ⟨r2, hr2⟩ := hX.thr h0 hh0t
                      have := Flow.Run.end_last hr2 he2 hE
                      omega
                    | some u2 =>
                      have hev2 := frag_ev hp hh0t hJ2 hat2 hi2 hc2 hf2
                      have h' : Proof.Epi.Shape L h0 de e2 := hev2
                      simp only [Proof.Epi.Shape, hsT] at h'
                      obtain ⟨v, hv, rfl⟩ := h'
                      refine ⟨i2, _, v, hv, by rw [show X.get (h0, i2) = _ from he2, hh0c], ?_⟩
                      have hC2 := c1_inv hp hX hh0t i2 hl2 _ hk2
                      have hC2' : _ = epiPh de := hC2
                      rw [List.take_add_one, he2, Option.toList_some, countP_snoc, hC2',
                        show epiPh de = 3 by simp [epiPh, hsT]]
                      simp [Execution.isBarId]
                · exact (hF.2 _ hk2).elim
            · exact (hF.2 _ hk2).elim
      · exact hJ.elim
    | worker w =>
      exfalso
      have : 4 ≤ h0 % L.block / 32 := hS
      omega
  · exact hJ.elim

theorem role_readN (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    {w : Value} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker w), .worker ⟨.ldRole, P⟩⟩, n)))
    (h4 : 4 ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) :
    ∃ v, storeValue 32 (b32 50529027) = .ok v ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 213332 + g % L.block / 32⟩ ∧
      bs = [wbyte (roleAcc L (g / L.block)) v.toBytes a.loc] := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- the read's footprint
  have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
  have hw8 : g % L.block / 32 < 8 := by
    have := Nat.mod_lt g (show 0 < L.block by omega)
    omega
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u => exact ⟨u, rfl⟩
  have hF : (Proof.WComp.code L g Q).toMachine.Fired (some (.worker ⟨.ldRole, P⟩))
      ⟨pc, .rd a bs⟩ (some u) := by
    refine ⟨t, ⟨hat, hi⟩, ?_⟩
    have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.worker ⟨.ldRole, P⟩)]? = some ins := hc
    show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.worker ⟨.ldRole, P⟩)) t) _ (some u)
    simp only [Code.tmpl]
    rw [hc', hat.1]
    exact hf
  obtain ⟨ac, bs', he', hl, hz⟩ := Proof.Worker.shape_ldRole hp
    (by rw [hb]; exact Nat.mod_lt _ (by omega)) rfl hF
  simp only [Event.mk.injEq, Kind.rd.injEq] at he'
  obtain ⟨-, rfl, rfl⟩ := he'
  have hwo : Proof.Worker.warpOf L g = g % L.block / 32 := rfl
  rw [hwo] at hl
  -- the reader's first barrier-1 event
  obtain ⟨j0, ev0, hj0, hb0e, hc0⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 1)
    (show 3 + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) by omega)
  have hj0k : j0 < k := by
    have := (List.getElem?_eq_some_iff.mp hj0).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hj0k.le] at hc0
  have hget0 : X.get (g, j0) = some ev0 := by
    change (X.tr g)[j0]? = some ev0
    rw [← hj0, List.getElem?_take, ite_eq_left hj0k]
  obtain ⟨pc0, k0⟩ := ev0
  obtain ⟨cnt0, md0, hk0⟩ := isBarId1_kind hb0e
  simp only at hk0
  subst hk0
  obtain ⟨hmd, hcnt⟩ := bar_event_static hX (by omega) hget0
  rcases hcnt with ⟨hcn, -⟩ | ⟨h01, -⟩
  · subst hmd hcn
    obtain ⟨j8, pc8, v, hv, hget8, hc8⟩ := stTab_exists hp hX hget0 (by omega) hc0
    refine ⟨v, hv, hl, ?_⟩
    -- the store is before the read
    have hg0t : g / L.block * L.block < L.threads :=
      lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
    have hcta0 : g / L.block * L.block / L.block = g / L.block :=
      Nat.mul_div_cancel _ (by omega)
    have hw0 : ((g / L.block * L.block) % L.block) / 32 ∈
        Finset.range (CtaBarrier.warps L.block) := by
      rw [Nat.mul_mod_left]; simp [CtaBarrier.warps, hb]
    have hbc8 : baseCausality L X (g / L.block * L.block, j8) (g, k) :=
      bar1_handoff hp hX _ _ j8 k ⟨⟨hg0t, hg, hcta0⟩, hw0, trivial⟩ hlen
        (by simp only; rw [hc8]; omega)
    -- the read of the one byte
    have hrd : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
    have hac : a.size = 1 := hz
    have hbl : bs.length = 1 := by rw [← hac]; exact (hX.rf _ _ _ hrd).1
    have hl0 : a.loc.at 0 = a.loc := by simp [Loc.at]
    have hrole : InRoleWord L (g / L.block) a.loc := by
      rw [hl]; exact ⟨rfl, rfl, by simp only; omega, by simp only; omega⟩
    have hbyte := read_byte_of_writers_hidden hX hrd (k := 0) (by omega)
      (fun ref => ∃ i pc', ref = .thread i ∧
        X.get i = some ⟨pc', .wr (roleAcc L (g / L.block)) v.toBytes⟩)
      (wbyte (roleAcc L (g / L.block)) v.toBytes a.loc)
      (w0 := .thread (g / L.block * L.block, j8)) (Or.inl ⟨pc8, hget8⟩) ?_ (.direct (.inl hbc8))
      (fun w dst written hW hm hcov => by
        obtain ⟨i, pc', rfl, hgi⟩ := hW
        rcases hm with ⟨pcm, hm⟩ | ⟨old, pcm, hm⟩
        · rw [hgi] at hm
          simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hm
          obtain ⟨-, rfl, rfl⟩ := hm
          rw [hl0]
        · rw [hgi] at hm; simp at hm)
      (fun w' dst' bytes hm hcov => by
        rw [hl0] at hcov
        rcases w' with ⟨h, j⟩ | ⟨i, p⟩
        · obtain ⟨⟨pcw, hgw⟩, hctw⟩ := thread_write_cta hp hX hm
          have hhc : h / L.block = g / L.block := by
            rw [← hctw (hcov.1.symm.trans hrole.1), ← hcov.2.1, hrole.2.1]
          have hr' : InRoleWord L (h / L.block) a.loc := by rw [hhc]; exact hrole
          obtain ⟨hdst, -, hcase⟩ := role_wr_info hp hX hgw hcov hr'
          rcases hcase with ⟨v', hv', hbs', hc0'⟩ | ⟨v', hv', hbs', -⟩
          · right; left
            have hh := Frame.lt_of_get hX hgw
            have hjl0 : j8 < (X.tr (g / L.block * L.block)).length :=
              (List.getElem?_eq_some_iff.mp hget8).1
            have hwh : (h % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
              have := Nat.mod_lt h (show 0 < L.block by omega)
              simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
              omega
            have hup : ((X.tr h).take (j + 1)).countP (Execution.isBarId 1) = 0 := by
              rw [List.take_add_one, show (X.tr h)[j]? = _ from hgw, Option.toList_some,
                countP_snoc, hc0']
              simp [Execution.isBarId]
            have hc8' : ((X.tr (g / L.block * L.block)).take j8).countP
                (Execution.isBarId 1) = 3 := by
              have := hc8
              rw [List.take_add_one, show (X.tr (g / L.block * L.block))[j8]? = _ from hget8,
                Option.toList_some, countP_snoc] at this
              simpa [Execution.isBarId] using this
            exact .direct (.inl (bar1_handoff hp hX h (g / L.block * L.block) j j8
              ⟨⟨hh, hg0t, by rw [hcta0, hhc]⟩, hwh, trivial⟩ hjl0
              (by simp only; rw [hup, hc8']; omega)))
          · left
            rw [hv] at hv'
            injection hv' with hvv
            subst hvv
            refine ⟨(h, j), pcw, rfl, ?_⟩
            rw [hgw, hdst, hbs', hhc]
        · exfalso
          obtain ⟨-, -, hfar⟩ := async_write_loc hp hX hm hcov
          rcases hfar with hfar | hfar
          · have := hrole.2.2.1; omega
          · have := hrole.2.2.2; omega)
    · apply List.ext_getElem?
      intro i
      rcases i with _ | i
      · rw [hbyte]; rfl
      · rw [List.getElem?_eq_none (by omega)]; rfl
    · rw [hl0]
      exact ⟨hrole.1, hrole.2.1, by
        simp only [roleAcc, Proof.EvD.wordAcc]
        rw [Nat.mod_eq_of_lt (by omega)]; exact hrole.2.2.1, by
        simp only [roleAcc, Proof.EvD.wordAcc]
        rw [Nat.mod_eq_of_lt (by omega)]; have := hrole.2.2.2; omega⟩
  · exact absurd h01 (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof2
