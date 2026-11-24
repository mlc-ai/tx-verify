-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.LdElect
public import Kernels.InklingRelDecode.Proof.Thread.WpSites

@[expose] public section

/-! # Two lanes' polls at one position are ordered (`PollSynced`)

ERR-NONUNIFORM-GUARD asks, of two lanes of a warp polling at one position before a poll branch,
an order between them unless they poll one object at a branch an assumption selects. Every poll
branch is selected by `pollAgree` (`Wp.pollPcs_sel`), so only polls of different objects need an
order. The polls (`poll_cls`) are the softmax region's `s_ready` and `o_done` polls, the
epilogue's `o_final` poll, the loader's `kv_empty` poll and the MMA warp's `kv_ready` and `p_ready`
polls; the `o_done` and `o_final` polls name one object per CTA. At the others the object is a
function of the CTA and the iteration, so two polls of different objects are in different
iterations, and the lane in the earlier iteration has made fewer collectives:

* the softmax region: `1 + num_pre + smBase i` shuffles at `waitS` (`PSH`); a lane does not exit
  before its next shuffle (its exit has `1 + num_pre + smBase num_iters`, `dp_exit_smIt`);
* the loader: `4 (i - num_pre)` elections at `wait` (`EL`);
* the MMA warp: `1 + mmSh` shuffles (`SH`); its exit has `1 + 2 num_iters`.

`meet_shfl`/`meet_elect` order the polls; `poll_synced`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The elections of the kernel use the full mask. -/
theorem elect_full (hX : Consistent L kernel Assumptions.all m X) {e : EvId} {pc mask inst l : Nat}
    (h : X.Elect e pc mask inst l) : mask = 4294967295 := by
  obtain ⟨g, k⟩ := e
  have hmem : (⟨pc, .elect mask inst l⟩ : Event) ∈ X.tr g := List.mem_of_getElem? h
  exact Proof.Interface.electMask_full hX g _ hmem mask inst l rfl

theorem elect_ordinal (hX : Consistent L kernel Assumptions.all m X) : ElectOrdinal L X :=
  electOrdinal hX (ElectMutual.of_full (fun h => elect_full hX h))

/-! ### The polls -/

/-- **A poll**, by the state that fires it: its object, as a function of the CTA and the
iteration, and its position. -/
theorem poll_cls (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc p : Nat} {mo : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait mo p ok acq sc⟩) :
    (∃ tm bw dt d n, Frame.stateAt (thread Q L) X g k =
        some (some (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, n)) ∧
      d.site = .waitS ∧ pc = Proof.Sm.Site.waitS.pc ∧
      mo = (Proof.EvD.sReadyOf d.i).loc L (g / L.block)) ∨
    (pc = Proof.Sm.Site.waitO.pc ∧ mo = Proof.EvD.Bar.oDone.loc L (g / L.block)) ∨
    (pc = Proof.Epi.Site.wait.pc ∧ mo = Proof.EvD.Bar.oFinal.loc L (g / L.block)) ∨
    (∃ tm d P n, Frame.stateAt (thread Q L) X g k =
        some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)) ∧
      d.site = .wait ∧ pc = Proof.Loader.Site.wait.pc ∧
      mo = Proof.EvW.kvEmpty L (g / L.block) (d.i % 3)) ∨
    (∃ tm d P n, Frame.stateAt (thread Q L) X g k =
        some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)) ∧
      ((d.site = .kvWait ∧ pc = Proof.Mma.Site.kvWait.pc ∧
          mo = Proof.EvW.kvReady L (g / L.block) (d.i % 3)) ∨
        (d.site = .pWait ∧ pc = Proof.Mma.Site.pWait.pc ∧
          mo = Proof.EvW.pReady L (g / L.block) ((d.i - 1) % 2)))) := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hpcf := fires_pc hf
  simp only at hpcf
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := wait_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r', d⟩
    · exact (startup_wait st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact (proA_wait d.site hpc).elim
        · cases τ with
          | sm d =>
            rcases sm_wait d.site hpc with hs | hs
            · have h' : Proof.Sm.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
              simp only [Proof.Sm.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨ok', -, rfl, -⟩ := h'
              refine .inl ⟨tm, bw, _, d, n, hσ, hs, ?_, rfl⟩
              exact hpcf.trans (by show d.site.pc = _; rw [hs])
            · obtain ⟨ok', h'⟩ := Proof.Sm.shape_waitO (Proof.ProA.sharedOk_of_pre hp)
                (sm_fired hat hi hc hf) hs
              simp only [Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨-, rfl, -⟩ := h'
              refine .inr (.inl ⟨?_, rfl⟩)
              exact hpcf.trans (by show d.site.pc = _; rw [hs])
          | epi d =>
            have hs := epi_wait d.site hpc
            have h' : Proof.Epi.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
            simp only [Proof.Epi.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
            obtain ⟨ok', -, rfl, -⟩ := h'
            have hM : Proof.Epi.Means Q L g d.pr := tm_means hp hX hg k hlen _ hσ
            have hmb := hM.mb
            simp only [Proof.EvD.Bar.off] at hmb
            rw [Nat.mod_eq_of_lt (by omega)] at hmb
            refine .inr (.inr (.inl ⟨?_, ?_⟩))
            · exact hpcf.trans (by show d.site.pc = _; rw [hs])
            · simp only [Proof.EvD.Bar.loc, Proof.EvD.Bar.off]
              rw [hmb]
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_wait d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          simp only [Proof.EvW.LdShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh
          obtain ⟨ok', -, rfl, -⟩ := hsh
          refine .inr (.inr (.inr (.inl ⟨w, d, P, n, hσ, hs, ?_, rfl⟩)))
          exact hpcf.trans (by show d.site.pc = _; rw [hs])
        | mma d P =>
          have hsh : Proof.EvW.MmShape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
          refine .inr (.inr (.inr (.inr ⟨w, d, P, n, hσ, ?_⟩)))
          rcases mma_wait d.site hpc with hs | hs <;>
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh <;>
            obtain ⟨ok', -, rfl, -⟩ := hsh
          · exact .inl ⟨hs, by exact hpcf.trans (by show d.site.pc = _; rw [hs]), rfl⟩
          · exact .inr ⟨hs, by exact hpcf.trans (by show d.site.pc = _; rw [hs]), rfl⟩
        | worker w => exact (worker_wait w.site hpc).elim
        | idle d => exact (idle_wait d.site hpc).elim
        | exit x => exact (exitsite_wait x.site hpc).elim
    · exact hJ.elim

/-! ### The exits -/

/-- **A thread of warps 0 to 3 exits after the softmax region's shuffles.** -/
theorem dp_exit_smIt (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} (hE : X.get (h, j) = some ⟨pc, .exit⟩) (hw : h % L.block < 128) :
    1 + npOf Q L h + Proof.Sm.smBase (smIt Q L h) ≤
      ((X.tr h).take j).countP Execution.isShfl := by
  have hh := Frame.lt_of_get hX hE
  have hlen : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hE).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hE (fun f h => by cases h)
  have hpc := ret_pc' hc hf rfl
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hm := startup_special st.site (List.mem_append_right _ hpc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h' | h' | h' <;>
      rw [show (thread Q L h).pc _ = st.site.pc from rfl, h'] at hpc <;>
      simp [retPcs, Startup.Site.pc] at hpc
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
      · cases τ with
        | sm d => exact absurd (sm_special d.site (List.mem_append_right _ hpc)) (by simp)
        | epi d => exact psh_inv hp hX hh j hlen _ hσ
      · exact hJ.elim
    | worker w =>
      have : 4 ≤ h % L.block / 32 := (tm_inv hp hX hh j hlen _ hσ).2
      omega
  · exact hJ.elim

theorem smBase_lt {i j : Nat} (h : i < j) : Proof.Sm.smBase i < Proof.Sm.smBase j := by
  unfold Proof.Sm.smBase
  split <;> split <;> omega

/-! ### Two lanes in different iterations -/

/-- **The softmax region's `s_ready` polls of two lanes in different iterations are ordered.** -/
theorem meet_sm (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h k k' : Nat}
    {e : Event} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : Execution.isShfl e = false) {tm tm' : Nat} {bw bw' : Value} {dt dt' : Proof.ProA.Dat}
    {d d' : Proof.Sm.D} {n n' : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, n)))
    (hσ' : Frame.stateAt (thread Q L) X h k' =
      some (some (.inr ⟨.inl (.dp tm' bw'), .inr ⟨.inl dt', .sm d'⟩⟩, n')))
    (hs : d.site = .waitS) (hs' : d'.site = .waitS) (hk' : k' < (X.tr h).length)
    (hlt : d.i < d'.i) : PollBefore L kernel X (g, k) (h, k') := by
  have hg := hw.1.1
  have hh := hw.1.2.1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hcta : h / L.block = g / L.block := hw.1.2.2.symm
  have hnp : npOf Q L h = npOf Q L g := npOf_cta' hcta
  obtain ⟨h1, -⟩ : _ ∧ _ := psh_inv hp hX hg k hk _ hσ
  obtain ⟨h2, -⟩ : _ ∧ _ := psh_inv hp hX hh k' hk' _ hσ'
  simp only [Proof.Sm.smW, Proof.Sm.smOff, hs, hs'] at h1 h2
  have h3 := smBase_lt hlt
  refine meet_shfl hX (elect_ordinal hX) hw he hne h1 (by rw [h2, hnp]; omega) hk' ?_
  -- the lane does not exit before its next shuffle
  rintro ⟨j, pc, hE, hle⟩
  have hdp : g % L.block < 128 := dp_lane k hσ
  have hx := dp_exit_smIt hp hX hE hdp
  obtain ⟨t, ins, o, hat, hi, -, -⟩ := Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have hI : Proof.Sm.Inv L g d := hi
  obtain ⟨-, -, hSR⟩ := ((good_all' hp hX hg k).2 _ hσ : TailRef Q L g tm (.sm d) n)
  have hlt' : d.i < smIt Q L g := by
    rw [← r26_smIt hI hSR]
    exact (hI.late (by rw [hs]; trivial)).2.2
  have := smBase_lt hlt'
  omega

/-- **The loader's `kv_empty` polls of two lanes in different iterations are ordered.** -/
theorem meet_ld (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h k k' : Nat}
    {e : Event} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : isElectEv e = false) {tm tm' : Value} {d d' : Proof.Loader.D}
    {P P' : Proof.Loader.Pro} {n n' : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)))
    (hσ' : Frame.stateAt (thread Q L) X h k' =
      some (some (.inr ⟨.inl (.worker tm'), .loader d' P'⟩, n')))
    (hs : d.site = .wait) (hs' : d'.site = .wait) (hk' : k' < (X.tr h).length)
    (hlt : d.i < d'.i) : PollBefore L kernel X (g, k) (h, k') := by
  have hg := hw.1.1
  have hh := hw.1.2.1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hcta : h / L.block = g / L.block := hw.1.2.2.symm
  have hnp : npOf Q L h = npOf Q L g := npOf_cta' hcta
  have hin : d.site.inLoop = true := by rw [hs]; rfl
  have hin' : d'.site.inLoop = true := by rw [hs']; rfl
  have h1 := (el_inv hp hX hg k hk _ hσ : LE Q L g d _).loop hin
  have h2 := (el_inv hp hX hh k' hk' _ hσ' : LE Q L h d' _).loop hin'
  have hlo := (kc_inv hp hX hg k hk _ hσ : LdCnt Q L g d _).lo hin
  simp only [hs, hs', elDoneS] at h1 h2
  exact meet_elect hX (elect_ordinal hX) hw he hne h1
    (by show _ ≤ electN _; rw [h2, hnp]; omega) hk'
    (fun h => elect_full hX h)

/-- An MMA lane does not exit before its broadcast of a half. -/
theorem mma_noExit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hk : k < (X.tr g).length) {tm : Value} {d : Proof.Mma.D} {P : Proof.Loader.Pro}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)))
    (hs : d.site = .kvWait ∨ d.site = .pWait) :
    ¬ ShflExited X g (1 + mmSh d) := by
  have hb : L.block = 256 := hp.block
  have hg := thread_lt_of_len hX hk
  have hw7 : g % L.block / 32 = 7 := role_warp hp hX hg k hk _ hσ
  obtain ⟨-, hL, hN⟩ := (sh_inv hp hX hg k hk _ hσ : _ = 1 + mmSh d ∧ MmLoop d ∧ _)
  have hdn : d.n = nIt Q L g := by apply hN <;> rcases hs with h | h <;> rw [h] <;> nofun
  rintro ⟨j, pc, hE, hle⟩
  have hw4 : 4 ≤ g % L.block / 32 := by omega
  obtain ⟨tm', P', n', hσx⟩ := worker_exit hp hX hE hw4
  have hlx : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hE).1
  have hSx : _ = 1 + sh7 Q L g := sh_inv hp hX hg j hlx _ hσx
  simp only [sh7, hw7, ite_true] at hSx
  rcases hs with h | h <;> simp only [MmLoop, mmSh, h] at hL hle ⊢ <;> rw [← hdn] at hSx <;>
    simp only [nRun] at hSx <;> split_ifs at hSx <;> omega

/-- `mmSh` grows with the iteration at a poll site. -/
theorem mmSh_lt {d d' : Proof.Mma.D} (hL : MmLoop d) (hL' : MmLoop d') (hn : d.n = d'.n)
    (h : (d.site = .kvWait ∧ d'.site = .kvWait) ∨ (d.site = .pWait ∧ d'.site = .pWait))
    (hlt : d.i < d'.i) : mmSh d < mmSh d' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [MmLoop, mmSh, h1, h2] at hL hL' ⊢ <;> omega

/-- **The MMA warp's polls of two lanes in different iterations are ordered.** -/
theorem meet_mma (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h k k' : Nat}
    {e : Event} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : Execution.isShfl e = false) {tm tm' : Value} {d d' : Proof.Mma.D}
    {P P' : Proof.Loader.Pro} {n n' : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)))
    (hσ' : Frame.stateAt (thread Q L) X h k' =
      some (some (.inr ⟨.inl (.worker tm'), .mma d' P'⟩, n')))
    (hs : (d.site = .kvWait ∧ d'.site = .kvWait) ∨ (d.site = .pWait ∧ d'.site = .pWait))
    (hk' : k' < (X.tr h).length) (hlt : d.i < d'.i) : PollBefore L kernel X (g, k) (h, k') := by
  have hg := hw.1.1
  have hh := hw.1.2.1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hcta : h / L.block = g / L.block := hw.1.2.2.symm
  obtain ⟨h1, hL, hN⟩ := (sh_inv hp hX hg k hk _ hσ : _ = 1 + mmSh d ∧ MmLoop d ∧ _)
  obtain ⟨h2, hL', hN'⟩ := (sh_inv hp hX hh k' hk' _ hσ' : _ = 1 + mmSh d' ∧ MmLoop d' ∧ _)
  have hs1 : d.site ≠ .setMaxReg ∧ d.site ≠ .ldNum := by
    rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> exact ⟨nofun, nofun⟩
  have hs2 : d'.site ≠ .setMaxReg ∧ d'.site ≠ .ldNum := by
    rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨nofun, nofun⟩
  have hn : d.n = d'.n := by
    rw [hN hs1.1 hs1.2, hN' hs2.1 hs2.2]
    simp only [nIt, Proof.ProA.cta, hcta]
  have h3 := mmSh_lt hL hL' hn hs hlt
  exact meet_shfl hX (elect_ordinal hX) hw he hne h1 (by rw [h2]; omega) hk'
    (mma_noExit hp hX hk hσ (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]))

/-! ### `PollSynced` -/

/-- **Two lanes' polls of one position are ordered**, unless they poll one object at a branch
`pollAgree` selects. -/
theorem poll_synced (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    PollSynced L kernel Assumptions.all X := by
  intro g h k k' pc mo mo' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hpb hd
  have hk' : k' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  have hcta : g / L.block = h / L.block := hw.1.2.2
  obtain ⟨σ, t, ins, o, -, -, -, -, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hpc := wait_pc hc hf rfl
  have hpcf := fires_pc hf
  simp only at hpcf
  have hsel : Assumptions.all.any (·.uniPoll (pc + 1)) = true := by
    apply Proof.Wp.pollPcs_sel
    rw [hpcf]
    simp only [waitPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with h | h | h | h | h | h <;> rw [h] <;> decide
  have hne : mo ≠ mo' := by
    rcases hd with hd | hd
    · exact hd
    · rw [hsel] at hd; cases hd
  have hnS : Execution.isShfl ⟨pc, .wait mo p ok acq sc⟩ = false := rfl
  have hnE : isElectEv ⟨pc, .wait mo p ok acq sc⟩ = false := rfl
  rcases poll_cls hp hX he with
    ⟨tm, bw, dt, d, n, hσ, hs, hp1, rfl⟩ | ⟨hp1, rfl⟩ | ⟨hp1, rfl⟩ |
      ⟨tm, d, P, n, hσ, hs, hp1, rfl⟩ | ⟨tm, d, P, n, hσ, ⟨hs, hp1, rfl⟩ | ⟨hs, hp1, rfl⟩⟩ <;>
    rcases poll_cls hp hX he' with
      ⟨tm', bw', dt', d', n', hσ', hs', hp2, rfl⟩ | ⟨hp2, rfl⟩ | ⟨hp2, rfl⟩ |
        ⟨tm', d', P', n', hσ', hs', hp2, rfl⟩ |
        ⟨tm', d', P', n', hσ', ⟨hs', hp2, rfl⟩ | ⟨hs', hp2, rfl⟩⟩ <;>
    (try (exfalso; rw [hp1] at hp2; revert hp2; decide)) <;>
    (try (exfalso; apply hne; rw [hcta]; done))
  · -- `s_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (meet_sm hp hX hw he hnS hσ hσ' hs hs' hk' hlt)
    · exact absurd (by rw [hcta, Proof.EvD.sReadyOf, Proof.EvD.sReadyOf, heq]) hne
    · exact .inr (meet_sm hp hX hw.symm he' rfl hσ' hσ hs' hs
        (List.getElem?_eq_some_iff.mp he).1 hgt)
  · -- `kv_empty`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (meet_ld hp hX hw he hnE hσ hσ' hs hs' hk' hlt)
    · exact absurd (by rw [hcta, heq]) hne
    · exact .inr (meet_ld hp hX hw.symm he' rfl hσ' hσ hs' hs
        (List.getElem?_eq_some_iff.mp he).1 hgt)
  · -- `kv_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (meet_mma hp hX hw he hnS hσ hσ' (.inl ⟨hs, hs'⟩) hk' hlt)
    · exact absurd (by rw [hcta, heq]) hne
    · exact .inr (meet_mma hp hX hw.symm he' rfl hσ' hσ (.inl ⟨hs', hs⟩)
        (List.getElem?_eq_some_iff.mp he).1 hgt)
  · -- `p_ready`
    rcases Nat.lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (meet_mma hp hX hw he hnS hσ hσ' (.inr ⟨hs, hs'⟩) hk' hlt)
    · exact absurd (by rw [hcta, heq]) hne
    · exact .inr (meet_mma hp hX hw.symm he' rfl hσ' hσ (.inr ⟨hs', hs⟩)
        (List.getElem?_eq_some_iff.mp he).1 hgt)

end
end PTX.Kernels.InklingRelDecode.Proof2
