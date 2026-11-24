-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Global
public import Kernels.InklingRelDecode.Proof2.Lib.EpiMeans

@[expose] public section

/-! # The global writes on the role table

* `tm_means`: along a thread the softmax states' entry numbers carry the launch's `num_tokens` and
  output bases (`SmEntry.entOf_params` at the hand-off), and the epilogue's registers mean what
  `Epi.Means` says (`Interface.exitIn_means` at the bridge, kept by every epilogue step).
* `global_wr`: a thread's write outside shared memory is an epilogue store of `OPart` or
  `LsePart`, inside its array (`Epi.shape_stO_loc`, `shape_stLse_loc`, `Epi.row_coords`,
  `oLoc_range`, `lseLoc_range`).
* `global_placed : Safety.GlobalPlaced Q X`: reads by `global_reads`, thread writes by
  `global_wr`, a tensor copy's writes are shared (`copy_ring`, `copy_foot`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Safety (InInput InOut GlobalPlaced)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The epilogue's numbers -/

/-- The softmax states' launch words and the epilogue states' meaning. -/
def TM (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _) =>
    d.e.ntok = Q.nTok % 2 ^ 32 ∧ d.e.rd75 = Q.oBase % 2 ^ 64 ∧ d.e.rd76 = Q.lseBase % 2 ^ 64
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) => Proof.Epi.Means Q L g d.pr
  | _ => True

/-- **The epilogue's numbers along a thread.** -/
theorem tm_means (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      TM Q L g σ := by
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
      · -- the startup enters no fragment state of the default partition's tail
        rw [next_start] at hn
        obtain ⟨s', -, hs'⟩ := mm_some hn
        cases hxo : Startup.enterOf s' with
        | none => rw [enter_inl hxo] at hs'; subst hs'; trivial
        | some r =>
          cases hsel : sel L g r s' with
          | none =>
            rw [Code.enter_some (i := Sum.inr r) (by simp [Code.gatedExit, hxo, hsel])] at hs'
            subst hs'; trivial
          | some ro =>
            rw [Code.enter_some (i := Sum.inl ro) (by simp [Code.gatedExit, hxo, hsel])] at hs'
            cases ro with
            | worker w => subst hs'; trivial
            | dp tm1 bw1 =>
              obtain ⟨x', n'⟩ := σ'
              simp only [Prod.mk.injEq] at hs'
              obtain ⟨hs', -⟩ := hs'
              rw [← hs']
              trivial
      · rename_i i
        obtain ⟨d2, hd2⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd2
        subst hd2
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases dd with d | ⟨_ | _, τ⟩
          · -- the prologue's exit enters the softmax region
            obtain ⟨-, -, hP, -⟩ := (hJ : ProRef Q L g tm bw d n)
            rw [next_pro] at hn
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
                have hG : TailGate Q L g dt' := by
                  simp only [ProA.selTail] at hsel
                  split at hsel
                  · obtain rfl := Option.some.inj hsel; assumption
                  · cases hsel
                obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
                  Frame.fired_site (fun g hg => thread_sound hp hg) hX hget hk0
                have hargs : Proof.ProA.ArgsOk L g dt'.pro := by
                  rw [hG.1]; exact Startup.argsOk_inh hp hg hi.1.args.tid 0
                obtain ⟨-, -, hntok, -, hrd75, hrd76⟩ := Proof.SmEntry.entOf_params hp hargs
                exact ⟨hntok, hrd75, hrd76⟩
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
              trivial
          · rw [next_tail] at hn
            obtain ⟨τ', hτ, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
              true_and] at he''
            rw [← he''.1]
            cases τ with
            | sm d =>
              obtain ⟨-, -, hS⟩ := (hJ : TailRef Q L g tm (.sm d) n)
              have hW : _ ∧ _ ∧ _ := hR0
              simp only [Tail.next] at hτ
              split at hτ
              · unfold Tail.exitNext at hτ
                split at hτ
                · simp only [Option.some.injEq] at hτ
                  subst hτ
                  exact Proof.Interface.exitIn_means hp hg ⟨hS, hW.1, hW.2.1, hW.2.2⟩
                · cases hτ
              · obtain ⟨d', hd', rfl⟩ := mm_some hτ
                show d'.e.ntok = _ ∧ d'.e.rd75 = _ ∧ d'.e.rd76 = _
                rw [sm_next_e hd']
                exact hW
            | epi d =>
              have hW : Proof.Epi.Means Q L g d.pr := hR0
              simp only [Tail.next] at hτ
              obtain ⟨d', hd', rfl⟩ := mm_some hτ
              show Proof.Epi.Means Q L g d'.pr
              rw [Proof.Epi.next_pr hd']
              exact hW.bw _
          · exact hJ.elim
      · exact hJ.elim


/-! ### The writes outside shared memory -/

/-- The positions of the stores that may write outside shared memory. -/
def wPcs : List Nat :=
  [Proof.Epi.Site.stLse.pc, Proof.Epi.Site.stTab.pc, Proof.ProA.Site.st8.pc,
    Proof.ProA.Site.st9_0.pc, Proof.ProA.Site.st9_1.pc] ++ (List.range 64).map Proof.Epi.stPc

/-- Instructions that store to a space other than shared memory, or through a dynamic
address. -/
def gstoreOp (op : Op) : Bool :=
  (storeSpace op != none && storeSpace op != some .shared) || (dynamicAccess op && writeOp op)

theorem kernel_gstore_pcs : OpPcsFast kernel.code gstoreOp wPcs = true := by decide +kernel

theorem gstore_pc {t : TState} {ins : Instr} {pc : Nat} {e : Event} {o : Option TState} {a : Acc}
    {bs : List Byte} (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .wr a bs)
    (hsp : a.loc.space ≠ .shared) : pc ∈ wPcs := by
  refine OpPcsFast.mem kernel_gstore_pcs hc ?_
  have hw := fires_write_op hf hk
  rcases fires_write_space hf hk with h | h
  · simp [gstoreOp, h, hsp]
  · simp [gstoreOp, h, hw]

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_gw : ∀ s : Startup.Site, s.pc ∈ wPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem pro_gw (s : ProA.Site) (h : s.pc ∈ wPcs) : s = .st8 ∨ ∃ j, s = .st9 j := by
  revert h
  cases s with
  | st8 => intro _; exact .inl rfl
  | st9 j => intro _; exact .inr ⟨j, rfl⟩
  | ld k | el k | init k | arr k | psh k | ldq k =>
    intro h; exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    intro h; exfalso; revert h; revert j; revert b; decide
  | _ => intro h; exfalso; revert h; decide

theorem sm_gw : ∀ s : Proof.Sm.Site, s.pc ∈ wPcs → False := by site_none
theorem epi_gw (s : Proof.Epi.Site) (h : s.pc ∈ wPcs) :
    s = .stLse ∨ s = .stTab ∨ ∃ j, s = .stO j := by
  revert h
  cases s
  all_goals first
    | (intro _; exact .inl rfl)
    | (intro _; exact .inr (.inl rfl))
    | (intro _; exact .inr (.inr ⟨_, rfl⟩))
    | (intro h; exfalso; revert h; decide +kernel)
theorem worker_gw : ∀ s : Proof.Worker.Site, s.pc ∈ wPcs → False := by site_none
theorem idle_gw : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ wPcs → False := by site_none
theorem loader_gw : ∀ s : Proof.Loader.Site, s.pc ∈ wPcs → False := by site_none
theorem mma_gw : ∀ s : Proof.Mma.Site, s.pc ∈ wPcs → False := by site_none
theorem exitsite_gw : ∀ s : Proof.WComp.ExitSite, s.pc ∈ wPcs → False := by site_none

/-- **A thread's write outside shared memory is an output store inside its array.** -/
theorem global_wr (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hsp : a.loc.space ≠ .shared) {l : Loc} (hc : a.Covers l) : InOut Q l := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc', hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hpc := gstore_pc hc' hf rfl hsp
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_gw st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exfalso
          have hx : d.site ≠ .exit := fun h => by
            have := hi.2; simp [Code.gatedExit, ProA.exitOf, h] at this
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc' hf
          rcases pro_gw d.site hpc with hs | ⟨j, hs⟩
          · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st8 hF (by simp [ProA.D.old, hs, ProA.Site.old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, -⟩ := he'
            exact hsp rfl
          · obtain ⟨pc', he'⟩ := st9_event hp hX he (by simp [Ends]) hσ hs
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, -⟩ := he'
            fin_cases j <;> exact hsp rfl
        · cases τ with
          | sm d => exact (sm_gw d.site hpc).elim
          | epi d =>
            have hm : Proof.Epi.Means Q L g d.pr := tm_means hp hX hg k hlen _ hσ
            have hFe := epi_fired hat hi.1 hc' hf
            have hI : Proof.Epi.Inv d := hi.1
            obtain ⟨hs1, hc1, h1, h2⟩ := hc
            rcases epi_gw d.site hpc with hs | hs | ⟨j, hs⟩
            · have hrv : d.pr.rv = true := hI.rv (by rw [hs]; trivial)
              obtain ⟨hx, -, ht', hh⟩ := Proof.Epi.row_coords hp hg hm hrv
              obtain ⟨v, -, he2⟩ := Proof.Epi.shape_stLse_loc hp hg hm hFe hs
              simp only [Event.mk.injEq, Kind.wr.injEq] at he2
              obtain ⟨-, rfl, -⟩ := he2
              have := Proof.Interface.lseLoc_range (Q := Q) (Proof.Epi.outSplit L g)
                (Proof.Epi.outToken Q L g) (Proof.Epi.outHead L g) hx ht' hh
              refine ⟨?_, ?_, .inr ?_⟩
              · rw [hs1]; rfl
              · rw [hc1]; rfl
              · simp only [Proof.EvD.wordAcc] at h1 h2; omega
            · exfalso
              obtain ⟨v, -, he2⟩ := Proof.Epi.shape_stTab hFe hs
              simp only [Event.mk.injEq, Kind.wr.injEq] at he2
              obtain ⟨-, rfl, -⟩ := he2
              exact hsp rfl
            · have hrv : d.pr.rv = true := hI.rv (by rw [hs]; trivial)
              obtain ⟨hx, -, ht', hh⟩ := Proof.Epi.row_coords hp hg hm hrv
              obtain ⟨v, -, he2⟩ := Proof.Epi.shape_stO_loc hp hg hm hFe hs
              simp only [Event.mk.injEq, Kind.wr.injEq] at he2
              obtain ⟨-, rfl, -⟩ := he2
              have hd : Proof.Epi.outCol0 L g + j.val < headDim := by
                have : Proof.Epi.halfM (g % L.block) ≤ 1 := by unfold Proof.Epi.halfM; omega
                have := j.isLt
                unfold Proof.Epi.outCol0 headDim
                omega
              have := Proof.Interface.oLoc_range (Q := Q) (Proof.Epi.outSplit L g)
                (Proof.Epi.outToken Q L g) (Proof.Epi.outHead L g) _ hx ht' hh hd
              refine ⟨?_, ?_, .inl ?_⟩
              · rw [hs1]; rfl
              · rw [hc1]; rfl
              · simp only [Proof.EvD.wordAcc] at h1 h2; omega
        · exact hJ.elim
      | worker w =>
        cases d with
        | worker w => exact (worker_gw w.site hpc).elim
        | idle d => exact (idle_gw d.site hpc).elim
        | loader d P => exact (loader_gw d.site hpc).elim
        | mma d P => exact (mma_gw d.site hpc).elim
        | exit x => exact (exitsite_gw x.site hpc).elim
    · exact hJ.elim

/-- **Global placement of every access of a consistent execution.** -/
theorem global_placed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    GlobalPlaced Q X := by
  intro e a l hmt hc hsp
  have hsa : a.loc.space ≠ .shared := fun h => hsp (hc.1.trans h)
  rcases hmt with ⟨w, hI⟩ | ⟨i, bs, rfl, pc, hn'⟩
  · cases w
    · exact .inl (global_reads hp hX e a l hI hc hsp)
    right
    rcases e with ⟨g, k⟩ | ⟨i, p⟩
    · rcases hI with ⟨bs, -, hw⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
      · cases hw
      · exact global_wr hp hX he hsa hc
      · exact absurd he (no_rmw hX)
    · obtain ⟨hw, hfp⟩ := hI
      cases p with
      | writeLoad x y k =>
        obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hfp
        obtain ⟨col, row, dst, bar, hs, -⟩ := copy_ring hp hX hget
        rw [hs] at hloc
        exact absurd (Proof.Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc).1 hsa
      | writeStore x y k =>
        obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_tensorStore hX)
      | writeCta c =>
        obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_clc hX)
      | writeCopy =>
        obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_copy hX)
      | writeElem j =>
        obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_copy hX)
      | writePrefetch x y k => exact hfp.elim
      | mmaRead isB index => cases hw
      | readLoad x y k => cases hw
      | readCopy => cases hw
      | readStore x y k => cases hw
      | readPrefetch x y k => cases hw
      | oldStore x y k => cases hw
      | oldElem j => cases hw
      | readCta c => cases hw
      | readElem j => cases hw
      | oldCopy => cases hw
      | oldLoad x y k => cases hw
      | oldCta c => cases hw
      | oldPrefetch x y k => cases hw
      | notifyCopy => cases hw
      | notifyLoad => cases hw
      | notifyCta c => cases hw
      | readsDone => cases hw
      | fullDone => cases hw
      | resolve => cases hw
      | tcNotify r => cases hw
      | mmaDone => cases hw
      | arriveOn => cases hw
  · exact absurd hn' (no_nc hX)
end
end PTX.Kernels.InklingRelDecode.Proof2
