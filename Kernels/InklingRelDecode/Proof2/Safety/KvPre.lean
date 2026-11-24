-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.RoleWarp
public import Kernels.InklingRelDecode.Proof.Thread.LpPreSites

@[expose] public section

/-! # The prologue's events on the KV ring

The prologue preloads the ring's slots `b < num_pre`: thread 0 of the CTA arrives on `kv_ready b`
(`arr b`) and the elected lanes of warps 0 and 1 issue the slot's eight copies (`ptc b j`, four
per lane). The ring's declaration names these events by counts (`SingleTmaRing.Decl.pArr`,
`pCp`), so what it needs is that a thread makes at most one arrival and four copies on a slot
there:

* `pro_pc_le`: the prologue's positions never decrease along its steps (`ProA.next_pc_le`, decided
  per flat site), and the steps out of an arrival or a copy increase them (`next_pc_lt`);
* `PCI`, `pc_inv`: at a prologue state the thread's arrivals on `kv_ready b` are at most one, and
  none before the arrival's site; its copies to `kv_ready b` at most the copy sites of block `b`
  before its site. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

theorem qSite_pc_ge (L : Launch) (g : Nat) (dt : Dat) (n : Nat) :
    388 + 32 * min n 4 ≤ (qSite L g dt n).pc := by
  match n with
  | 0 => simp only [qSite]; (repeat' split) <;> decide
  | 1 => simp only [qSite]; (repeat' split) <;> decide
  | 2 => simp only [qSite]; (repeat' split) <;> decide
  | 3 => simp only [qSite]; (repeat' split) <;> decide
  | n + 4 => rw [show min (n + 4) 4 = 4 by omega]; simp only [qSite]; decide

set_option maxHeartbeats 1000000 in
/-- **The flat prologue's positions never decrease.** -/
theorem next_pc_le {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) : s.pc ≤ d'.site.pc := by
  cases s <;> simp only [next] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       dsimp only
       first
         | decide
         | (refine le_trans ?_ (qSite_pc_ge L g _ _); decide))

/-- The positions of the prologue's arrivals and copies. -/
def arrCpPcs : List Nat :=
  [193, 237, 279, 211, 217, 226, 231, 253, 259, 268, 273, 295, 301, 310, 315]

/-- **The steps out of an arrival or a copy increase the position.** -/
theorem next_pc_lt {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (hs : s.pc ∈ arrCpPcs) (h : next L g ⟨s, dt⟩ e = some (some d')) : s.pc < d'.site.pc := by
  cases s
  all_goals first
    | (exfalso; revert hs; decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            dsimp only
            first
              | decide
              | (refine lt_of_lt_of_le ?_ (qSite_pc_ge L g _ _); decide)))

end PTX.Kernels.InklingRelDecode.Proof.ProA

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The prologue's positions never decrease**, and the steps out of an arrival or a copy
increase them. -/
theorem pro_pc_le {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d')) :
    d.site.pc ≤ d'.site.pc ∧ (d.site.pc ∈ Proof.ProA.arrCpPcs → d.site.pc < d'.site.pc) := by
  obtain ⟨s, dt⟩ := d
  simp only
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1
    have hx : d'.site = .exit := by
      simp [ProA.next0] at h'
      rw [← h']
    rw [hx]
    exact ⟨by decide, fun h => by revert h; decide⟩
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    rw [ld2_succ h']
    exact ⟨by decide, fun h => by revert h; decide⟩
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hx' : d'.site ≠ .exit := fun hx => h1 (exit_from_bar18 h hx)
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  have e1 := ProA.pc_old s h2
  have e2 := ProA.pc_old _ hx'
  refine ⟨?_, fun hm => ?_⟩
  · have := Proof.ProA.next_pc_le hf'
    show s.pc ≤ d'.site.pc
    rw [e1, e2]; exact this
  · have := Proof.ProA.next_pc_lt (by rw [← e1]; exact hm) hf'
    show s.pc < d'.site.pc
    rw [e1, e2]; exact this

/-! ### The positions of the ring's event kinds -/

def arrPcs : List Nat := [193, 237, 279, 1013, 2378]
def waitPcs : List Nat := [1257, 2239, 2374, 2462, 2510, 2565]
def commitPcs : List Nat := [2499, 2546, 2548, 2553]

theorem kernel_arr_pcs : OpPcsFast kernel.code arriveOp arrPcs = true := by decide +kernel
theorem kernel_wait_pcs : OpPcsFast kernel.code waitOp waitPcs = true := by decide +kernel
theorem kernel_commit_pcs : OpPcsFast kernel.code commitOp commitPcs = true := by decide +kernel

theorem arr_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {l : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive l tx c rel sc) :
    pc ∈ arrPcs := by
  refine OpPcsFast.mem kernel_arr_pcs hc ?_
  cases hop : arriveOp ins.op
  · exact absurd hk (fires_notArrive (eventTmpl_notArrive (arriveOp_ne hop)) hf _ _ _ _ _)
  · rfl

theorem wait_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {l : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait l p ok acq sc) :
    pc ∈ waitPcs := by
  refine OpPcsFast.mem kernel_wait_pcs hc ?_
  cases hop : waitOp ins.op
  · exact absurd hk (fires_notWait (eventTmpl_notWait (waitOp_ne hop)) hf _ _ _ _ _)
  · rfl

theorem commit_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {sp : TcCommit.Spec} (hk : e.kind = .tc (.commit sp)) : pc ∈ commitPcs := by
  refine OpPcsFast.mem kernel_commit_pcs hc ?_
  cases hop : commitOp ins.op
  · exact absurd hk (fires_notCommit (eventTmpl_notCommit (commitOp_ne hop)) hf _)
  · rfl

theorem proA_arr (s : ProA.Site) (h : s.pc ∈ arrPcs) : ∃ b, s = .arr b := by
  cases s with
  | arr b => exact ⟨b, rfl⟩
  | ld k | el k | init k | psh k | ldq k | st9 k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

theorem kvReadyOf_loc (c b : Nat) (hb : b < 3) :
    (Proof.EvD.kvReadyOf b).loc L c = Proof.EvW.kvReady L c b := by
  simp only [Proof.EvD.kvReadyOf, Proof.EvD.Bar.loc, Proof.EvD.Bar.off, Proof.EvW.kvReady,
    Proof.EvW.barLoc, Proof.EvW.kvReadyOff, Loc.mk.injEq, true_and]
  rw [Nat.mod_eq_of_lt hb]

/-! ### The prologue's counts -/

def arrPcB (b : Nat) : Nat := [193, 237, 279].getD b 0
def ptcPcsB (b : Nat) : List Nat :=
  [[211, 217, 226, 231], [253, 259, 268, 273], [295, 301, 310, 315]].getD b []

/-- **The prologue's counts on its CTA's ring**: at most one arrival on `kv_ready b`, none before
the arrival's site; at most the block's copy sites before the site's copies to it. -/
def PCI (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → List Event → Prop
  | (.inl _, _), es => objN es = 0
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), es => ∀ b < 3,
      arrivals (Proof.EvW.kvReady L (g / L.block) b) es ≤
        (if arrPcB b < d.site.pc then 1 else 0) ∧
      es.countP (issuesTo (Proof.EvW.kvReady L (g / L.block) b)) ≤
        (ptcPcsB b).countP (· < d.site.pc)
  | _, _ => True

theorem countP_lt_mono (l : List Nat) {x y : Nat} (h : x ≤ y) :
    l.countP (· < x) ≤ l.countP (· < y) :=
  List.countP_mono_left fun a _ ha => by simp only [decide_eq_true_eq] at ha ⊢; omega

theorem arr_bound_mono (b : Nat) {x y : Nat} (h : x ≤ y) :
    (if arrPcB b < x then 1 else 0) ≤ (if arrPcB b < y then 1 else 0) := by
  split <;> split <;> omega

/-- The step of a prologue state by an event that is no arrival and no copy keeps the counts. -/
theorem pci_other {d d' : ProA.D} {e : Event} {es : List Event}
    (hR : ∀ b < 3, arrivals (Proof.EvW.kvReady L (g / L.block) b) es ≤
        (if arrPcB b < d.site.pc then 1 else 0) ∧
      es.countP (issuesTo (Proof.EvW.kvReady L (g / L.block) b)) ≤
        (ptcPcsB b).countP (· < d.site.pc))
    (hle : d.site.pc ≤ d'.site.pc)
    (ha : ∀ b, arrivesOn (Proof.EvW.kvReady L (g / L.block) b) e = false)
    (hc : ∀ b, issuesTo (Proof.EvW.kvReady L (g / L.block) b) e = false) :
    ∀ b < 3, arrivals (Proof.EvW.kvReady L (g / L.block) b) (es ++ [e]) ≤
        (if arrPcB b < d'.site.pc then 1 else 0) ∧
      (es ++ [e]).countP (issuesTo (Proof.EvW.kvReady L (g / L.block) b)) ≤
        (ptcPcsB b).countP (· < d'.site.pc) := by
  intro b hb
  obtain ⟨h1, h2⟩ := hR b hb
  rw [arrivals_snoc, countP_snoc', ha b, hc b]
  have := arr_bound_mono b hle
  have := countP_lt_mono (ptcPcsB b) hle
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
  omega

theorem kvCopy_bytes (Q : Params) (cta col row dst : Nat) (bar : Loc) :
    TensorTransfer.bytes (Proof.EvW.kvCopySpec Q cta col row dst bar).descriptor = 8192 := by
  simp [Proof.EvW.kvCopySpec, TensorTransfer.bytes, mapKv, TensorTile.count,
    TensorTile.step, TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes]

theorem arr_old (b : Fin 3) : (ProA.Site.arr b).old = Proof.ProA.arrSite b.val := by
  fin_cases b <;> rfl

/-- A byte address of slot `s` of the K or V ring. -/
def InSlot (L : Launch) (s a : Nat) : Prop :=
  (L.sharedBase + 32768 * s ≤ a ∧ a < L.sharedBase + 32768 * s + 32768) ∨
    (L.sharedBase + 98304 + 32768 * s ≤ a ∧ a < L.sharedBase + 98304 + 32768 * s + 32768)

/-- **A prologue event on the ring**: the arrival of block `b` at its site, on `kv_ready b`; a copy
of block `b` at its site, to `kv_ready b`, of 8192 bytes; or no arrival and no copy. -/
theorem pro_ev_kv (hp : Pre Q L m) {tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat}
    {t u : TState} {ins : Instr} {e : Event}
    (hJ : ProRef Q L g tm bw d n)
    (hat : (ProA.code L g (Startup.inh L g Q tm) bw).AtD d t)
    (hi : (ProA.code L g (Startup.inh L g Q tm) bw).inv d) (hx : d.site ≠ .exit)
    (hc : kernel.code[(ProA.code L g (Startup.inh L g Q tm) bw).pc d]? = some ins)
    (hf : Fires ((ProA.code L g (Startup.inh L g Q tm) bw).pc d)
      (eventTmpl Assumptions.all L g t ins.op) e (some u)) :
    (∃ b : Fin 3, d.site = .arr b ∧
      e.kind = .arrive (Proof.EvW.kvReady L (g / L.block) b) 65536 1 true .cta) ∨
    (∃ (b : Fin 3) (j : Fin 4), d.site = .ptc b j ∧ ∃ a sp, e.kind = .tensorIssue a sp ∧
      sp.mbar = Proof.EvW.kvReady L (g / L.block) b ∧
      TensorTransfer.bytes sp.descriptor = 8192 ∧
      ∀ x y z l, TensorCopy.writeLoc sp x y z = some l → l.space = .shared ∧
        l.cta = g / L.block ∧ InSlot L b l.addr) ∨
    ((∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc) ∧ ∀ a sp, e.kind ≠ .tensorIssue a sp) := by
  have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi hc hf
  by_cases ha : ∃ l tx c rel sc, e.kind = .arrive l tx c rel sc
  · obtain ⟨l, tx, c, rel, sc, hk⟩ := ha
    obtain ⟨b, hs⟩ := proA_arr d.site (arr_pc hc hf hk)
    have he := Proof.ProA.shape_arr (Proof.ProA.sharedOk_of_pre hp) (j := b.val) b.isLt hF
      (by simp only [ProA.D.old, hs, arr_old])
    refine .inl ⟨b, hs, ?_⟩
    rw [he, kvReadyOf_loc _ _ b.isLt]
  by_cases hcp : ∃ a sp, e.kind = .tensorIssue a sp
  · obtain ⟨a, sp, hk⟩ := hcp
    have hop : tensorOp ins.op = true := by
      cases hq : tensorOp ins.op
      · exact absurd hk (fires_notTensor (eventTmpl_notTensor hq) hf a sp)
      · rfl
    obtain ⟨b, j, hs⟩ := proA_copy d.site (OpPcsFast.mem kernel_copy_pcs hc hop)
    obtain ⟨-, -, hP, -⟩ := hJ
    have hmap : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0 := by
      rw [hP.pro]; rfl
    have hi12 : 4 * b.val + j.val < 12 := by omega
    have he' := Proof.ProA.ptc_event_map hp (i := 4 * b.val + j.val) hi12 hmap hF
      (by simp only [ProA.D.old, hs, ptc_old])
    subst he'
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine .inr (.inl ⟨b, j, hs, _, _, rfl, ?_, kvCopy_bytes _ _ _ _ _ _, ?_⟩)
    · simp only [Proof.EvW.kvCopySpec]
      rw [kvReadyOf_loc _ _ (by omega)]
      congr 1
      omega
    · intro x y z l hl
      obtain ⟨h1, h2, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q _ _ _ _ _ hl
      have hsb : Proof.ProA.SbRoom L := by
        have := hp.sharedRange; unfold sharedBytes at this; unfold Proof.ProA.SbRoom; omega
      rw [show (ProA.D.old d).dt = d.dt from rfl, Proof.ProA.copyDst_form L g d.dt hsb hi12]
        at h3 h4
      have h5 := Proof.ProA.half_lt d.dt ((4 * b.val + j.val) / 4)
      have hb4 : (4 * b.val + j.val) / 4 = b.val := by omega
      rw [hb4] at h3 h4 h5
      refine ⟨h1, h2, ?_⟩
      unfold InSlot
      have : (4 * b.val + j.val) % 2 = 0 ∨ (4 * b.val + j.val) % 2 = 1 := by omega
      rcases this with h | h <;> rw [h] at h3 h4 <;> [left; right] <;> constructor <;> omega
  · exact .inr (.inr ⟨fun l tx c rel sc h => ha ⟨l, tx, c, rel, sc, h⟩,
      fun a sp h => hcp ⟨a, sp, h⟩⟩)

theorem ptc_step (b : Fin 3) (j : Fin 4) {y : Nat} (hy : (ProA.Site.ptc b j).pc < y) :
    (ptcPcsB b).countP (· < (ProA.Site.ptc b j).pc) + 1 ≤ (ptcPcsB b).countP (· < y) := by
  have h1 : (ptcPcsB b).countP (· < (ProA.Site.ptc b j).pc + 1) =
      (ptcPcsB b).countP (· < (ProA.Site.ptc b j).pc) + 1 := by
    fin_cases b <;> fin_cases j <;> decide
  have := countP_lt_mono (ptcPcsB b) (show (ProA.Site.ptc b j).pc + 1 ≤ y by omega)
  omega

theorem arr_pcB (b : Fin 3) : (ProA.Site.arr b).pc = arrPcB b.val := by fin_cases b <;> rfl

theorem arr_mem (b : Fin 3) : (ProA.Site.arr b).pc ∈ Proof.ProA.arrCpPcs := by
  fin_cases b <;> decide

theorem ptc_mem (b : Fin 3) (j : Fin 4) : (ProA.Site.ptc b j).pc ∈ Proof.ProA.arrCpPcs := by
  fin_cases b <;> fin_cases j <;> decide

/-- **The prologue's counts along every thread.** -/
theorem pci_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      PCI Q L g σ ((X.tr g).take k) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake]
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      cases o with
      | none => exact absurd (fires_none_ends hf) hnE
      | some u =>
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup: no object event
        have he0 : isObjEv e = false := by
          cases hq : isObjEv e
          · rfl
          · exact absurd (obj_pc hc hf hq) (fun h => startup_obj st.site h)
        have h0 : objN ((X.tr g).take k ++ [e]) = 0 := by
          rw [objN_snoc, hR0, he0]; rfl
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · intro b hb
            exact ⟨by rw [arrivals_zero h0]; omega, by rw [issues_zero h0]; omega⟩
          · trivial
          · trivial
        · exact h0
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hx : ProA.exitOf d'' = none ∨ ∃ v, ProA.exitOf d'' = some v := by
              cases ProA.exitOf d'' <;> simp
            rcases hx with hx | ⟨v, hxo⟩
            · rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
              obtain ⟨rfl, -⟩ := he''
              have hR : ∀ b < 3, _ := hR0
              show ∀ b < 3, _
              have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
              obtain ⟨hle, hlt'⟩ := pro_pc_le hd''
              rcases pro_ev_kv hp (hJ : ProRef Q L g tm bw d n) hat hi.1 hxd hc hf with
                ⟨b0, hs, hk'⟩ | ⟨b0, j, hs, a, sp, hk', hsp, -⟩ | ⟨hna, hnc⟩
              · intro b hb
                obtain ⟨h1, h2⟩ := hR b hb
                have hstr := hlt' (by rw [hs]; exact arr_mem b0)
                rw [arrivals_snoc, countP_snoc']
                have hie : issuesTo (Proof.EvW.kvReady L (g / L.block) b) e = false := by
                  simp [issuesTo, hk']
                have hae : arrivesOn (Proof.EvW.kvReady L (g / L.block) b) e =
                    decide (b0.val = b) := by
                  simp [arrivesOn, sourceArrive, hk', kvReady_inj]
                rw [hie, hae]
                have := countP_lt_mono (ptcPcsB b) hle
                refine ⟨?_, by simp only [Bool.false_eq_true, ite_false]; omega⟩
                by_cases hbb : b0.val = b
                · subst hbb
                  rw [hs, arr_pcB] at h1 hstr
                  simp only [lt_irrefl, ite_false, decide_true, ite_true] at h1 ⊢
                  simp only [hstr, ite_true]; omega
                · simp only [hbb, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
                  have := arr_bound_mono b hle
                  omega
              · intro b hb
                obtain ⟨h1, h2⟩ := hR b hb
                have hstr := hlt' (by rw [hs]; exact ptc_mem b0 j)
                rw [arrivals_snoc, countP_snoc']
                have hae : arrivesOn (Proof.EvW.kvReady L (g / L.block) b) e = false := by
                  simp [arrivesOn, sourceArrive, hk']
                have hie : issuesTo (Proof.EvW.kvReady L (g / L.block) b) e =
                    decide (b0.val = b) := by
                  simp [issuesTo, hk', hsp, kvReady_inj]
                rw [hie, hae]
                have := arr_bound_mono b hle
                refine ⟨by simp only [Bool.false_eq_true, ite_false]; omega, ?_⟩
                by_cases hbb : b0.val = b
                · subst hbb
                  rw [hs] at h2 hstr
                  have := ptc_step b0 j hstr
                  simp only [decide_true, ite_true]
                  omega
                · simp only [hbb, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
                  have := countP_lt_mono (ptcPcsB b) hle
                  omega
              · refine pci_other hR hle (fun b => ?_) (fun b => ?_)
                · cases hq : arrivesOn (Proof.EvW.kvReady L (g / L.block) b) e
                  · rfl
                  · exfalso
                    simp only [arrivesOn, sourceArrive] at hq
                    cases hq
                · cases hq : issuesTo (Proof.EvW.kvReady L (g / L.block) b) e
                  · rfl
                  · exfalso
                    simp only [issuesTo] at hq
                    cases hq
            · -- the prologue's exit enters the softmax region or its stub
              cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
          · rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            trivial
          · exact hJ.elim
      · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
