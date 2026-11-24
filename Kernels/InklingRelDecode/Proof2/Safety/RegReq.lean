-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.WarpPoll
public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure
public import Kernels.InklingRelDecode.Proof.Protocol.RegSyncOf

@[expose] public section

/-! # The register requests and the barrier-1 events (`RegLedger`)

`SetMaxNReg.UnsafeAt` is discharged from `Proof.Bar.RegLedger` (`Protocol/RegSyncOf.lean`), a
statement
about two kinds of event of one thread, the `setmaxnreg` requests and the `barrier.sync 1`
arrivals, by their counts. On the role table:

* the request and barrier-1 phases of a state (`rph`): the first tree's pure tables
  (`Ledger.dPh` for the softmax region and the epilogue, `Ledger.wPh` for the workers; the
  prologue's `setmaxnreg.inc` at its first site, `bar18` its barrier);
* `RQ`, `rq_inv`: along every thread the requests `r` and the barrier-1 events `c` before a state
  satisfy `r + ph₂ = c + ph₁`: the two advance by the state's instruction (`req_iff`,
  `bar1_iff`), and a worker role's tail returns to the loop's head one round on, both by 3
  (`Ledger.w_next`);
* `reg_ledger`: the three fields, with the barrier-1 counts of the roles (`c1_inv`,
  `role_count`, `ri_inv`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Ledger (dPh wPh rInc bInc wReqS wB1S reqAt barAt wrap wTo)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### An event is a request, a barrier-1 event, by its position -/

/-- Every `setmaxnreg` of the program has a count the model accepts. -/
def reqValid' : Op → Bool
  | .setMaxReg _ n => SetMaxNReg.validCount n
  | _ => true

theorem kernel_reqValid' : kernel.code.all (fun ins => reqValid' ins.op) = true := by
  decide +kernel

theorem req_iff {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (if SetMaxNReg.isRequest e then 1 else 0) = rInc (reqAt pc) ∧
      ∀ pc' i n inst, e = ⟨pc', .setMaxReg i n inst⟩ → reqAt pc = some (i, n) := by
  by_cases hq : ∃ i n, ins.op = .setMaxReg i n
  · obtain ⟨i, n, hop⟩ := hq
    have hall := List.all_eq_true.mp kernel_reqValid' ins (List.mem_of_getElem? hc)
    rw [hop] at hall hf
    simp only [reqValid'] at hall
    obtain ⟨inst, rfl⟩ := fires_of_setMaxReg_op hall hf
    have h1 : reqAt pc = some (i, n) := by simp [reqAt, hc, hop]
    refine ⟨by simp [SetMaxNReg.isRequest, h1, rInc], ?_⟩
    intro pc' i' n' inst' h
    simp only [Event.mk.injEq, Kind.setMaxReg.injEq] at h
    obtain ⟨-, rfl, rfl, -⟩ := h
    exact h1
  · have hn : reqAt pc = none := by
      simp only [reqAt, hc]
      cases hop : ins.op <;> simp_all
    refine ⟨?_, fun pc' i n inst h => absurd ⟨i, n, fires_setMaxReg_op hf (by rw [h])⟩ hq⟩
    rw [hn]
    cases hr : SetMaxNReg.isRequest e
    · rfl
    · exfalso
      obtain ⟨pc', kd⟩ := e
      cases kd <;> simp only [SetMaxNReg.isRequest, Bool.false_eq_true] at hr
      rename_i inc n inst
      exact hq ⟨inc, n, fires_setMaxReg_op hf rfl⟩

/-- `barrier.sync 1` is at the positions of `bar1Pcs`. -/
theorem b1At_barAt (pc : Nat) : b1At pc = bInc (barAt pc) := by
  unfold b1At bInc barAt
  by_cases hp : pc ∈ bar1Pcs
  · obtain ⟨ins, hc⟩ : ∃ ins, kernel.code[pc]? = some ins := by
      cases hq : kernel.code[pc]? with
      | none =>
        exfalso
        have := List.all_eq_true.mp kernel_bar1_ins pc hp
        rw [hq] at this
        simp [isBar1Ins] at this
      | some ins => exact ⟨ins, rfl⟩
    obtain ⟨al, hop⟩ := kernel_bar1_code hp hc
    simp [hp, hc, hop]
  · simp only [hp, ↓reduceIte]
    cases hq : kernel.code[pc]? with
    | none => rfl
    | some ins =>
      have hn : ¬ bar1Op ins.op = true := fun h => hp (OpPcsFast.mem kernel_bar1_pcs hq h)
      change 0 = if bar1Op ins.op then 1 else 0
      rw [Bool.not_eq_true] at hn
      rw [hn]
      rfl

/-! ### The phases of the role table -/

/-- **The phase `(requests, barrier-1 events)` of a state**, in its round. -/
def rph : (thread Q L g).D → Nat × Nat
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _) =>
    if d.site = .sMax then (0, 0) else if d.site = .exit then (1, 1) else (1, 0)
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _) => dPh (.sm d)
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _) => dPh (.epi d)
  | (.inr ⟨.inl (.worker _), σ⟩, _) => wPh σ
  | _ => (0, 0)

/-- **The requests and the barrier-1 events of a state** advance together (not claimed at the
stubs, which no followed thread enters). -/
def RQ : (thread Q L g).D → Nat → Nat → Prop
  | (.inl _, _), r, c => r = c
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), r, c =>
    r + (if d.site = .sMax then 0 else if d.site = .exit then 1 else 0) =
      c + (if d.site = .sMax then 0 else 1)
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _), r, c =>
    r + (dPh (.sm d)).2 = c + (dPh (.sm d)).1
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _), r, c =>
    r + (dPh (.epi d)).2 = c + (dPh (.epi d)).1
  | (.inr ⟨.inl (.worker _), σ⟩, _), r, c => r + (wPh σ).2 = c + (wPh σ).1
  | _, _, _ => True

theorem startup_static (s : Startup.Site) (hs : ∀ r, s ≠ .enter r) :
    reqAt s.pc = none ∧ barAt s.pc = false := by
  cases s with
  | enter r => exact absurd rfl (hs r)
  | _ => decide +kernel

/-- A prologue successor is not its first site. -/
theorem pro_next_ne' {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d')) :
    d'.site ≠ .sMax := by
  obtain ⟨s, dt⟩ := d
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1
    have hx : d'.site = .exit := by simp [ProA.next0] at h'; rw [← h']
    rw [hx]; nofun
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3; rw [ld2_succ h']; nofun
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  have := Proof.Ledger.pro_next_ne hf'
  intro hs
  apply this
  show d'.site.old = _
  rw [hs]; rfl

theorem proReq_old (s : ProA.Site) (hx : s ≠ .exit) :
    reqAt s.pc = (if s = .sMax then some (true, 256) else none) ∧
      barAt s.pc = decide (s = .bar18) := by
  rw [ProA.pc_old s hx]
  obtain ⟨h1, h2⟩ := Proof.Ledger.pro_static s.old
  rw [h1, h2]
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert hx; fin_cases k <;> decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    revert hx; fin_cases b <;> fin_cases j <;> decide
  | exit => exact absurd rfl hx
  | _ => revert hx; decide

set_option maxHeartbeats 1000000 in
/-- **The requests and the barrier-1 events along every thread.** -/
theorem rq_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      RQ σ (((X.tr g).take k).countP SetMaxNReg.isRequest)
        (((X.tr g).take k).countP (Execution.isBarId 1)) := by
  have hb : L.block = 256 := hp.block
  have hb128 : L.block ≠ 128 := by omega
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    show 0 = 0
    rfl
  | succ k ih =>
    intro hk σ' hσ'0
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hσ' := hσ'0
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake, countP_snoc2, countP_snoc2]
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
      have hrq := (req_iff hc hf).1
      have hb1 := bar1_iff hc hf hb128
      rw [b1At_barAt] at hb1
      rw [hrq, hb1]
      cases o with
      | none => exact absurd (fires_none_ends hf) hnE
      | some u =>
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup
        have hne : ∀ r, st.site ≠ .enter r := by
          intro r h
          have : StartRef st n := hJ
          unfold StartRef at this
          rw [h] at this
          exact this
        obtain ⟨hs1, hs2⟩ := startup_static st.site hne
        have hrs : reqAt ((thread Q L g).pc (.inl st, n)) = none := hs1
        have hbs : barAt ((thread Q L g).pc (.inl st, n)) = false := hs2
        rw [hrs, hbs]
        have hR0' : _ = _ := hR0
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · show _ + (if ProA.Site.sMax = .sMax then 0 else _) =
              _ + (if ProA.Site.sMax = .sMax then 0 else 1)
            simp only [ite_true, rInc, bInc, Option.isSome_none, Bool.false_eq_true, ite_false]
            omega
          · show _ + (wPh (.worker _)).2 = _ + (wPh (.worker _)).1
            simp only [wPh, rInc, bInc, Option.isSome_none, Bool.false_eq_true, ite_false]
            omega
          · trivial
        · show _ = _
          simp only [rInc, bInc, Option.isSome_none, Bool.false_eq_true, ite_false]
          omega
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hW : WSite (b32 0) d := hJ.2.2.1
          have hRI : RIt d _ := ri_inv hp hX hg k hlt _ hk0
          have hs0 : wTo d = false := by
            cases d with
            | worker ww =>
              obtain ⟨hs, -⟩ := hW
              obtain ⟨-, -, -, h0, h1⟩ := hRI
              simp only [wTo, decide_eq_false_iff_not]
              rcases hs with h | h | h | h | h <;> rw [h] <;> simp_all
            | _ => rfl
          obtain ⟨p1, p2, -⟩ := Proof.Ledger.w_next hσw hs0
          obtain ⟨q1, q2⟩ := Proof.Ledger.w_static d
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.worker w), d⟩, n) = Proof.WComp.pc d := rfl
          have hR0' : _ + (wPh d).2 = _ + (wPh d).1 := hR0
          show _ + (wPh σw').2 = _ + (wPh σw').1
          rw [hpc, q1, q2]
          omega
        | dp tm bw =>
          rcases d with d | ⟨dt | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
            obtain ⟨q1, q2⟩ := proReq_old d.site hxd
            have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = d.site.pc := rfl
            rw [hpc, q1, q2]
            have hR0' : _ + (if d.site = .sMax then 0 else if d.site = .exit then 1 else 0) =
                _ + (if d.site = .sMax then 0 else 1) := hR0
            simp only [hxd, ite_false] at hR0'
            have hx : ProA.exitOf d'' = none ∨ ∃ v, ProA.exitOf d'' = some v := by
              cases ProA.exitOf d'' <;> simp
            rcases hx with hx | ⟨v, hxo⟩
            · rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
              obtain ⟨rfl, -⟩ := he''
              have hx'' : d''.site ≠ .exit := proA_site_ne hx
              have hs'' := pro_next_ne' hd''
              have hnb : d.site ≠ .bar18 := by
                intro h
                obtain ⟨s, dt⟩ := d
                simp only at h
                subst h
                exact hx'' (bar18_next hd'')
              show _ + (if d''.site = .sMax then 0 else if d''.site = .exit then 1 else 0) =
                _ + (if d''.site = .sMax then 0 else 1)
              simp only [hs'', hx'', hnb, ite_false, decide_false, bInc, Bool.false_eq_true]
              by_cases h0 : d.site = .sMax <;> simp only [h0, ite_true, ite_false, rInc,
                Option.isSome_some, Option.isSome_none, Bool.false_eq_true] at hR0' ⊢ <;> omega
            · have hxs : d''.site = .exit := by
                simp only [ProA.exitOf] at hxo; split at hxo <;> simp_all
              have hb18 := exit_from_bar18 hd'' hxs
              simp only [hb18, decide_true, ite_false, reduceCtorEq, bInc, ite_true, rInc,
                Option.isSome_none, Bool.false_eq_true] at hR0' ⊢
              cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                show _ + (dPh (.sm (tailInit Q L g dt'))).2 = _ + (dPh (.sm (tailInit Q L g dt'))).1
                simp only [tailInit, Proof.SmEntry.d0, dPh]
                omega
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
          · rw [next_tail] at hn
            obtain ⟨τ', hτ, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            cases τ with
            | epi d =>
              have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, n) =
                d.site.pc := rfl
              obtain ⟨q1, q2⟩ := Proof.Ledger.epi_static d.site
              rw [hpc, q1, q2]
              simp only [Tail.next] at hτ
              obtain ⟨d', hd', rfl⟩ := mm_some hτ
              obtain ⟨p1, p2⟩ := Proof.Ledger.epi_next_ph hd'
              have hR0' : _ + (dPh (.epi d)).2 = _ + (dPh (.epi d)).1 := hR0
              show _ + (dPh (.epi d')).2 = _ + (dPh (.epi d')).1
              omega
            | sm d =>
              have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, n) =
                d.site.pc := rfl
              obtain ⟨q1, q2⟩ := Proof.Ledger.sm_static d.site
              rw [hpc, q1, q2]
              have hR0' : _ + (dPh (.sm d)).2 = _ + (dPh (.sm d)).1 := hR0
              simp only [Tail.next] at hτ
              split at hτ
              · rename_i hl
                simp only [Tail.exitNext] at hτ
                split at hτ
                · simp only [Option.some.injEq] at hτ
                  subst hτ
                  show _ + (dPh (.epi _)).2 = _ + (dPh (.epi _)).1
                  obtain ⟨s, en, i, m0, l, cw, cv, w, v, sv, pf, stg⟩ := d
                  cases s <;> simp only [Proof.DComp.leaves] at hl <;>
                    simp_all [dPh, Proof.Epi.D.entry, Proof.Ledger.smReq, Proof.Ledger.smB1,
                      rInc, bInc]
                · cases hτ
              · rename_i hl
                obtain ⟨d', hd', rfl⟩ := mm_some hτ
                have hD : Proof.DComp.next L g Q (.sm d) e = some (some (.sm d')) := by
                  simp [Proof.DComp.next, Proof.DComp.smNext, hl, hd']
                obtain ⟨p1, p2⟩ := Proof.Ledger.d_next_ph hD
                show _ + (dPh (.sm d')).2 = _ + (dPh (.sm d')).1
                simp only [Proof.Ledger.dReq, Proof.Ledger.dB1] at p1 p2
                omega
          · exact hJ.elim
      · exact hJ.elim

/-! ### The tables at the request and barrier sites -/

theorem wph_wPh {σ : Proof.WComp.WSt} (hs : wTo σ = false) : wph σ = (wPh σ).2 % 3 := by
  cases σ with
  | worker w =>
    obtain ⟨site, P⟩ := w
    cases site <;> simp_all [wph, wPh, wTo]
  | idle d => obtain ⟨site, P⟩ := d; cases site <;> simp [wph, wPh, idPh]
  | loader d P => obtain ⟨site, _, _, _, _, _, _⟩ := d; cases site <;> simp [wph, wPh, ldPh]
  | mma d P => obtain ⟨site, _, _, _, _⟩ := d; cases site <;> simp [wph, wPh, mmPh]
  | exit x => rfl

theorem w_req_ph {σ : Proof.WComp.WSt} {x : Bool × Nat} (h : wReqS σ = some x) :
    (wPh σ).1 ≤ 2 ∧ ((wPh σ).1 = 0 → ∃ P, σ = .worker ⟨.loop, P⟩) ∧
      ((wPh σ).1 = 1 → (wPh σ).2 = 1) ∧ ((wPh σ).1 = 2 → (wPh σ).2 = 3) := by
  cases σ with
  | worker w =>
    obtain ⟨site, P⟩ := w
    cases site <;> simp_all [wReqS, Proof.Ledger.wReq, wPh]
  | idle d => obtain ⟨site, P⟩ := d; cases site <;> simp_all [wReqS, Proof.Ledger.idleReq, wPh]
  | loader d P =>
    obtain ⟨site, _, _, _, _, _, _⟩ := d
    cases site <;> simp_all [wReqS, Proof.Ledger.loaderReq, wPh]
  | mma d P =>
    obtain ⟨site, _, _, _, _⟩ := d
    cases site <;> simp_all [wReqS, Proof.Ledger.mmaReq, wPh]
  | exit x => simp [wReqS] at h

theorem w_b1_ph {σ : Proof.WComp.WSt} (h : wB1S σ = true) (hs : wTo σ = false) :
    (wPh σ).2 ≤ (wPh σ).1 ∧ (wph σ = 0 → (wPh σ).2 + 1 ≤ (wPh σ).1) := by
  cases σ with
  | worker w =>
    obtain ⟨site, P⟩ := w
    cases site <;> simp_all [wB1S, Proof.Ledger.wB1, wPh, wph, wTo]
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp_all [wB1S, Proof.Ledger.idleB1, wPh, wph, idPh]
  | loader d P =>
    obtain ⟨site, _, _, _, _, _, _⟩ := d
    cases site <;> simp_all [wB1S, Proof.Ledger.loaderB1, wPh, wph, ldPh]
  | mma d P =>
    obtain ⟨site, _, _, _, _⟩ := d
    cases site <;> simp_all [wB1S, Proof.Ledger.mmaB1, wPh, wph, mmPh]
  | exit x => simp [wB1S] at h

theorem loop_exempt : ¬ (Assumptions.all.all
    (fun a => !a.regSyncExempt Proof.Worker.Site.loop.pc) = true) := by
  simp [Assumptions.all, Assumptions.setMaxNRegSync, Assumption.setMaxNRegSyncAt,
    Assumptions.regSyncSites, Proof.Worker.Site.pc]

/-- A worker state of the role table is at no role entry and no bad site. -/
theorem wTo_false (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {w : Value}
    {d : Proof.WComp.WSt} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.worker w), d⟩, n))) :
    wTo d = false := by
  have hJ := (good_all' hp hX hg k).2 _ hσ
  have hW : WSite (b32 0) d := hJ.2.2.1
  have hRI : RIt d _ := ri_inv hp hX hg k hk _ hσ
  cases d with
  | worker ww =>
    obtain ⟨hs, -⟩ := hW
    obtain ⟨-, -, -, h0, h1⟩ := hRI
    simp only [wTo, decide_eq_false_iff_not]
    rcases hs with h | h | h | h | h <;> rw [h] <;> simp_all
  | _ => rfl

/-! ### The ledger -/

/-- **A barrier-1 event has at least as many requests before it, one more at the first.** -/
theorem bar1_rq (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h i pc : Nat}
    {cnt : Option Nat} {md : BarMode} (he : X.get (h, i) = some ⟨pc, .bar 1 cnt md⟩) :
    Proof.Bar.b1Before X h i ≤ Proof.Bar.rqBefore X h i ∧
      (Proof.Bar.b1Before X h i = 0 → 1 ≤ Proof.Bar.rqBefore X h i) := by
  have hb : L.block = 256 := hp.block
  have hh := Frame.lt_of_get hX he
  have hlen : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hb1 := bar1_iff hc hf (by omega)
  rw [b1At_barAt] at hb1
  simp only [Execution.isBarId] at hb1
  have hbar : barAt ((thread Q L h).pc σ) = true := by
    cases hq : barAt ((thread Q L h).pc σ)
    · rw [hq] at hb1; simp [bInc] at hb1
    · rfl
  have hR := rq_inv hp hX hh i hlen _ hσ
  unfold Proof.Bar.b1Before Proof.Bar.rqBefore
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hne : ∀ r, st.site ≠ .enter r := by
      intro r h'
      have : StartRef st n := hJ
      unfold StartRef at this
      rw [h'] at this
      exact this
    rw [show barAt _ = false from (startup_static st.site hne).2] at hbar
    cases hbar
  · rename_i i'
    cases i' with
    | dp tm bw =>
      rcases d with d | ⟨dt | _, τ⟩
      · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
        have q2 := (proReq_old d.site hxd).2
        have hpc : (thread Q L h).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = d.site.pc := rfl
        rw [hpc, q2] at hbar
        simp only [decide_eq_true_eq] at hbar
        have hR' : _ + (if d.site = .sMax then 0 else if d.site = .exit then 1 else 0) =
            _ + (if d.site = .sMax then 0 else 1) := hR
        simp only [hbar, reduceCtorEq, ite_false] at hR'
        omega
      · cases τ with
        | sm d =>
          have hpc : (thread Q L h).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, n) =
            d.site.pc := rfl
          rw [hpc, (Proof.Ledger.sm_static d.site).2] at hbar
          have hR' : _ + (dPh (.sm d)).2 = _ + (dPh (.sm d)).1 := hR
          have hs : d.site = .bar0 := by
            revert hbar; cases d.site <;> simp [Proof.Ledger.smB1]
          have hd : dPh (.sm d) = (2, 1) := by simp [dPh, hs]
          rw [hd] at hR'
          omega
        | epi d =>
          have hpc : (thread Q L h).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, n) =
            d.site.pc := rfl
          rw [hpc, (Proof.Ledger.epi_static d.site).2] at hbar
          have hR' : _ + (dPh (.epi d)).2 = _ + (dPh (.epi d)).1 := hR
          have hC : _ = epiPh d := c1_inv hp hX hh i hlen _ hσ
          have hs : d.site = .bar1 ∨ d.site = .bar2 := by
            revert hbar; cases d.site <;> simp [Proof.Ledger.epiB1]
          rcases hs with hs | hs
          · have hd : dPh (.epi d) = (2, 2) := by simp [dPh, hs]
            have he : epiPh d = 2 := by simp [epiPh, hs]
            rw [hd] at hR'; rw [he] at hC; omega
          · have hd : dPh (.epi d) = (3, 3) := by simp [dPh, hs]
            have he : epiPh d = 3 := by simp [epiPh, hs]
            rw [hd] at hR'; rw [he] at hC; omega
      · exact hJ.elim
    | worker w =>
      have hpc : (thread Q L h).pc (.inr ⟨.inl (.worker w), d⟩, n) = Proof.WComp.pc d := rfl
      rw [hpc, (Proof.Ledger.w_static d).2] at hbar
      have hR' : _ + (wPh d).2 = _ + (wPh d).1 := hR
      have hW : _ % 3 = wph d := w1_inv hp hX hh i hlen _ hσ
      obtain ⟨h1, h2⟩ := w_b1_ph hbar (wTo_false hp hX hh hlen hσ)
      refine ⟨by omega, fun h0 => ?_⟩
      rw [h0] at hW
      have := h2 hW.symm
      omega
  · exact hJ.elim

/-- **The register-request ledger** on the role table. -/
theorem reg_ledger (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Proof.Bar.RegLedger L X where
  shape := by
    intro g k pc inc n inst hg he
    have hb : L.block = 256 := hp.block
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hq := (req_iff hc hf).2 _ _ _ _ rfl
    have hR := rq_inv hp hX hg k hlen _ hσ
    unfold Proof.Bar.rqBefore
    obtain ⟨x, nn⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exfalso
      have hne : ∀ r, st.site ≠ .enter r := by
        intro r h'
        have : StartRef st nn := hJ
        unfold StartRef at this
        rw [h'] at this
        exact this
      rw [show reqAt _ = none from (startup_static st.site hne).1] at hq
      cases hq
    · rename_i i'
      cases i' with
      | dp tm bw =>
        have hdp : g % L.block < 128 := dp_lane k hσ
        have hw : g % L.block / 128 = 0 := by omega
        rw [hw]
        simp only [Proof.Bar.regSched, zero_ne_one, false_and, ite_false]
        rcases d with d | ⟨dt | _, τ⟩
        · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, nn) = d.site.pc := rfl
          rw [hpc, (proReq_old d.site hxd).1] at hq
          split at hq
          · simp only [Option.some.injEq, Prod.mk.injEq] at hq
            rw [hq.1, hq.2]
          · cases hq
        · cases τ with
          | sm d =>
            have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, nn) =
              d.site.pc := rfl
            rw [hpc, (Proof.Ledger.sm_static d.site).1] at hq
            cases hs : d.site <;> simp_all [Proof.Ledger.smReq]
          | epi d =>
            have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, nn) =
              d.site.pc := rfl
            rw [hpc, (Proof.Ledger.epi_static d.site).1] at hq
            cases hs : d.site <;> simp_all [Proof.Ledger.epiReq]
        · exact hJ.elim
      | worker w =>
        have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
        have hw : g % L.block / 128 = 1 := by
          have := Nat.mod_lt g (show 0 < L.block by omega)
          omega
        rw [hw]
        have hpc : (thread Q L g).pc (.inr ⟨.inl (.worker w), d⟩, nn) = Proof.WComp.pc d := rfl
        rw [hpc, (Proof.Ledger.w_static d).1] at hq
        have hs := Proof.Ledger.w_req_sched hq
        obtain ⟨hle, -, -, -⟩ := w_req_ph hq
        have hR' : _ + (wPh d).2 = _ + (wPh d).1 := hR
        have hW : _ % 3 = wph d := w1_inv hp hX hg k hlen _ hσ
        rw [wph_wPh (wTo_false hp hX hg hlen hσ)] at hW
        rw [hs]
        simp only [Proof.Bar.regSched, true_and]
        have key : (((X.tr g).take k).countP SetMaxNReg.isRequest) % 3 = (wPh d).1 := by omega
        by_cases h1 : (wPh d).1 = 1
        · have : ((X.tr g).take k).countP SetMaxNReg.isRequest % 3 = 1 := by omega
          simp [h1, this]
        · have : ¬ ((X.tr g).take k).countP SetMaxNReg.isRequest % 3 = 1 := by omega
          simp [h1, this]
    · exact hJ.elim
  b1 := by
    intro g k pc inc n inst hg he hex hpos
    have hb : L.block = 256 := hp.block
    have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    have hpcf := fires_pc hf
    simp only at hpcf
    have hq := (req_iff hc hf).2 _ _ _ _ rfl
    have hR := rq_inv hp hX hg k hlen _ hσ
    -- the request's own counts: one request and one barrier-1 event, or two and three
    have hrc : (Proof.Bar.rqBefore X g k = 1 ∧ Proof.Bar.b1Before X g k = 1) ∨
        (Proof.Bar.rqBefore X g k = 2 ∧ Proof.Bar.b1Before X g k = 3) := by
      unfold Proof.Bar.rqBefore Proof.Bar.b1Before at *
      obtain ⟨x, nn⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · exfalso
        have hne : ∀ r, st.site ≠ .enter r := by
          intro r h'
          have : StartRef st nn := hJ
          unfold StartRef at this
          rw [h'] at this
          exact this
        rw [show reqAt _ = none from (startup_static st.site hne).1] at hq
        cases hq
      · rename_i i'
        cases i' with
        | dp tm bw =>
          rcases d with d | ⟨dt | _, τ⟩
          · exfalso
            have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
            have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, nn) = d.site.pc := rfl
            rw [hpc, (proReq_old d.site hxd).1] at hq
            have hs : d.site = .sMax := by
              by_contra hne; simp [hne] at hq
            have hC : _ = proPh d := c1_inv hp hX hg k hlen _ hσ
            have hR' : _ + (if d.site = .sMax then 0 else if d.site = .exit then 1 else 0) =
                _ + (if d.site = .sMax then 0 else 1) := hR
            simp only [hs, ite_true, proPh, reduceCtorEq, ite_false] at hR' hC
            omega
          · cases τ with
            | sm d =>
              have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, nn) =
                d.site.pc := rfl
              rw [hpc, (Proof.Ledger.sm_static d.site).1] at hq
              have hC : _ = smPh d := c1_inv hp hX hg k hlen _ hσ
              have hR' : _ + (dPh (.sm d)).2 = _ + (dPh (.sm d)).1 := hR
              left
              cases hs : d.site <;> simp_all [Proof.Ledger.smReq, dPh, smPh]
            | epi d =>
              have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, nn) =
                d.site.pc := rfl
              rw [hpc, (Proof.Ledger.epi_static d.site).1] at hq
              have hC : _ = epiPh d := c1_inv hp hX hg k hlen _ hσ
              have hR' : _ + (dPh (.epi d)).2 = _ + (dPh (.epi d)).1 := hR
              right
              cases hs : d.site <;> simp_all [Proof.Ledger.epiReq, dPh, epiPh]
          · exact hJ.elim
        | worker w =>
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.worker w), d⟩, nn) = Proof.WComp.pc d := rfl
          rw [hpc, (Proof.Ledger.w_static d).1] at hq
          obtain ⟨hle, h0, h1, h2⟩ := w_req_ph hq
          have hR' : _ + (wPh d).2 = _ + (wPh d).1 := hR
          rcases (by omega : (wPh d).1 = 0 ∨ (wPh d).1 = 1 ∨ (wPh d).1 = 2) with h | h | h
          · exfalso
            obtain ⟨P, rfl⟩ := h0 h
            apply loop_exempt
            have : pc = Proof.Worker.Site.loop.pc := hpcf
            rw [← this]
            exact hex
          · have hr : isRole d = true := by
              have hT := wTo_false hp hX hg hlen hσ
              cases d with
              | worker ww =>
                obtain ⟨site, P⟩ := ww
                cases site <;> simp_all [wReqS, Proof.Ledger.wReq, wPh, wTo]
              | exit x => simp [wReqS] at hq
              | _ => rfl
            have hcnt := role_count hp hX hg hlen hr hσ
            have hT := wTo_false hp hX hg hlen hσ
            have hw1 : wph d = 1 := by rw [wph_wPh hT, h1 h]
            rw [hw1] at hcnt
            simp only [one_ne_zero, ite_false] at hcnt
            rw [h, h1 h, hcnt] at hR'
            exact .inl ⟨by omega, hcnt⟩
          · have hr : isRole d = true := by
              have hT := wTo_false hp hX hg hlen hσ
              cases d with
              | worker ww =>
                obtain ⟨site, P⟩ := ww
                cases site <;> simp_all [wReqS, Proof.Ledger.wReq, wPh]
              | exit x => simp [wReqS] at hq
              | _ => rfl
            have hcnt := role_count hp hX hg hlen hr hσ
            have hT := wTo_false hp hX hg hlen hσ
            have hw0 : wph d = 0 := by rw [wph_wPh hT, h2 h]
            rw [hw0] at hcnt
            simp only [ite_true] at hcnt
            rw [h, h2 h, hcnt] at hR'
            exact .inr ⟨by omega, hcnt⟩
      · exact hJ.elim
    refine ⟨by omega, by omega, fun h i pc' cnt md _ hbh hord => ?_⟩
    obtain ⟨b1, b2⟩ := bar1_rq hp hX hbh
    omega
  exit := by
    intro h j pc hh hE
    have hb : L.block = 256 := hp.block
    have hlen : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hE).1
    unfold Proof.Bar.b1Before
    by_cases hw : h % L.block < 128
    · obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
        ev_state hp hX hE (fun f h => by cases h)
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
          rcases d with d | ⟨dt | _, τ⟩
          · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
          · cases τ with
            | sm d => exact absurd (sm_special d.site (List.mem_append_right _ hpc)) (by simp)
            | epi d =>
              have hs := epi_special d.site (List.mem_append_right _ hpc)
              have hC : _ = epiPh d := c1_inv hp hX hh j hlen _ hσ
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with hs | hs <;> rw [hC] <;> simp [epiPh, hs]
          · exact hJ.elim
        | worker w =>
          have : 4 ≤ h % L.block / 32 := (tm_inv hp hX hh j hlen _ hσ).2
          omega
      · exact hJ.elim
    · obtain ⟨tm', P', n', hσx⟩ := worker_exit hp hX hE (by omega)
      have hRI : 4 ≤ _ := ri_inv hp hX hh j hlen _ hσx
      omega

/-- **`regAgree`** on the role table. -/
theorem reg_agree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Proof.Safety.RegAgree L X :=
  Proof.Bar.regAgree_of_ledger hX (reg_ledger hp hX)

/-- **`regSync`** on the role table. -/
theorem reg_sync (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Proof.Safety.RegSync L X :=
  Proof.Bar.regSync_of_ledger hp hX (reg_ledger hp hX)

/-! ### `regAligned` -/

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **A request's position and ordinal**: the position is a function of the warp and the
ordinal (`Ledger.reqPcOf`), the ordinal at most 2 in the default partition and 3 in a worker. -/
theorem request_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {inc : Bool} {n inst : Nat}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    pc = Proof.Ledger.reqPcOf (g % L.block / 32) (((X.tr g).take k).countP SetMaxNReg.isRequest) ∧
      (g % L.block < 128 → ((X.tr g).take k).countP SetMaxNReg.isRequest ≤ 2) ∧
      (128 ≤ g % L.block → ((X.tr g).take k).countP SetMaxNReg.isRequest ≤ 3) := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hpcf := fires_pc hf
  simp only at hpcf
  have hq := (req_iff hc hf).2 _ _ _ _ rfl
  have hR := rq_inv hp hX hg k hlen _ hσ
  have hmod := Nat.mod_lt g (show 0 < L.block by omega)
  obtain ⟨x, nn⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hne : ∀ r, st.site ≠ .enter r := by
      intro r h'
      have : StartRef st nn := hJ
      unfold StartRef at this
      rw [h'] at this
      exact this
    rw [show reqAt _ = none from (startup_static st.site hne).1] at hq
    cases hq
  · rename_i i'
    cases i' with
    | dp tm bw =>
      have hdp : g % L.block < 128 := dp_lane k hσ
      have hw : g % L.block / 32 < 4 := by omega
      simp only [Proof.Ledger.reqPcOf, hw, ite_true]
      rcases d with d | ⟨dt | _, τ⟩
      · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
        have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, nn) = d.site.pc := rfl
        rw [hpc, (proReq_old d.site hxd).1] at hq
        have hs : d.site = .sMax := by by_contra hne; simp [hne] at hq
        have hC : _ = proPh d := c1_inv hp hX hg k hlen _ hσ
        have hR' : _ + (if d.site = .sMax then 0 else if d.site = .exit then 1 else 0) =
            _ + (if d.site = .sMax then 0 else 1) := hR
        simp only [hs, ite_true, proPh, reduceCtorEq, ite_false] at hR' hC
        rw [hpcf.trans hpc, hs]
        refine ⟨?_, fun _ => by omega, fun h => by omega⟩
        rw [show ((X.tr g).take k).countP SetMaxNReg.isRequest = 0 by omega]
        rfl
      · cases τ with
        | sm d =>
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .sm d⟩⟩, nn) =
            d.site.pc := rfl
          rw [hpc, (Proof.Ledger.sm_static d.site).1] at hq
          have hs : d.site = .setMaxReg := by
            revert hq; cases d.site <;> simp [Proof.Ledger.smReq]
          have hC : _ = smPh d := c1_inv hp hX hg k hlen _ hσ
          have hR' : _ + (dPh (.sm d)).2 = _ + (dPh (.sm d)).1 := hR
          have hd : dPh (.sm d) = (1, 1) := by simp [dPh, hs]
          have hc1 : smPh d = 1 := by simp [smPh, hs]
          rw [hd] at hR'; rw [hc1] at hC
          rw [hpcf.trans hpc, hs]
          refine ⟨?_, fun _ => by omega, fun h => by omega⟩
          rw [show ((X.tr g).take k).countP SetMaxNReg.isRequest = 1 by omega]
          decide
        | epi d =>
          have hpc : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, .epi d⟩⟩, nn) =
            d.site.pc := rfl
          rw [hpc, (Proof.Ledger.epi_static d.site).1] at hq
          have hs : d.site = .setMaxInc := by
            revert hq; cases d.site <;> simp [Proof.Ledger.epiReq]
          have hC : _ = epiPh d := c1_inv hp hX hg k hlen _ hσ
          have hR' : _ + (dPh (.epi d)).2 = _ + (dPh (.epi d)).1 := hR
          have hd : dPh (.epi d) = (2, 3) := by simp [dPh, hs]
          have hc1 : epiPh d = 3 := by simp [epiPh, hs]
          rw [hd] at hR'; rw [hc1] at hC
          rw [hpcf.trans hpc, hs]
          refine ⟨?_, fun _ => by omega, fun h => by omega⟩
          rw [show ((X.tr g).take k).countP SetMaxNReg.isRequest = 2 by omega]
          decide
      · exact hJ.elim
    | worker w =>
      have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
      have hpc : (thread Q L g).pc (.inr ⟨.inl (.worker w), d⟩, nn) = Proof.WComp.pc d := rfl
      rw [hpc, (Proof.Ledger.w_static d).1] at hq
      have hR' : _ + (wPh d).2 = _ + (wPh d).1 := hR
      have hT := wTo_false hp hX hg hlen hσ
      have hW : _ % 3 = wph d := w1_inv hp hX hg k hlen _ hσ
      rw [wph_wPh hT] at hW
      have hRW : RW Q L g _ := role_warp hp hX hg k hlen _ hσ
      have hRI : RIt d _ := ri_inv hp hX hg k hlen _ hσ
      have hn4 : ¬ g % L.block / 32 < 4 := by omega
      rw [hpcf.trans hpc]
      refine ⟨?_, fun h => by omega, fun _ => ?_⟩
      · simp only [Proof.Ledger.reqPcOf, hn4, ite_false]
        cases d with
        | worker ww =>
          obtain ⟨site, P⟩ := ww
          cases site <;> (try (simp [wTo] at hT; done)) <;>
            simp only [wReqS, Proof.Ledger.wReq, wPh, reduceCtorEq] at hq hR' hW ⊢ <;>
            (split_ifs <;> first | rfl | omega)
        | idle dd =>
          obtain ⟨site, P⟩ := dd
          have h6 : g % L.block / 32 < 6 := hRW
          cases site <;>
            simp only [wReqS, Proof.Ledger.idleReq, wPh, reduceCtorEq] at hq hR' hW ⊢ <;>
            (split_ifs <;> first | rfl | omega)
        | loader dd P =>
          have h6 : g % L.block / 32 = 6 := hRW
          obtain ⟨site, _, _, _, _, _, _⟩ := dd
          cases site <;>
            simp only [wReqS, Proof.Ledger.loaderReq, wPh, reduceCtorEq] at hq hR' hW ⊢ <;>
            (split_ifs <;> first | rfl | omega)
        | mma dd P =>
          have h7 : g % L.block / 32 = 7 := hRW
          obtain ⟨site, _, _, _, _⟩ := dd
          cases site <;>
            simp only [wReqS, Proof.Ledger.mmaReq, wPh, reduceCtorEq] at hq hR' hW ⊢ <;>
            (split_ifs <;> first | rfl | omega)
        | exit x => simp [wReqS] at hq
      · obtain ⟨hle, h0, h1, h2⟩ := w_req_ph hq
        rcases (by omega : (wPh d).1 = 0 ∨ (wPh d).1 = 1 ∨ (wPh d).1 = 2) with h | h | h
        · obtain ⟨P, rfl⟩ := h0 h
          have : _ ≤ 3 := hRI.1 rfl
          simp only [wPh] at hR'
          omega
        · have hw1 := wph_wPh hT
          rw [h1 h] at hw1
          rw [h, h1 h] at hR'
          have hr : isRole d = true := by
            cases d with
            | worker ww =>
              obtain ⟨site, P⟩ := ww
              cases site <;> simp_all [wReqS, Proof.Ledger.wReq, wPh, wTo]
            | exit x => simp [wReqS] at hq
            | _ => rfl
          have hcnt := role_count hp hX hg hlen hr hσ
          split at hcnt <;> omega
        · have hw1 := wph_wPh hT
          rw [h2 h] at hw1
          rw [h, h2 h] at hR'
          have hr : isRole d = true := by
            cases d with
            | worker ww =>
              obtain ⟨site, P⟩ := ww
              cases site <;> simp_all [wReqS, Proof.Ledger.wReq, wPh]
            | exit x => simp [wReqS] at hq
            | _ => rfl
          have hcnt := role_count hp hX hg hlen hr hσ
          split at hcnt <;> omega
  · exact hJ.elim

/-- **An exiting thread's requests**: three in the default partition, at least four in a
worker. -/
theorem exit_requests' (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} (hE : X.get (h, j) = some ⟨pc, .exit⟩) :
    (h % L.block < 128 → 3 ≤ ((X.tr h).take j).countP SetMaxNReg.isRequest) ∧
      (128 ≤ h % L.block → 4 ≤ ((X.tr h).take j).countP SetMaxNReg.isRequest) := by
  have hb : L.block = 256 := hp.block
  have hh := Frame.lt_of_get hX hE
  have hlen : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hE).1
  by_cases hw : h % L.block < 128
  · refine ⟨fun _ => ?_, fun h' => by omega⟩
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hE (fun f h => by cases h)
    have hpc := ret_pc' hc hf rfl
    have hR := rq_inv hp hX hh j hlen _ hσ
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
        rcases d with d | ⟨dt | _, τ⟩
        · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
        · cases τ with
          | sm d => exact absurd (sm_special d.site (List.mem_append_right _ hpc)) (by simp)
          | epi d =>
            have hs := epi_special d.site (List.mem_append_right _ hpc)
            have hC : _ = epiPh d := c1_inv hp hX hh j hlen _ hσ
            have hR' : _ + (dPh (.epi d)).2 = _ + (dPh (.epi d)).1 := hR
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
            rcases hs with hs | hs <;> simp only [dPh, epiPh, hs] at hC hR' <;> omega
        · exact hJ.elim
      | worker w =>
        have : 4 ≤ h % L.block / 32 := (tm_inv hp hX hh j hlen _ hσ).2
        omega
    · exact hJ.elim
  · refine ⟨fun h' => absurd h' hw, fun _ => ?_⟩
    obtain ⟨tm', P', n', hσx⟩ := worker_exit hp hX hE (by omega)
    have hRI : 4 ≤ _ := ri_inv hp hX hh j hlen _ hσx
    have hR : _ + (wPh _).2 = _ + (wPh _).1 := rq_inv hp hX hh j hlen _ hσx
    simp only [wPh] at hR
    omega

/-- **`regAligned`** on the role table. -/
theorem reg_aligned (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ¬ AlignedClass.setMaxReg.Divergent L kernel X ∧ ¬ AlignedClass.setMaxReg.Exited L kernel X := by
  have hb : L.block = 256 := hp.block
  constructor
  · rintro ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, hord, -, hne⟩
    rcases hne with hne | hne
    · simp only [AlignedClass.member, SetMaxNReg.isRequest] at hme hmf
      cases ke <;> simp at hme
      cases kf <;> simp at hmf
      obtain ⟨e1, e2⟩ := e
      obtain ⟨f1, f2⟩ := f
      have h1 := (request_info hp hX he).1
      have h2 := (request_info hp hX hf).1
      have hwarp : e1 % L.block / 32 = f1 % L.block / 32 := hw.2
      have hq : ((X.tr e1).take e2).countP SetMaxNReg.isRequest =
          ((X.tr f1).take f2).countP SetMaxNReg.isRequest := hord
      rw [h1, h2, hwarp, hq] at hne
      exact hne rfl
    · simp [AlignedClass.operands] at hne
  · rintro ⟨⟨e1, e2⟩, ⟨f1, f2⟩, ev, hpart, he, hme, -, hshort⟩
    obtain ⟨⟨pc, hfx⟩, hcount⟩ := hshort
    obtain ⟨pe, ke⟩ := ev
    simp only [AlignedClass.exitMember, AlignedClass.member, SetMaxNReg.isRequest] at hme
    cases ke <;> simp at hme
    obtain ⟨-, h1a, h1b⟩ := request_info hp hX he
    obtain ⟨h2a, h2b⟩ := exit_requests' hp hX hfx
    have hg : (e1 % L.block) / 32 / 4 = (f1 % L.block) / 32 / 4 := hpart.2
    have hk : ((X.tr e1).take e2).countP SetMaxNReg.isRequest = ((X.tr e1).take e2).countP
        (AlignedClass.exitMember kernel AlignedClass.setMaxReg) := rfl
    rw [← hk] at hcount
    simp only at hcount
    have hme1 := Nat.mod_lt e1 (show L.block > 0 by omega)
    have hmf1 := Nat.mod_lt f1 (show L.block > 0 by omega)
    have hle : ((X.tr f1).take f2).countP SetMaxNReg.isRequest ≤
        (X.tr f1).countP (AlignedClass.exitMember kernel AlignedClass.setMaxReg) :=
      (List.take_sublist f2 (X.tr f1)).countP_le (p := SetMaxNReg.isRequest)
    by_cases hd : e1 % L.block < 128
    · have := h1a hd
      have := h2a (by omega)
      omega
    · have := h1b (by omega)
      have := h2b (by omega)
      omega

end
end PTX.Kernels.InklingRelDecode.Proof2
