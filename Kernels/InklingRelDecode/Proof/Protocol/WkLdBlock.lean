-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WkLdEnd
public import Kernels.InklingRelDecode.Proof.Protocol.LpKv
public import Kernels.InklingRelDecode.Proof.Lib.KvSingle
public import Kernels.InklingRelDecode.Proof.Interface.LpPreProof
public import Kernels.InklingRelDecode.Proof.Interface.WySoft
public import Lemmas.Protocol.NotifyBlocker

@[expose] public section

/-!
# Who blocks a loader lane's poll of `kv_empty`

`kv_empty s` of CTA `c` is a commit object (`MbarRing.Notify.Obj`) of the CTA's committing MMA
lane, polled with offset `1 - δ` (`δ = 1` when the prologue preloads the slot): `emptyObj`, from
the slot's hypotheses `Ring.Kv.Hyp` (`kvSlot`, as `Lp.kv_of`, with the arrival thread and `δ`
named). Its reuse paths hold for **every** lane `h` of the loader warp, not only for lane 0
(`unit_reach`, `emptyReach`): the notification of the MMA lane's commit with `t` earlier ones
follows `h`'s successful poll with `q` earlier ones whenever `q + δ ≤ t`. The path is `h`'s poll,
lane 0's arrival on `kv_ready s` of use `q + δ` (`lane_rdv`, through the warp barrier `wb0`),
the MMA lane's poll of `kv_ready s` for that use, which observes the arrival
(`MbarRing.Items.Ring.observes_full` of `Ring.Kv.ring`), its commit of use `t`, and the commit's
notification.

`loader_empty_blocked`: a loader lane at its poll of `kv_empty (i % 3)` at the end of its trace,
when the object's final phase has the poll's parity, finds the MMA lane short: it has made at
most `i / 3 - 1` commits to the slot, i.e. not the commit of block `i - 3`; or a commit's
notification is undelivered (an open `.commit` obligation). This is
`MbarRing.Notify.Obj.blocker`, except at the first poll of a slot the prologue does not preload,
where the parity is excluded: no notification can precede that poll (`unit_reach` with `q = 0`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite ldThread)
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The KV slot `s` of CTA `c`** under `Ring.Kv.Hyp`, with its arrival thread and its preloaded
use named (`Lp.kv_of`). -/
theorem kvSlot (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (G : Sr.SrPkg L kernel asms mem0 X) {c s : Nat} (hc : c < L.grid) (hs : s < 3) :
    ∃ S : Ring.Kv.Slot, S.full = kvReady L c s ∧ S.empty = kvEmpty L c s ∧ S.cm = G.cm c ∧
      S.ap = ldThread L c ∧ S.δ = (if s < Lp.npOf Q L c then 1 else 0) ∧
      Ring.Kv.Hyp L kernel asms X S := by
  obtain ⟨pArr, pCp, hP⟩ := Lp.preRing_of hpre hX hf c hc s hs
  exact ⟨Lp.slotOf Q L X c s (G.cm c) pArr pCp, rfl, rfl, rfl, rfl, rfl,
    Lp.slot_hyp hpre hX hf hR hp G hc hs hP⟩

/-- **`kv_empty` is a commit object** of the slot's consumer, polled with offset `1 - δ`. -/
theorem emptyObj {S : Ring.Kv.Slot} (H : Ring.Kv.Hyp L kernel asms X S) :
    MbarRing.Notify.Obj X S.empty S.cm S.empty (1 - S.δ) :=
  { src := fun r hr => by
      cases H.empty_src r hr with
      | init ha => exact .init ha
      | poll hid he ha => exact .poll hid he ha
      | notify hid he hm htg ha _ => exact .commit hid he hm htg ha
    init := H.empty_init
    noInval := H.empty_noInval
    parityOf := fun _ he => H.empty_parity he
    δ_le := by omega }

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
include hpre hX hf hR hp

/-- **A loader lane's poll precedes the later notifications of `kv_empty`.** For a counted
notification of use `t` of the slot and `q + δ ≤ t`, lane `h`'s successful poll of `kv_empty s`
with `q` earlier ones precedes it in the dependency order. -/
theorem lane_note {c s : Nat} (hc : c < L.grid) (hs : s < 3) {S : Ring.Kv.Slot}
    (H : Ring.Kv.Hyp L kernel asms X S) (hfull : S.full = kvReady L c s)
    (hempty : S.empty = kvEmpty L c s) (hap : S.ap = ldThread L c) {h : Nat}
    (hsw : SameWarp L h (ldThread L c)) {y : Fin 1 × Nat} (hy : y ∈ Ring.Kv.SE X S) {q : Nat}
    (hq : q + S.δ ≤ y.2) :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h, MbarRing.Poll.nth X S.empty h q), true) (Ring.Kv.note X S y.1 0 y.2, false) := by
  have hδ := H.δ_le
  have gM := Ring.Kv.guardM H hy (j := q + S.δ) hq
  have hw : X.RefPresent (.thread (Ring.Kv.wF X S y.1 (q + S.δ))) :=
    MbarRing.Round.Slot.present_of_guard gM
  obtain ⟨hx, hwit⟩ := (Ring.Kv.ring hX H).observes_full hX.depAcyclic (b := y.1) hw
    (⟨0, by decide⟩ : Fin 9)
  have hx' : ((⟨0, by decide⟩ : Ring.Kv.Kind), q + S.δ) ∈ Ring.Kv.SF X S := hx
  have hiF := Ring.Kv.issueF hX H hx'
  obtain ⟨-, ⟨e, he⟩, -⟩ := Ring.Kv.SF_op H hx'
  have hpred := Ring.Kv.SF_pred H hx' he
  have hop : Ring.Kv.opF X S ⟨0, by decide⟩ (q + S.δ) =
      (S.ap, nthEv X (arrivesOn S.full) S.ap q) := by
    rw [Ring.Kv.opF_ld (by omega)]
    simp [Ring.Kv.kOwner, Ring.Kv.Slot.prod, Ring.Kv.kPred, Ring.Kv.kIdx]
  rw [hop] at he
  rw [Ring.Kv.kPred_zero] at hpred
  obtain ⟨tx, cnt, rel, sc, hk⟩ := arrivesOn_form hpred
  have hcount := (nthEv_spec_of_get he).2
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  rw [hap, hfull] at he
  rw [hap, hfull] at hcount
  have hlane := lane_rdv hpre hX hf hR hp hc hs hsw he
  have harr : arrivals (kvReady L c s)
      ((X.tr (ldThread L c)).take (nthEv X (arrivesOn (kvReady L c s)) (ldThread L c) q)) = q :=
    hcount
  rw [harr, ← hempty] at hlane
  have h1 : Relation.TransGen (DepStep L kernel X)
      (.thread (h, MbarRing.Poll.nth X S.empty h q), true)
      (.thread (Ring.Kv.opF X S ⟨0, by decide⟩ (q + S.δ)), false) := by
    rw [hop, hap, hfull]
    exact hlane
  exact (((h1.trans_left hiF).tail (DepStep.of_witness L hwit)).tail
    (DepStep.of_resumes L gM)).trans_left (Ring.Kv.issueE hX H hy)

/-- **The reuse paths of `kv_empty` for every loader lane**, numbered by the commit object's
units. -/
theorem unit_reach {c s : Nat} (hc : c < L.grid) (hs : s < 3) {S : Ring.Kv.Slot}
    (H : Ring.Kv.Hyp L kernel asms X S) (hfull : S.full = kvReady L c s)
    (hempty : S.empty = kvEmpty L c s) (hap : S.ap = ldThread L c) {h : Nat}
    (hsw : SameWarp L h (ldThread L c)) {x : Fin 1 × Nat}
    (hx : x ∈ MbarRing.Notify.S X S.empty S.cm S.empty) {q : Nat} (hq : q + S.δ ≤ x.2) :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h, MbarRing.Poll.nth X S.empty h q), true)
      (MbarRing.Notify.it X S.empty S.cm S.empty x.2, false) := by
  obtain ⟨⟨k, r, hk, hid, hf0, ha⟩, -, -, -, -, -, hc0⟩ := (emptyObj H).S_rec hx
  obtain ⟨-, y, hy, hyid⟩ := Ring.Kv.empty_item H (List.mem_of_getElem? hk) hf0 ha
  obtain ⟨-, ⟨pc, sp, hey, -, -, hcy⟩, -⟩ := Ring.Kv.SE_op H hy
  have heq : MbarRing.Notify.it X S.empty S.cm S.empty x.2 = Ring.Kv.note X S y.1 0 y.2 :=
    hid.symm.trans hyid
  have hpos : MbarRing.Notify.cm X S.cm S.empty x.2 = (Ring.Kv.cmE X S y.1 y.2).2 := by
    simp only [MbarRing.Notify.it, Ring.Kv.note, Ring.Kv.cmE, Ref.async.injEq,
      Prod.mk.injEq] at heq
    exact heq.1.2
  have hxy : x.2 = y.2 := by rw [← hc0, ← hcy, hpos]
  rw [heq]
  exact lane_note hpre hX hf hR hp hc hs H hfull hempty hap hsw hy (by omega)

/-- **`Notify.Reach` of `kv_empty` for every loader lane.** -/
theorem emptyReach {c s : Nat} (hc : c < L.grid) (hs : s < 3) {S : Ring.Kv.Slot}
    (H : Ring.Kv.Hyp L kernel asms X S) (hfull : S.full = kvReady L c s)
    (hempty : S.empty = kvEmpty L c s) (hap : S.ap = ldThread L c) {h : Nat}
    (hsw : SameWarp L h (ldThread L c)) :
    MbarRing.Notify.Reach L kernel asms X S.empty S.cm S.empty (1 - S.δ) h := by
  have hδ := H.δ_le
  intro x hx j hj
  exact unit_reach hpre hX hf hR hp hc hs H hfull hempty hap hsw hx (by omega)

/-- **Who blocks a loader lane at its poll of `kv_empty`.** A loader lane at its poll of
`kv_empty (i % 3)` at the end of its trace, whose object's final phase has the poll's parity:
the CTA's committing MMA lane has made at most `i / 3 - 1` commits to it, or a commit's
notification is undelivered. -/
theorem loader_empty_blocked (G : Sr.SrPkg L kernel asms mem0 X) (hg : g < L.threads)
    {d : Loader.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.loader d P)))) {m : Loc} {par : Nat}
    (hat : PollAt L g (.w (.loader d P)) m par) {before : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = par % 2) :
    (X.tr (G.cm (g / L.block))).countP (commitsTo m) + 1 ≤ d.i / 3 ∨
      Descent.Obl L X .commit := by
  obtain ⟨hws, rfl, rfl⟩ := hat
  set c := g / L.block with hcdef
  have hb : L.block = 256 := hpre.block
  have hc : c < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hs : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  obtain ⟨S, hfull, hempty, hcm, hap, hδS, H⟩ := kvSlot hpre hX hf hR hp G hc hs
  -- the lane is in the loader warp of its CTA
  have h6 := roleWarp_inv hf.roleWarp _ _ le_rfl hσ
  simp only [RoleWarp, roleWarp] at h6
  obtain ⟨hlt, hlc, hl192⟩ := Lp.ldThread_props hb hc
  have hsw : SameWarp L g (ldThread L c) :=
    ⟨⟨hg, hlt, by rw [hlc]⟩, by rw [hl192]; omega⟩
  -- the lane's successful polls
  have hnp : ¬ PreSite d.site := by rw [hws]; rintro (h | h | h) <;> cases h
  have hcnt := ld_polls_le hpre hX hf hR hp le_rfl hσ hnp (by rw [hws]; nofun) _ hs
  rw [List.take_length] at hcnt
  have hpo : Ring.Ld.polled d = d.i := by simp [Ring.Ld.polled, Ring.Ld.afterWait, hws]
  rw [hpo, Ring.below_of_slot hs rfl, Ring.below_small hs (Lp.numPre_le _ _ _)] at hcnt
  have hcnt2 : okPolls (kvEmpty L c (d.i % 3)) (X.tr g) +
      (if d.i % 3 < Lp.npOf Q L c then 1 else 0) = d.i / 3 := hcnt
  rw [← hδS, ← hempty] at hcnt2
  -- the commit object
  have O := emptyObj H
  have hδ := H.δ_le
  rw [← hempty] at hst ⊢
  rw [← hcm]
  have hR' := emptyReach hpre hX hf hR hp hc hs H hfull hempty hap hsw
  have hff : ∀ r ∈ X.objects S.empty, r.fault = none := fun r hr =>
    Ring.Kv.fault_free hX H (.inr rfl) hr
  have htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec}, X.get (S.cm, i) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = S.empty → ∃ rank, TcCommit.target sp rank = some S.empty := by
    intro i pc sp he hmb
    obtain ⟨rank, hr⟩ := commit_target_self hpre hX hf he
    exact ⟨rank, hmb ▸ hr⟩
  set P0 := okPolls S.empty (X.tr g) with hP0
  have hcnt' : P0 + S.δ = d.i / 3 := hcnt2
  by_cases hle : 1 - S.δ ≤ P0
  · have hpar' : before.phase % 2 = (P0 + (1 - S.δ)) % 2 := by omega
    obtain ⟨hph, hk⟩ := O.blocker hX hR' hff htgt hst hpar' hle
    rcases hk with h1 | h1
    · exact .inl (by omega)
    · exact .inr h1
  · -- the first poll of a slot the prologue does not preload: no notification precedes it
    exfalso
    have hP00 : P0 = 0 := by omega
    have hδ0 : S.δ = 0 := by omega
    have hodd : before.phase % 2 = 1 := by omega
    have hunits := O.units_eq_phase hX hst
    rw [O.units_eq_card] at hunits
    have hpos : 0 < ((Finset.range (X.objects S.empty).length).filter
        fun k => ((X.objects S.empty)[k]?).any MBarrier.countedArrive = true).card := by omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
    obtain ⟨-, hka⟩ := Finset.mem_filter.mp hk
    cases hr : (X.objects S.empty)[k]? with
    | none => rw [hr] at hka; cases hka
    | some r =>
      rw [hr, Option.any_some] at hka
      obtain ⟨hf0, c', tx, ha⟩ := MBarrier.countedArrive_iff.mp hka
      obtain ⟨x, hx, -⟩ := O.rec_S hr hf0 ha
      have hpath := unit_reach hpre hX hf hR hp hc hs H hfull hempty hap hsw hx (q := 0)
        (by omega)
      obtain ⟨c0, hc0, -⟩ := Relation.TransGen.head'_iff.mp hpath
      have := MbarRing.Poll.nth_present.mp hc0.present_of_return
      omega

end

end
end PTX.Kernels.InklingRelDecode.Proof.Wk
