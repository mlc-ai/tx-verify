-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvLead
public import Kernels.InklingRelDecode.Proof2.Safety.GlobalW
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSmWait

@[expose] public section

/-! # The events on the KV ring's barriers, by the state that fires them

The ring's barriers lie at `sharedBase + 213216 … 213272` of a CTA (`InRing`): `kv_ready s` and
`kv_empty s`; the kernel's other barriers (`s_ready`, `p_ready`, `o_done`, `o_final`) above.
From the role table:

* `arrive_ring`: an arrival on a ring barrier is on `kv_ready s` of the thread's CTA, of 65536
  bytes and count 1, by lane 0 of warp 6 within its budget (`kc_inv`), or by thread 0 at the
  prologue's arrival of a preloaded slot (`s < num_pre`), its first on the barrier (`pci_inv`);
* `copy_ring_ev`: a copy completing on a ring barrier is of 8192 bytes, on `kv_ready s`, by the
  warp-6 lane that leads its elections within its budget, or a prologue copy of a preloaded slot
  by the elected lane of warp 0 or 1, at most its fourth on the barrier;
* `commit_ring`: a commit notifying a ring barrier is the MMA warp's PV commit on `kv_empty s`,
  by the warp-7 lane that leads its elections, within its budget;
* `wait_ring`: a poll of `kv_empty s` is a loader lane's and a poll of `kv_ready s` an MMA lane's,
  acquiring at CTA scope, with the parity of the poller's earlier successful polls. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A byte range of a CTA's ring barriers. -/
def InRing (L : Launch) (m : Loc) : Prop :=
  m.space = .shared ∧ L.sharedBase + 213216 ≤ m.addr ∧ m.addr < L.sharedBase + 213272

theorem inRing_kvReady (c : Nat) {s : Nat} (hs : s < 3) :
    InRing L (Proof.EvW.kvReady L c s) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [Proof.EvW.kvReady, Proof.EvW.barLoc, Proof.EvW.kvReadyOff] <;>
    omega

theorem inRing_kvEmpty (c : Nat) {s : Nat} (hs : s < 3) :
    InRing L (Proof.EvW.kvEmpty L c s) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff] <;>
    omega

theorem kvReady_ne_kvEmpty {c c' s s' : Nat} (hs : s < 3) (hs' : s' < 3) :
    Proof.EvW.kvReady L c s ≠ Proof.EvW.kvEmpty L c' s' := by
  simp only [Proof.EvW.kvReady, Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvReadyOff,
    Proof.EvW.kvEmptyOff, ne_eq, Loc.mk.injEq, true_and, not_and]
  omega

/-! ### The prologue's arrival and copies: thread and block -/

/-- **The prologue's arrival of block `b`** is thread 0's, for a block below `num_pre`, and the
thread's first arrival on the barrier. -/
theorem pro_arr_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    {b : Fin 3} (hs : d.site = .arr b) :
    g % L.block = 0 ∧ b.val < npOf Q L g ∧
      arrivals (Proof.EvW.kvReady L (g / L.block) b) ((X.tr g).take k) = 0 := by
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
  have hold : d.site.old = Proof.ProA.arrSite b.val := by rw [hs]; exact arr_old b
  have hnm : Proof.ProA.arrSite b.val ≠ .sMax ∧ Proof.ProA.arrSite b.val ≠ .ldCu0 ∧
      (Proof.ProA.arrSite b.val).afterSk = true := by
    fin_cases b <;> decide
  obtain ⟨w0, w1, w2⟩ := hR.words
  have hdold : (ProA.D.old d).site = Proof.ProA.arrSite b.val := hold
  rw [hdold] at w0 w1 w2
  have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) d.dt :=
    ⟨w0 hnm.1 hnm.2.1, w1 (.inl hnm.2.2), w2 hnm.2.2⟩
  have hG := hR.gate
  rw [hold] at hG
  have hnp := Proof.ProA.numPre_of_gate hp hg ha hw hm hG (Proof.ProA.arr_blk b.val b.isLt)
  have hguard : Proof.ProA.v_p177 L g d.dt = true := by
    have := hi.1.guard
    simp only [ProA.D.old, hold] at this
    fin_cases b <;> exact this
  have h0 := Proof.ProA.tid_of_p177 hi.1.args.tid hguard
  refine ⟨h0, hnp, ?_⟩
  have hP : _ := pci_inv hp hX hg k hlen _ hσ
  obtain ⟨h1, -⟩ := hP b.val b.isLt
  rw [hs, arr_pcB] at h1
  simp only [lt_irrefl, ite_false] at h1
  omega

/-- **A prologue copy of block `b`** is of a block below `num_pre`, by an elected lane of warp 0
or 1, and at most the thread's fourth copy to the barrier. -/
theorem pro_ptc_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    {b : Fin 3} {j : Fin 4} (hs : d.site = .ptc b j) :
    b.val < npOf Q L g ∧ Elected (X.tr g) (laneOf L g) ∧ g % L.block < 64 ∧
      ((X.tr g).take k).countP (issuesTo (Proof.EvW.kvReady L (g / L.block) b)) < 4 := by
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
  have hmem : ∀ i < 12, (Proof.ProA.ptcSite i).afterSk = true ∧
      Proof.ProA.ptcSite i ≠ .sMax ∧ Proof.ProA.ptcSite i ≠ .ldCu0 := by
    intro i hi; interval_cases i <;> decide
  obtain ⟨hb3, hn1, hn2⟩ := hmem _ hi12
  obtain ⟨w0, w1, w2⟩ := hR.words
  have hdold : (ProA.D.old d).site = Proof.ProA.ptcSite (4 * b.val + j.val) := hold
  rw [hdold] at w0 w1 w2
  have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) d.dt :=
    ⟨w0 hn1 hn2, w1 (.inl hb3), w2 hb3⟩
  have hG := hR.gate
  rw [hold] at hG
  have hnp := Proof.ProA.numPre_of_gate hp hg ha hw hm hG
    (Proof.ProA.ptc_blk (4 * b.val + j.val) hi12)
  have hb4 : (4 * b.val + j.val) / 4 = b.val := by omega
  rw [hb4] at hnp
  obtain ⟨hel, h64⟩ := pro_ptc_elected hp hX hg hlen.le hσ ⟨b, j, hs⟩
  refine ⟨hnp, hel, h64, ?_⟩
  obtain ⟨-, h2⟩ := pci_inv hp hX hg k hlen _ hσ b.val b.isLt
  rw [hs] at h2
  have : (ptcPcsB b.val).countP (· < (ProA.Site.ptc b j).pc) < 4 := by
    fin_cases b <;> fin_cases j <;> decide
  omega

/-! ### The sites at the ring's event positions -/

local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_arr : ∀ s : Startup.Site, s.pc ∈ arrPcs → False := by
  intro s h; revert h; cases s with
  | enter r => cases r <;> decide
  | _ => decide
theorem sm_arr : ∀ s : Proof.Sm.Site, s.pc ∈ arrPcs → s = .arrive := by site_cls
theorem epi_arr : ∀ s : Proof.Epi.Site, s.pc ∈ arrPcs → False := by site_cls
theorem worker_arr : ∀ s : Proof.Worker.Site, s.pc ∈ arrPcs → False := by site_cls
theorem idle_arr : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ arrPcs → False := by site_cls
theorem loader_arr : ∀ s : Proof.Loader.Site, s.pc ∈ arrPcs → s = .arrive := by site_cls
theorem mma_arr : ∀ s : Proof.Mma.Site, s.pc ∈ arrPcs → False := by site_cls
theorem exitsite_arr : ∀ s : Proof.WComp.ExitSite, s.pc ∈ arrPcs → False := by site_cls

theorem pReady_notRing {c : Nat} (b : Proof.EvD.Bar) (hb : ∃ i, b = .pReady i) :
    ¬ InRing L (b.loc L c) := by
  obtain ⟨i, rfl⟩ := hb
  simp only [InRing, Proof.EvD.Bar.loc, Proof.EvD.Bar.off, not_and, not_lt]
  intro _ _; omega

/-- A loader thread's lane-0 lanes are thread 192 of the CTA. -/
theorem loader_lane0 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {tm : Value}
    {d : Proof.Loader.D} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n)))
    (hI : Proof.Loader.Inv L g d) (hs : d.site = .arrive) : g % L.block = 192 := by
  have hb : L.block = 256 := hp.block
  have h6 : g % L.block / 32 = 6 := role_warp hp hX hg k hk _ hσ
  have hln := hI.lane hs
  rw [hI.ln] at hln
  have h0 : laneOf L g = 0 := by simpa using hln
  simp only [laneOf] at h0
  omega

/-- **A state that uses the ring after the publication of its barriers**: a prologue state after
`bar2` (position 180), or a loader or MMA state. -/
def UserAt (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  (∃ tm bw d n, Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)) ∧ 180 < d.site.pc) ∨
  (∃ tm d P n, Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .loader d P⟩, n))) ∨
  (∃ tm d P n, Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)))

/-- **An arrival on a ring barrier.** -/
theorem arrive_ring (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {mo : Loc} {tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive mo tx cnt rel sc⟩) (hr : InRing L mo) :
    (tx = 65536 ∧ cnt = 1 ∧ ∃ s < 3, mo = Proof.EvW.kvReady L (g / L.block) s ∧
      ((g % L.block = 192 ∧ arrivals (Proof.EvW.kvReady L (g / L.block) s) ((X.tr g).take k) + 1 ≤
          okPolls (Proof.EvW.kvEmpty L (g / L.block) s) ((X.tr g).take k)) ∨
        (g % L.block = 0 ∧ s < npOf Q L g ∧
          arrivals (Proof.EvW.kvReady L (g / L.block) s) ((X.tr g).take k) = 0))) ∧
      UserAt Q L X g k := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := arr_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_arr st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
          rcases pro_ev_kv hp (hJ : ProRef Q L g tm bw d n) hat hi.1 hxd hc hf with
            ⟨b, hs, hk⟩ | ⟨b, j, hs, a, sp, hk, -⟩ | ⟨hna, -⟩
          · simp only [Kind.arrive.injEq] at hk
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
            obtain ⟨h0, hnp, hc0⟩ := pro_arr_info hp hX he hσ hs
            exact ⟨⟨rfl, rfl, b.val, b.isLt, rfl, .inr ⟨h0, hnp, hc0⟩⟩,
              .inl ⟨tm, bw, d, n, hσ, by rw [hs]; fin_cases b <;> decide⟩⟩
          · cases hk
          · exact absurd rfl (hna _ _ _ _ _)
        · exfalso
          cases τ with
          | sm d =>
            have hs := sm_arr d.site hpc
            have h' : Proof.Sm.Shape L g d ⟨pc, .arrive mo tx cnt rel sc⟩ := hev
            simp only [Proof.Sm.Shape, hs] at h'
            obtain ⟨-, h'⟩ := h'
            simp only [Event.mk.injEq, Kind.arrive.injEq] at h'
            obtain ⟨-, rfl, -⟩ := h'
            exact pReady_notRing _ ⟨_, rfl⟩ hr
          | epi d => exact epi_arr d.site hpc
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_arr d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          simp only [Proof.EvW.LdShape, hs, Event.mk.injEq, Kind.arrive.injEq] at hsh
          obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := hsh
          have hI : Proof.Loader.Inv L g d := (hi : Proof.WComp.Inv L g (.loader d P)).1
          have h192 := loader_lane0 hp hX hg hlen hσ hI hs
          have hK : LdCnt Q L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
          have hin : d.site.inLoop = true := by rw [hs]; rfl
          have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
          have hA := hK.A hin _ hm3
          have hP := hK.P hin _ hm3
          simp only [hs, arrivedS, polledS, Bool.false_eq_true, false_and, ite_false, true_and,
            ite_true] at hA hP
          exact ⟨⟨rfl, rfl, d.i % 3, hm3, rfl, .inl ⟨h192, by omega⟩⟩, .inr (.inl ⟨w, d, P, n, hσ⟩)⟩
        | worker w => exact (worker_arr w.site hpc).elim
        | idle d => exact (idle_arr d.site hpc).elim
        | mma d P => exact (mma_arr d.site hpc).elim
        | exit x => exact (exitsite_arr x.site hpc).elim
    · exact hJ.elim

theorem loader_cp_site : ∀ s : Proof.Loader.Site, s.pc ∈ copyPcs → isCpS s = true := by site_cls

/-- **A copy completing on a barrier** is on `kv_ready s` of the thread's CTA, of 8192 bytes: the
loader's, by the warp-6 lane that leads its elections, within its budget, or the prologue's of a
preloaded slot, by the elected lane of warp 0 or 1, at most its fourth on the barrier. -/
theorem copy_ring_ev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc a : Nat} {sp : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    (TensorTransfer.bytes sp.descriptor = 8192 ∧ ∃ s < 3,
      sp.mbar = Proof.EvW.kvReady L (g / L.block) s ∧
      (∀ x y z l, TensorCopy.writeLoc sp x y z = some l → l.space = .shared ∧
        l.cta = g / L.block ∧ InSlot L s l.addr) ∧
      ((g = leadT L X (g / L.block) 6 ∧
          ((X.tr g).take k).countP (issuesTo (Proof.EvW.kvReady L (g / L.block) s)) + 1 ≤
            8 * okPolls (Proof.EvW.kvEmpty L (g / L.block) s) ((X.tr g).take k)) ∨
        (s < npOf Q L g ∧ g % L.block / 32 < 2 ∧ g = leadT L X (g / L.block) (g % L.block / 32) ∧
          ((X.tr g).take k).countP (issuesTo (Proof.EvW.kvReady L (g / L.block) s)) < 4))) ∧
      UserAt Q L X g k := by
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
        · have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
          rcases pro_ev_kv hp (hJ : ProRef Q L g tm bw d n) hat hi.1 hxd hc hf with
            ⟨b, hs, hk⟩ | ⟨b, j, hs, a', sp', hk, hsp, hby, hreg⟩ | ⟨-, hnc⟩
          · cases hk
          · simp only [Kind.tensorIssue.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            obtain ⟨hnp, hel, h64, hc4⟩ := pro_ptc_info hp hX he hσ hs
            exact ⟨⟨hby, b.val, b.isLt, hsp, hreg, .inr ⟨hnp, by omega, (leadT_eq hX hg hel).symm,
              hc4⟩⟩,
              .inl ⟨tm, bw, d, n, hσ, by rw [hs]; fin_cases b <;> fin_cases j <;> decide⟩⟩
          · exact absurd rfl (hnc _ _)
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
          obtain ⟨bx, hbx, hk⟩ := hev
          simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hk
          obtain ⟨-, -, rfl⟩ := hk
          have hreg : ∀ x y z l, TensorCopy.writeLoc (Proof.EvW.ldCopy Q L g d bx) x y z =
              some l → l.space = .shared ∧ l.cta = g / L.block ∧ InSlot L (d.i % 3) l.addr := by
            intro x y z l hl
            unfold Proof.EvW.ldCopy at hl
            obtain ⟨h1, h2, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q _ _ _ _ _ hl
            refine ⟨h1, h2, ?_⟩
            unfold Proof.EvW.ldDst at h3 h4
            obtain ⟨v, sl, hh⟩ := bx
            have hb' : sl ≤ 1 ∧ hh ≤ 1 := by
              cases hsite : d.site <;> rw [hsite] at hbx <;> simp [Proof.EvW.ldBox] at hbx <;>
                omega
            unfold InSlot
            cases v <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h3 h4 <;>
              [left; right] <;> constructor <;> omega
          have hel := ld_cp_elected hp hX hg k hlen.le _ hσ hs
          have h6 : g % L.block / 32 = 6 := role_warp hp hX hg k hlen _ hσ
          have hlead := leadT_eq hX hg hel
          rw [h6] at hlead
          have hK : LdCnt Q L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
          have hin : d.site.inLoop = true := by
            cases hst : d.site <;> rw [hst] at hs <;> first | (simp [isCpS] at hs; done) | rfl
          have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
          have hC := hK.C hin _ hm3
          have hP := hK.P hin _ hm3
          have hpol : polledS d.site = true := by
            cases hst : d.site <;> rw [hst] at hs <;> first | (simp [isCpS] at hs; done) | rfl
          have hcd : cpDoneS d.site ≤ 7 := by
            cases hst : d.site <;> simp [cpDoneS]
          simp only [hpol, true_and, ite_true] at hC hP
          refine ⟨⟨kvCopy_bytes _ _ _ _ _ _, d.i % 3, hm3, rfl, hreg, .inl ⟨hlead.symm, ?_⟩⟩,
            .inr (.inl ⟨w, d, P, n, hσ⟩)⟩
          show _ + 1 ≤ 8 * okPolls _ _
          rw [hP]; omega
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

/-! ### Commits -/

theorem target_commitSpec {c : Nat} {l mo : Loc} {r : Fin 16}
    (h : TcCommit.target (Proof.EvW.commitSpec c l) r = some mo) :
    r.val = 0 ∧ mo = ⟨.shared, c, l.addr⟩ := by
  unfold TcCommit.target at h
  split at h
  · rename_i hr
    simp only [Proof.EvW.commitSpec, Option.some.injEq] at h hr
    have hr0 : r.val = 0 := by omega
    refine ⟨hr0, ?_⟩
    rw [← h, hr0]
    rfl
  · cases h

theorem startup_commit : ∀ s : Startup.Site, s.pc ∈ commitPcs → False := by
  intro s h; revert h; cases s with
  | enter r => cases r <;> decide
  | _ => decide
theorem proA_commit (s : ProA.Site) (h : s.pc ∈ commitPcs) : False := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j => revert h; revert j; revert b; decide
  | _ => revert h; decide
theorem sm_commit : ∀ s : Proof.Sm.Site, s.pc ∈ commitPcs → False := by site_cls
theorem epi_commit : ∀ s : Proof.Epi.Site, s.pc ∈ commitPcs → False := by site_cls
theorem worker_commit : ∀ s : Proof.Worker.Site, s.pc ∈ commitPcs → False := by site_cls
theorem idle_commit : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ commitPcs → False := by site_cls
theorem loader_commit : ∀ s : Proof.Loader.Site, s.pc ∈ commitPcs → False := by site_cls
theorem exitsite_commit : ∀ s : Proof.WComp.ExitSite, s.pc ∈ commitPcs → False := by site_cls
theorem mma_commit : ∀ s : Proof.Mma.Site, s.pc ∈ commitPcs →
    s = .qkCommit ∨ s = .pvCommit1 ∨ s = .pvCommit2 ∨ s = .finCommit := by site_cls

/-- **A commit notifying a ring barrier** is the MMA warp's PV commit on `kv_empty s`, by the
warp-7 lane that leads its elections, at rank 0, within its budget. -/
theorem commit_ring (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {sp : TcCommit.Spec} (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    {r : Fin 16} {mo : Loc} (ht : TcCommit.target sp r = some mo) (hr : InRing L mo) :
    (g = leadT L X (g / L.block) 7 ∧ r.val = 0 ∧ ∃ s < 3,
      mo = Proof.EvW.kvEmpty L (g / L.block) s ∧ sp.mbar = mo ∧
      ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
        okPolls (Proof.EvW.kvReady L (g / L.block) s) ((X.tr g).take k)) ∧
      UserAt Q L X g k := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := commit_pc hc hf rfl
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r', d⟩
    · exact (startup_commit st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        exfalso
        rcases d with d | ⟨_ | _, τ⟩
        · exact proA_commit d.site hpc
        · cases τ with
          | sm d => exact sm_commit d.site hpc
          | epi d => exact epi_commit d.site hpc
        · exact hJ.elim
      | worker w =>
        cases d with
        | mma d P =>
          have hsh : Proof.EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩ := hev
          have hI : Proof.Mma.Inv d := (hi : Proof.WComp.Inv L g (.mma d P)).1
          rcases mma_commit d.site hpc with hs | hs | hs | hs <;>
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.tc.injEq,
              TcKind.commit.injEq] at hsh <;> obtain ⟨-, rfl⟩ := hsh <;>
            obtain ⟨hr0, rfl⟩ := target_commitSpec ht
          · exfalso
            simp only [InRing, Proof.EvW.sReady, Proof.EvW.barLoc, Proof.EvW.sReadyOff] at hr
            omega
          · -- the PV half's first commit
            have hel := mm_pv_elected hp hX hg k hlen.le _ hσ
              (by show isPvS d.site = true; rw [hs]; rfl)
            have h7 : g % L.block / 32 = 7 := role_warp hp hX hg k hlen _ hσ
            have hlead := leadT_eq hX hg hel
            rw [h7] at hlead
            have hK : MmCnt L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
            have hin : iterS d.site = true := by rw [hs]; rfl
            have hm3 : (d.i - 1) % 3 < 3 := Nat.mod_lt _ (by omega)
            have hM := hK.M hin _ hm3
            have hF := hK.F hin _ hm3
            have hi1 := (hI.pv (by rw [hs]; trivial)).1
            simp only [hs, reduceCtorEq, false_and, ite_false, Nat.add_zero] at hM hF
            have hcs := cnt0_succ (i := d.i - 1) hm3
            rw [show d.i - 1 + 1 = d.i by omega] at hcs
            simp only [ite_true] at hcs
            refine ⟨⟨hlead.symm, hr0, (d.i - 1) % 3, hm3, rfl, rfl, ?_⟩,
              .inr (.inr ⟨w, d, P, n, hσ⟩)⟩
            show _ + 1 ≤ _
            have : okPolls (Proof.EvW.kvReady L (g / L.block) ((d.i - 1) % 3)) ((X.tr g).take k) ≥
                cnt0 d.i ((d.i - 1) % 3) := by rw [hF]; omega
            have hM' := hM
            simp only [Proof.EvW.commitSpec] at hM' ⊢
            omega
          · exfalso
            simp only [InRing, Proof.EvW.oDone, Proof.EvW.barLoc, Proof.EvW.oDoneOff] at hr
            omega
          · exfalso
            simp only [InRing, Proof.EvW.oFinal, Proof.EvW.barLoc, Proof.EvW.oFinalOff] at hr
            omega
        | worker w => exact (worker_commit w.site hpc).elim
        | idle d => exact (idle_commit d.site hpc).elim
        | loader d P => exact (loader_commit d.site hpc).elim
        | exit x => exact (exitsite_commit x.site hpc).elim
    · exact hJ.elim

/-! ### Polls -/

theorem startup_wait : ∀ s : Startup.Site, s.pc ∈ waitPcs → False := by
  intro s h; revert h; cases s with
  | enter r => cases r <;> decide
  | _ => decide
theorem proA_wait (s : ProA.Site) (h : s.pc ∈ waitPcs) : False := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k => revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j => revert h; revert j; revert b; decide
  | _ => revert h; decide
theorem sm_wait : ∀ s : Proof.Sm.Site, s.pc ∈ waitPcs → s = .waitS ∨ s = .waitO := by site_cls
theorem epi_wait : ∀ s : Proof.Epi.Site, s.pc ∈ waitPcs → s = .wait := by site_cls
theorem worker_wait : ∀ s : Proof.Worker.Site, s.pc ∈ waitPcs → False := by site_cls
theorem idle_wait : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ waitPcs → False := by site_cls
theorem loader_wait : ∀ s : Proof.Loader.Site, s.pc ∈ waitPcs → s = .wait := by site_cls
theorem exitsite_wait : ∀ s : Proof.WComp.ExitSite, s.pc ∈ waitPcs → False := by site_cls
theorem mma_wait : ∀ s : Proof.Mma.Site, s.pc ∈ waitPcs → s = .kvWait ∨ s = .pWait := by site_cls

/-- **A poll of a ring barrier** acquires at CTA scope; a poll of `kv_ready s` is an MMA lane's
and a poll of `kv_empty s` a loader lane's, with the parity of the poller's earlier successful
polls (offset by `1 - δ` for `kv_empty`, `δ` the slot's preload). -/
theorem wait_ring (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc p : Nat} {mo : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait mo p ok acq sc⟩) (hr : InRing L mo) :
    (acq = true ∧ sc = .cta ∧ ∃ s < 3,
      (mo = Proof.EvW.kvReady L (g / L.block) s ∧ g % L.block / 32 = 7 ∧
        p % 2 = (okPolls (Proof.EvW.kvReady L (g / L.block) s) ((X.tr g).take k) + 0) % 2) ∨
      (mo = Proof.EvW.kvEmpty L (g / L.block) s ∧ g % L.block / 32 = 6 ∧
        p % 2 = (okPolls (Proof.EvW.kvEmpty L (g / L.block) s) ((X.tr g).take k) +
          (1 - if s < npOf Q L g then 1 else 0)) % 2)) ∧ UserAt Q L X g k := by
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
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
        exfalso
        rcases d with d | ⟨_ | _, τ⟩
        · exact proA_wait d.site hpc
        · cases τ with
          | sm d =>
            rcases sm_wait d.site hpc with hs | hs
            · have h' : Proof.Sm.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
              simp only [Proof.Sm.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨ok', -, rfl, -⟩ := h'
              simp only [InRing, Proof.EvD.sReadyOf, Proof.EvD.Bar.loc, Proof.EvD.Bar.off] at hr
              omega
            · obtain ⟨ok', h'⟩ := Proof.Sm.shape_waitO (Proof.ProA.sharedOk_of_pre hp)
                (sm_fired hat hi hc hf) hs
              simp only [Event.mk.injEq, Kind.wait.injEq] at h'
              obtain ⟨-, rfl, -⟩ := h'
              simp only [InRing, Proof.EvD.Bar.loc, Proof.EvD.Bar.off] at hr
              omega
          | epi d =>
            have hs := epi_wait d.site hpc
            have h' : Proof.Epi.Shape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
            simp only [Proof.Epi.Shape, hs, Event.mk.injEq, Kind.wait.injEq] at h'
            obtain ⟨ok', -, rfl, -⟩ := h'
            have hM : Proof.Epi.Means Q L g d.pr := tm_means hp hX hg k hlen _ hσ
            have hmb := hM.mb
            simp only [Proof.EvD.Bar.off] at hmb
            rw [Nat.mod_eq_of_lt (by omega)] at hmb
            simp only [InRing] at hr
            rw [hmb] at hr
            omega
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have hs := loader_wait d.site hpc
          have hsh := ld_shape hp hX he (by simp [Ends]) hσ
          simp only [Proof.EvW.LdShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh
          obtain ⟨ok', -, rfl, rfl, -, rfl, rfl⟩ := hsh
          have h6 : g % L.block / 32 = 6 := role_warp hp hX hg k hlen _ hσ
          have hK : LdCnt Q L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
          have hin : d.site.inLoop = true := by rw [hs]; rfl
          have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
          have hP := hK.P hin _ hm3
          have hlo := hK.lo hin
          simp only [hs, polledS, Bool.false_eq_true, false_and, ite_false, Nat.add_zero] at hP
          have hnp : npOf Q L g ≤ 3 := numPre_le3 _ _ _
          refine ⟨⟨rfl, rfl, d.i % 3, hm3, .inr ⟨rfl, h6, ?_⟩⟩, .inr (.inl ⟨w, d, P, n, hσ⟩)⟩
          rw [hP]
          exact slotCnt_parity hnp hlo
        | mma d P =>
          rcases mma_wait d.site hpc with hs | hs
          · have hsh : Proof.EvW.MmShape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh
            obtain ⟨ok', -, rfl, rfl, -, rfl, rfl⟩ := hsh
            have h7 : g % L.block / 32 = 7 := role_warp hp hX hg k hlen _ hσ
            have hK : MmCnt L g d ((X.tr g).take k) := kc_inv hp hX hg k hlen _ hσ
            have hin : iterS d.site = true := by rw [hs]; rfl
            have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
            have hF := hK.F hin _ hm3
            simp only [qkDoneS, hs, Bool.false_eq_true, false_and, ite_false, Nat.add_zero] at hF
            refine ⟨⟨rfl, rfl, d.i % 3, hm3, .inl ⟨rfl, h7, ?_⟩⟩, .inr (.inr ⟨w, d, P, n, hσ⟩)⟩
            rw [hF]
            rw [Nat.mod_mod]
            exact cnt0_parity d.i
          · exfalso
            have hsh : Proof.EvW.MmShape L g d ⟨pc, .wait mo p ok acq sc⟩ := hev
            simp only [Proof.EvW.MmShape, hs, Event.mk.injEq, Kind.wait.injEq] at hsh
            obtain ⟨ok', -, rfl, -⟩ := hsh
            simp only [InRing, Proof.EvW.pReady, Proof.EvW.barLoc, Proof.EvW.pReadyOff] at hr
            omega
        | worker w => exact (worker_wait w.site hpc).elim
        | idle d => exact (idle_wait d.site hpc).elim
        | exit x => exact (exitsite_wait x.site hpc).elim
    · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
