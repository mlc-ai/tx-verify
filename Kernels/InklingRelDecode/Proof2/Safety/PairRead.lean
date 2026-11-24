-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.RoleIter

@[expose] public section

/-! # The reads of the pair `(num_pre, num_iters)`

The prologue's 128 threads store the pair at `global_smem + 212992` (`st9 0`, `st9 1`, one
vector store) before their first `barrier.sync 1`, every thread of a CTA with the CTA's values
(`st9_event`, from the prologue's reference: the request words, `ProA.st9_values`). The softmax
region's scratch store (`store10`) writes the same bytes after its second barrier-1 event. No
other write covers them (`pair_wr_info`, `async_write_loc`).

A worker's four-byte read of an element of the pair is the loader's `ld0`/`ld1` or the MMA warp's
`ldNum`, at barrier-1 count 1 (`role_count`: the roles run at the first iteration only). So the
CTA's thread 0's store is before it (`st9_exists`, `bar1_handoff`), every `store10` after it
(count 1 below 2), and the read returns the element (`pair_read`, by `read_of_writers`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The access of element `j` of the pair of CTA `c`. -/
def pairAcc (L : Launch) (c : Nat) : Fin 2 → Acc
  | 0 => Proof.EvD.wordAcc ⟨.shared, c, (L.sharedBase + 212992) % 2 ^ 32⟩
  | 1 => Proof.EvD.wordAcc ⟨.shared, c, (L.sharedBase + 212992) % 2 ^ 32 + 4⟩ 1

/-- Element `j` of the pair of thread `g`'s CTA: `num_pre` and `num_iters`. -/
def pairVal (Q : Params) (L : Launch) (g : Nat) : Fin 2 → Nat
  | 0 => Proof.ProA.numPre Q (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)
  | 1 => Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)

/-- A byte of the pair of CTA `c`. -/
def InPair (L : Launch) (c : Nat) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = c ∧ L.sharedBase + 212992 ≤ l.addr ∧ l.addr < L.sharedBase + 213000

theorem pairVal_eq {g h : Nat} (hc : g / L.block = h / L.block) (j : Fin 2) :
    pairVal Q L g j = pairVal Q L h j := by
  have hz : Proof.ProA.cta L g .z = Proof.ProA.cta L h .z := by unfold Proof.ProA.cta; rw [hc]
  have hx : Proof.ProA.cta L g .x = Proof.ProA.cta L h .x := by unfold Proof.ProA.cta; rw [hc]
  fin_cases j <;> simp only [pairVal, hz, hx]

/-! ### The stores -/

/-- **The event of a prologue `st9 j` state** writes element `j` of the CTA's pair. -/
theorem st9_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j : Nat} {e : Event} (he : X.get (h, j) = some e) (hne : ¬ Ends e)
    {tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X h j = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    {jj : Fin 2} (hs : d.site = .st9 jj) :
    ∃ pc, e = ⟨pc, .wr (pairAcc L (h / L.block) jj) (b32 (pairVal Q L h jj)).toBytes⟩ := by
  have hg := Frame.lt_of_get hX he
  have hJ := (good_all' hp hX hg j).2 _ hσ
  obtain ⟨-, -, hR, -⟩ := hJ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  cases o with
  | none => exact absurd (fires_none_ends hf) hne
  | some u =>
    have hx : d.site ≠ .exit := by rw [hs]; simp
    have hF := ProA.fired_old (P := Startup.inh L h Q tm) hx hat hi.1 hc hf
    have ha : Proof.ProA.ArgsOk L h d.dt.pro := hi.1.args
    have hspl := hp.splitsRange
    have hw : d.dt.pro.w71 = Q.splits := by
      rw [hR.pro]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨w0, w1, w2⟩ := hR.words
    have hold : d.old.site = (ProA.Site.st9 jj).old := by simp only [ProA.D.old, hs]
    have hafter : (ProA.Site.st9 jj).old.afterSk = true := by fin_cases jj <;> rfl
    have hne1 : (ProA.Site.st9 jj).old ≠ .sMax := by fin_cases jj <;> decide
    have hne2 : (ProA.Site.st9 jj).old ≠ .ldCu0 := by fin_cases jj <;> decide
    rw [hold] at w0 w1 w2
    have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L h .z) d.dt :=
      ⟨w0 hne1 hne2, w1 (.inl hafter), w2 hafter⟩
    obtain ⟨hv0, hv1⟩ := Proof.ProA.st9_values hp hg ha hw hm
    fin_cases jj
    · obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st9_0 hF (by simp [ProA.D.old, hs, ProA.Site.old])
      have hv' : storeValue 32 (Proof.ProA.numPreW L h d.dt) = .ok v := hv
      rw [hv0, storeValue_b32'] at hv'
      obtain rfl := (Except.ok.inj hv').symm
      exact ⟨_, he'⟩
    · obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st9_1 hF (by simp [ProA.D.old, hs, ProA.Site.old])
      have hv' : storeValue 32 (Proof.ProA.numItersW L h d.dt) = .ok v := hv
      rw [hv1, storeValue_b32'] at hv'
      obtain rfl := (Except.ok.inj hv').symm
      exact ⟨_, he'⟩

/-- **A write of a byte of the pair** is a prologue `st9` with the CTA's element at barrier-1
count 0, or the softmax region's scratch store at count 2. -/
theorem pair_wr_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (h, j) = some ⟨pc, .wr a bs⟩)
    {l : Loc} (hl : a.Covers l) (hr : InPair L (h / L.block) l) :
    (∃ jj : Fin 2, a = pairAcc L (h / L.block) jj ∧ bs = (b32 (pairVal Q L h jj)).toBytes ∧
        ((X.tr h).take j).countP (Execution.isBarId 1) = 0) ∨
      ((X.tr h).take j).countP (Execution.isBarId 1) = 2 := by
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
          · exfalso
            obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st8 hF
              (by simp [ProA.D.old, hs, ProA.Site.old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            simp only [Proof.EvD.wordAcc, hm 213336 (by omega)] at hlo hhi
            omega
          · left
            obtain ⟨pc', he'⟩ := st9_event hp hX he (by simp [Ends]) hσ hs
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            refine ⟨jj, rfl, rfl, ?_⟩
            have hC' : _ = proPh d := hC
            rw [hC']
            simp [proPh, hs]
        · cases τ with
          | sm d =>
            right
            have hs := sm_wr d.site hpc
            have hC' : _ = smPh d := hC
            rw [hC']
            simp [smPh, hs]
          | epi d =>
            exfalso
            have h' : Proof.Epi.Shape L h d ⟨pc, .wr a bs⟩ := hev
            unfold Proof.Epi.Shape at h'
            split at h'
            all_goals first
              | exact h'.elim
              | (simp only [Event.mk.injEq, reduceCtorEq, and_false, exists_false] at h'; done)
              | (obtain ⟨v, hv, h'⟩ := h'
                 simp only [Event.mk.injEq, Kind.wr.injEq] at h'
                 obtain ⟨-, rfl, rfl⟩ := h'
                 first
                   | (simp only [Proof.EvD.wordAcc, hm 213336 (by omega)] at hlo hhi; omega)
                   | (simp [Proof.EvD.wordAcc] at hs1 hrs; simp_all))
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

/-- The prologue's step from `st8` and from `st9 0`. -/
theorem pro_next_st9 {dt : Proof.ProA.Dat} {e : Event} :
    ProA.next L g ⟨.st8, dt⟩ e = some (some ⟨.st9 0, dt⟩) ∧
      ProA.next L g ⟨.st9 0, dt⟩ e = some (some ⟨.st9 1, dt⟩) := ⟨rfl, rfl⟩

/-- A prologue state followed by a prologue step to a site other than the exit. -/
theorem pro_state_succ {h j : Nat} (hj : j + 1 < (X.tr h).length) {tm : Nat} {bw : Value}
    {d d' : ProA.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X h j = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hd : ∀ e, ProA.next L h d e = some (some d')) (hx : d'.site ≠ .exit) :
    ∃ n', Frame.stateAt (thread Q L) X h (j + 1) =
      some (some (.inr ⟨.inl (.dp tm bw), .inl d'⟩, n')) := by
  have hlt : j < (X.tr h).length := by omega
  obtain ⟨e, he⟩ : ∃ e, (X.tr h)[j]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [Frame.stateAt_succ he, hσ]
  show ∃ n', (thread Q L h).next _ e = _
  rw [next_pro, hd e]
  have hxo : ProA.exitOf d' = none := by
    unfold ProA.exitOf; split
    · rename_i hs; exact absurd hs hx
    · rfl
  refine ⟨Code.bump cls n e, ?_⟩
  simp only [Option.map_some, Option.some.injEq]
  rw [Code.enter_none (by simp [Code.gatedExit, hxo])]

/-- **The CTA's thread 0 made its `st9 j` store before its first barrier-1 arrival**, once a
thread of the CTA has passed its first barrier-1 event. -/
theorem st9_exists (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j0 pc0 : Nat} (hb0 : X.IsBarrier (g, j0) 1 none pc0)
    (hpass : j0 + 1 < (X.tr g).length)
    (h0c : ((X.tr g).take j0).countP (Execution.isBarId 1) = 0) (jj : Fin 2) :
    ∃ j9 pc9, X.get (g / L.block * L.block, j9) =
        some ⟨pc9, .wr (pairAcc L (g / L.block) jj)
          (b32 (pairVal Q L (g / L.block * L.block) jj)).toBytes⟩ ∧
      ((X.tr (g / L.block * L.block)).take (j9 + 1)).countP (Execution.isBarId 1) = 0 := by
  have hb : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg : g < L.threads := Frame.lt_of_get hX hb0
  obtain ⟨i0, j8, tm, bw, d8, n8, hj8, hlen0, hci, hev0, h8σ, h8s⟩ :=
    st8_state hp hX hb0 hpass h0c
  have hh0t : g / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hh0c : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  obtain ⟨site8, dt⟩ := d8
  simp only at h8s
  subst h8s
  obtain ⟨ev, hev, hb1⟩ := hev0
  obtain ⟨c1, md1, hk1⟩ := isBarId1_kind hb1
  -- an event at a `st9` state up to `i0` is a write, so it is before `i0`
  have hwr : ∀ j (jj : Fin 2) n, j ≤ i0 →
      Frame.stateAt (thread Q L) X (g / L.block * L.block) j =
        some (some (.inr ⟨.inl (.dp tm bw), .inl ⟨.st9 jj, dt⟩⟩, n)) →
      j < i0 ∧ ∃ pc9, X.get (g / L.block * L.block, j) =
        some ⟨pc9, .wr (pairAcc L (g / L.block) jj)
          (b32 (pairVal Q L (g / L.block * L.block) jj)).toBytes⟩ := by
    intro j jj n hle hσj
    have hjl : j < (X.tr (g / L.block * L.block)).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g / L.block * L.block, j) = some e :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    have hne : ¬ Ends e := by
      rcases Nat.lt_or_eq_of_le hle with hlt | rfl
      · exact not_ends_of_lt hX hh0t he (by omega)
      · rw [hev] at he
        obtain rfl := Option.some.inj he
        obtain ⟨pce, ke⟩ := ev
        simp only at hk1
        subst hk1
        simp [Ends]
    obtain ⟨pc', he'⟩ := st9_event hp hX he hne hσj rfl
    rw [hh0c] at he'
    refine ⟨?_, pc', by rw [he, he']⟩
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact hlt
    · exfalso
      rw [hev] at he
      obtain rfl := Option.some.inj he
      rw [he'] at hk1
      cases hk1
  have hcnt : ∀ j, j < i0 → ((X.tr (g / L.block * L.block)).take (j + 1)).countP
      (Execution.isBarId 1) = 0 := by
    intro j hj
    have := countP_take_mono (Execution.isBarId 1) (X.tr (g / L.block * L.block))
      (show j + 1 ≤ i0 by omega)
    omega
  obtain ⟨n1, h1σ⟩ := pro_state_succ (by omega) h8σ (fun _ => pro_next_st9.1) (by simp)
  obtain ⟨hlt1, pc1, he1⟩ := hwr (j8 + 1) 0 n1 (by omega) h1σ
  fin_cases jj
  · exact ⟨j8 + 1, pc1, he1, hcnt _ hlt1⟩
  · obtain ⟨n2, h2σ⟩ := pro_state_succ (by omega) h1σ (fun _ => pro_next_st9.2) (by simp)
    obtain ⟨hlt2, pc2, he2⟩ := hwr (j8 + 1 + 1) 1 n2 (by omega) h2σ
    exact ⟨j8 + 1 + 1, pc2, he2, hcnt _ hlt2⟩


/-! ### The reads -/

/-- **A worker's four-byte read of the pair is at barrier-1 count 1**: it is the loader's `ld0`
or `ld1` or the MMA warp's `ldNum`, whose phase is 1 (`role_count`). -/
theorem pair_reader_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hw : 128 ≤ g % L.block) (hsp : a.loc.space = .shared) (hsz : a.size = 4)
    (hlo : L.sharedBase + 212992 ≤ a.loc.addr) :
    ((X.tr g).take k).countP (Execution.isBarId 1) = 1 := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := rd_pc hc hf rfl hsp
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exfalso
      have hs := startup_rd st.site hpc
      have h' : Startup.Ev L g st ⟨pc, .rd a bs⟩ := hev
      simp only [Startup.Ev, hs] at h'
      obtain ⟨ac, bs', h', hl, -, -⟩ := h'
      simp only [Event.mk.injEq, Kind.rd.injEq] at h'
      obtain ⟨-, rfl, rfl⟩ := h'
      rw [hl] at hlo
      simp only at hlo
      omega
    · rename_i i
      cases i with
      | dp tm bw =>
        exfalso
        rcases d with d | ⟨_ | _, τ⟩
        · exact proA_rd d.site hpc
        · cases τ with
          | sm d =>
            have := (hi : Proof.Sm.Inv L g d).tid
            omega
          | epi d => exact epi_rd d.site hpc
        · exact hJ.elim
      | worker w =>
        cases d with
        | worker w =>
          exfalso
          have hs : w.site = .ldRole := by
            rcases worker_rd w.site hpc with h | h
            · exact h
            · have hW := hJ.2.2.1.1
              rw [h] at hW
              simp at hW
          have hF : (Proof.WComp.code L g Q).toMachine.Fired (some (.worker w))
              ⟨pc, .rd a bs⟩ (some u) := by
            refine ⟨t, ⟨hat, hi⟩, ?_⟩
            have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.worker w)]? = some ins := hc
            show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.worker w)) t) _ (some u)
            simp only [Code.tmpl]
            rw [hc', hat.1]
            exact hf
          obtain ⟨ac, bs', he', -, hz⟩ := Proof.Worker.shape_ldRole hp
            (by rw [hb]; exact Nat.mod_lt _ (by omega)) hs hF
          simp only [Event.mk.injEq, Kind.rd.injEq] at he'
          obtain ⟨-, rfl, rfl⟩ := he'
          omega
        | idle d => exact (idle_rd d.site hpc).elim
        | loader d P =>
          rw [role_count hp hX hg hlen rfl hσ]
          rcases loader_rd d.site hpc with hs | hs <;> simp [wph, ldPh, hs]
        | mma d P =>
          rw [role_count hp hX hg hlen rfl hσ]
          simp [wph, mmPh, mma_rd d.site hpc]
        | exit x => exact (exitsite_rd x.site hpc).elim
    · exact hJ.elim

/-- **A worker's read of an element of the pair returns the CTA's element.** -/
theorem pair_read (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hw : 128 ≤ g % L.block) (jj : Fin 2)
    (hloc : a.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * jj.val⟩)
    (hsz : a.size = 4) :
    bs = (b32 (pairVal Q L g jj)).toBytes.map some := by
  have hb : L.block = 256 := hp.block
  have hblk : 0 < L.block := by omega
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hjj : jj.val < 2 := jj.isLt
  have h1 := pair_reader_count hp hX he hw (by rw [hloc]) hsz (by rw [hloc]; simp only; omega)
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
  swap
  · exact absurd h01 (by omega)
  subst hmd hcn
  -- the visible store of the CTA's thread 0
  obtain ⟨j9, pc9, hget9, hc9⟩ := st9_exists hp hX hget0 (by omega) hc0 jj
  have hg0t : g / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hcta0 : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  rw [pairVal_eq hcta0] at hget9
  have hw0 : ((g / L.block * L.block) % L.block) / 32 ∈
      Finset.range (CtaBarrier.warps L.block) := by
    rw [Nat.mul_mod_left]; simp [CtaBarrier.warps, hb]
  have hlen9 : j9 < (X.tr (g / L.block * L.block)).length :=
    (List.getElem?_eq_some_iff.mp hget9).1
  have hbc9 : baseCausality L X (g / L.block * L.block, j9) (g, k) :=
    bar1_handoff hp hX _ _ j9 k ⟨⟨hg0t, hg, hcta0⟩, hw0, trivial⟩ hlen
      (by simp only; rw [hc9, h1]; omega)
  -- the bytes
  have hrd : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, he⟩
  have hm : (L.sharedBase + 212992) % 2 ^ 32 = L.sharedBase + 212992 :=
    Nat.mod_eq_of_lt (by omega)
  have hat : ∀ i, a.loc.at i = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * jj.val + i⟩ :=
    fun i => by rw [hloc]; rfl
  have hacc : (pairAcc L (g / L.block) jj).loc =
      ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * jj.val⟩ ∧
      (pairAcc L (g / L.block) jj).size = 4 := by
    rcases jj with ⟨_ | _ | _, hj⟩
    · exact ⟨by simp [pairAcc, Proof.EvD.wordAcc]; omega, rfl⟩
    · exact ⟨by simp [pairAcc, Proof.EvD.wordAcc]; omega, rfl⟩
    · omega
  have hcovA : ∀ i < a.size, (pairAcc L (g / L.block) jj).Covers (a.loc.at i) := by
    intro i hi
    rw [hat, hsz] at *
    refine ⟨by rw [hacc.1], by rw [hacc.1], ?_, ?_⟩
    · rw [hacc.1]; simp only; omega
    · rw [hacc.1, hacc.2]; simp only; omega
  have hwb : ∀ i < a.size, wbyte (pairAcc L (g / L.block) jj) (b32 (pairVal Q L g jj)).toBytes
      (a.loc.at i) = (b32 (pairVal Q L g jj)).toBytes[i]? := by
    intro i hi
    simp only [wbyte, hat, hacc.1]
    rw [show L.sharedBase + 212992 + 4 * jj.val + i - (L.sharedBase + 212992 + 4 * jj.val) = i by
      omega]
  refine read_of_writers hX hrd
    (fun ref => ∃ i pc', ref = .thread i ∧
      X.get i = some ⟨pc', .wr (pairAcc L (g / L.block) jj) (b32 (pairVal Q L g jj)).toBytes⟩)
    _ (by rw [b32_toBytes, hsz]; rfl)
    (fun i hi => ⟨.thread (g / L.block * L.block, j9), _, _, ⟨_, pc9, rfl, hget9⟩,
      Or.inl ⟨pc9, hget9⟩, hcovA i hi, .direct (.inl hbc9)⟩)
    (fun i hi w dst written hW hmw _ => by
      obtain ⟨i', pc', rfl, hgi⟩ := hW
      rcases hmw with ⟨pcm, hmw⟩ | ⟨old, pcm, hmw⟩
      · rw [hgi] at hmw
        simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hmw
        obtain ⟨-, rfl, rfl⟩ := hmw
        exact hwb i hi
      · rw [hgi] at hmw; simp at hmw)
    (fun i hi w' dst' bytes hmw hcov => by
      have hl := hat i
      rw [hsz] at hi
      rcases w' with ⟨h, j⟩ | ⟨ii, p⟩
      · obtain ⟨⟨pcw, hgw⟩, hctw⟩ := thread_write_cta hp hX hmw
        have hhc : h / L.block = g / L.block := by
          rw [← hctw (hcov.1.symm.trans (by rw [hl])), ← hcov.2.1, hl]
        have hr' : InPair L (h / L.block) (a.loc.at i) := by
          rw [hl, hhc]; exact ⟨rfl, rfl, by simp only; omega, by simp only; omega⟩
        rcases pair_wr_info hp hX hgw hcov hr' with ⟨jj', hdst, hbs', -⟩ | hc2
        · by_cases hjj' : jj' = jj
          · subst hjj'
            left
            refine ⟨(h, j), pcw, rfl, ?_⟩
            rw [hgw, hdst, hbs', hhc, pairVal_eq hhc]
          · exfalso
            obtain ⟨-, -, hlo', hhi'⟩ := hcov
            rw [hdst, hhc, hl] at *
            have hjj'' : jj'.val < 2 := jj'.isLt
            have hne : jj'.val ≠ jj.val := fun h => hjj' (Fin.ext h)
            fin_cases jj <;> fin_cases jj' <;>
              simp_all [pairAcc, Proof.EvD.wordAcc] <;> omega
        · right
          have hh := Frame.lt_of_get hX hgw
          have hjl : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hgw).1
          have hwg : (g % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
            have := Nat.mod_lt g (show 0 < L.block by omega)
            simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
            omega
          have hup : ((X.tr g).take (k + 1)).countP (Execution.isBarId 1) = 1 := by
            rw [List.take_add_one, show (X.tr g)[k]? = _ from he, Option.toList_some,
              countP_snoc, h1]
            simp [Execution.isBarId]
          exact .direct (.inl (bar1_handoff hp hX g h k j ⟨⟨hg, hh, hhc.symm⟩, hwg, trivial⟩
            hjl (by simp only; rw [hup, hc2]; omega)))
      · exfalso
        obtain ⟨-, -, hfar⟩ := async_write_loc hp hX hmw hcov
        rw [hl] at hfar
        simp only at hfar
        omega)

end
end PTX.Kernels.InklingRelDecode.Proof2
