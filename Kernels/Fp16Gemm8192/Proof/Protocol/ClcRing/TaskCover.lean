-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.PartitionTiles

@[expose] public section

/-! # Every cluster task's tile is stored

In a complete execution without undefined behaviour every cluster task `t` is processed: its cluster
ran, or exactly one request canceled it (`Clc.Owned`, `Complete`); the first thread of each warp
group of the processing cluster exited, and the request's number is below its successful response
polls (`exit_task`): it read a claiming response at each poll but its latest, and the responses of
the leader scheduler's requests in order (`ReaderValues`, `AllResponsesAgree`). An exited first
thread issued eight TMA stores per response poll, the `(8 E + s)`-th one of slice `s` of its task
`E` (`tma_ordinal`, `exit_store`), whose tile is the task's (`tile_task`). So every slot of every
tile is a TMA store's (`outputCover`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy TensorDescriptor

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A request is its cluster's leader scheduler's, from the leader CTA, on that CTA's response
barrier. -/
theorem issue_leader (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {h ki pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (he : X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩) :
    h / L.block = 2 * (h / L.block / 2) ∧ h = producer L X (h / L.block / 2) ∧
      sp.mbar = Bar.loc L (2 * (h / L.block / 2)) ⟨.clc, 0, true⟩ := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hh := Frame.lt_of_get hX he
  have hC : h / L.block < 1024 := by
    rw [← hgrid]
    exact (Nat.div_lt_iff_lt_mul (by rw [hblock]; decide)).mpr hh
  have hmem := ht.clc_multicast h ki pc sp tg he (2 * (h / L.block / 2)) (by omega) (by omega)
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := h / L.block / 2) hpre hX ht he hmem (by omega)
  have hsel := producer_sel (X := X) hpre (h / L.block / 2)
  rw [← hp] at hsel
  simp only [consumerSel, decide_eq_true_eq] at hsel
  have h0 : ctaOf 2 = 0 := by decide
  rw [h0] at hsel
  exact ⟨by omega, hp, hmb⟩

/-- A response naming a valid task claims a CTA. -/
theorem claims_task (hpre : Pre P L mem0) {i : EvId} {t : Nat} (ht : t < 512) :
    Loader.claims (Clc.responseOf L i (some t)) := by
  simp only [Loader.claims, Clc.responseOf, Option.map_some, Option.getD_some,
    Launch.oneDim_ctaidOf hpre.oneDimLaunch.1, clusterStart_eq hpre]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : t * 2 < 2 ^ 32)]
  unfold Loader.none32
  omega

/-- A trace without undefined behaviour has none in its prefixes. -/
theorem take_no_ub {g k : Nat} (hub : ∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) :
    ∀ e ∈ (X.tr g).take k, ∀ f, e.kind ≠ .ub f := by
  intro e he f hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  have hjl : j < ((X.tr g).take k).length := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_take] at hjl
  rw [List.getElem?_take_of_lt (by omega)] at hj
  apply hub j e.pc f
  change (X.tr g)[j]? = _
  rw [hj, ← hk]

/-- **A TMA store's number**: a first thread's TMA store of slice `s` of its task `E` (after `E + 1`
successful response polls) is its `(8 E + s)`-th. -/
theorem tma_ordinal (ht : ThreadFacts L X) {g k pc a : Nat} {sp : TensorStore.Spec}
    {c : Consumer.D} {s : Fin 8} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) (hs : c.site = .tma s)
    (hub : ∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) :
    storeIssues ((X.tr g).take k) + 8 =
      8 * okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + s.val := by
  obtain ⟨hT1, hT2⟩ := ht.cons_tmas hg hσ
  have hM := hT2 (take_no_ub hub)
  simp only [hT1 s (.inr hs), ↓reduceIte, Consumer.D.tmaPend, hs, Nat.add_zero] at hM
  obtain ⟨-, hO⟩ := (ht.cons_out hg he hσ).1
  simp only [Consumer.D.outLag, hs] at hO
  have hb := (tma_outBars ht hg he hσ hs).1
  omega

/-- **An exited first thread's stores**: for each of its tasks `E` and slice `s`, its TMA store of
slice `s` after `E + 1` successful response polls. -/
theorem exit_store (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g pc : Nat}
    (hg : g < L.threads)
    (hw : g % L.block / 32 < 8) (hf : Consumer.first L g = true)
    (hub : ∀ j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩)
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) {E : Nat}
    (hE : E < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) (s : Fin 8) :
    ∃ k pc a sp c, X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ ∧
      Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) ∧ c.site = .tma s ∧
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) = E + 1 := by
  have htot := ht.cons_exit_tmas hg hw hf hub hlast
  have hsl := s.isLt
  obtain ⟨j, ev, hj, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isTensorStore (xs := X.tr g)
    (c := 8 * E + s.val) (by unfold storeIssues at htot; omega)
  obtain ⟨epc, ek⟩ := ev
  obtain ⟨a, sp, rfl⟩ : ∃ a sp, ek = .tensorStore a sp := by
    unfold isTensorStore at hp
    split at hp
    · rename_i a sp hk
      exact ⟨a, sp, hk⟩
    · cases hp
  have hej : X.get (g, j) = some ⟨epc, .tensorStore a sp⟩ := hj
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hej (by simp)
  obtain ⟨c, rfl⟩ := (ht.access_region hg hej hσ).2.2 a sp rfl
  obtain ⟨s', hs', -⟩ := (ht.cons_out hg hej hσ).2.2.1 a sp rfl
  have hord := tma_ordinal ht hg hej hσ hs' hub
  unfold storeIssues at hord
  rw [hc] at hord
  have hs'l := s'.isLt
  have hss : s' = s := Fin.ext (by omega)
  subst hss
  exact ⟨j, epc, a, sp, c, hej, hσ, hs', by omega⟩

/-- A request's number in its cluster: its leader scheduler's earlier requests. -/
abbrev reqNo (L : Launch) (X : Execution) (i : EvId) : Nat :=
  issuesBefore L X (i.1 / L.block / 2) i.1 i.2

/-- Two requests of one cluster with the same number are one event. -/
theorem request_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {i j : EvId} {s s' : Clc.Spec} {tg tg' : List Nat}
    (hi : X.ClcIssue i s tg) (hj : X.ClcIssue j s' tg')
    (hc : i.1 / L.block / 2 = j.1 / L.block / 2) (hn : reqNo L X i = reqNo L X j) : i = j := by
  obtain ⟨pci, hei⟩ := hi
  obtain ⟨pcj, hej⟩ := hj
  obtain ⟨-, hpi, hmi⟩ := issue_leader hpre hX ht hei
  obtain ⟨-, hpj, hmj⟩ := issue_leader hpre hX ht hej
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := j
  simp only at hc hpi hpj hmi hmj hn
  have hgg : g = g' := by rw [hpi, hpj, hc]
  subst hgg
  have hk := issues_inj (X := X) (L := L) (c := g / L.block / 2) hei hej
    (by simp [clcIssuesTo, hmi]) (by simp [clcIssuesTo, hmj]) (by simpa using hn)
  rw [hk]

/-- The response a request was answered with, read after a successful poll, names the request's
task. -/
theorem read_task (hX : Consistent L kernel Prod mem0 X) {i : EvId} {s : Clc.Spec} {tg : List Nat}
    (hi : X.ClcIssue i s tg) {t : Nat}
    (hres : X.clcState.response (Clc.requestId i) = some (some t))
    {r : ClcResponse} (hr : (X.clc i).resolved = some r) : r = Clc.responseOf L i (some t) := by
  obtain ⟨task, htask, rfl⟩ := (hX.clc.2.2.2.1 i s tg hi).1.result r hr
  rw [hres] at htask
  cases htask
  rfl

/-- **An exited first thread processed its cluster's answered tasks**: a request of its cluster
answered with a task numbers fewer requests than the thread's successful response polls, less one.
-/
theorem exit_task (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) (hag : AllResponsesAgree L X) {g pc : Nat}
    (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (hlast : (X.tr g).getLast? = some ⟨pc, .exit⟩) {i : EvId} {s : Clc.Spec} {tg : List Nat}
    (hi : X.ClcIssue i s tg) (hic : i.1 / L.block / 2 = g / L.block / 2) {t : Nat} (htl : t < 512)
    (hres : X.clcState.response (Clc.requestId i) = some (some t)) :
    reqNo L X i + 1 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨-, j0, pcw, p, acq, sc, pcr, a, bs, rr, hj0, hj1, hfoot, hrr, hnc, hcnt⟩ :=
    ht.cons_exit_tiles hg hw hlast
  by_contra hlt
  set n := okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j0) with hn
  obtain ⟨pci, hei⟩ := hi
  obtain ⟨hcta, hprod, hmb⟩ := issue_leader hpre hX ht hei
  rcases Nat.lt_or_ge n (reqNo L X i) with hlt' | hge
  · -- the leader scheduler read, at its `n`-th poll before the request, a claiming response
    have hh := Frame.lt_of_get hX hei
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hei (by simp)
    obtain ⟨b, hb, hby, -⟩ := (ht.ring_event hh hei hσ).clc _ _ rfl
    obtain ⟨rg, sl, f⟩ := b
    simp only [Bar.Valid] at hb
    cases rg <;> cases f <;> simp only [Ring.slots, Bar.clcBy] at hb hby
    obtain ⟨⟨sd, rfl⟩, -⟩ := hby
    obtain ⟨hle, hreads⟩ := ht.sched_issue hh hei hσ rfl
    have hreq : ((X.tr i.1).take i.2).countP
        (clcIssuesTo (Bar.loc L (i.1 / L.block) ⟨.clc, 0, true⟩)) = reqNo L X i := by
      simp only [reqNo, issuesBefore]
      rw [← hcta]
    obtain ⟨j1, ev, hj, hp, hc⟩ := MbarRing.Slot.exists_nth_countP
      (okPoll (Bar.loc L (i.1 / L.block) ⟨.clc, 0, true⟩)) (xs := (X.tr i.1).take i.2) (c := n)
      (by unfold okPolls at hle; omega)
    have hj1l : j1 < i.2 := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hj1l] at hj
    rw [List.take_take, Nat.min_eq_left hj1l.le] at hc
    obtain ⟨p1, acq1, sc1, hk1⟩ := okPoll_wait_form hp
    have he1 : X.get (i.1, j1) = some ⟨ev.pc, .wait (Bar.loc L (i.1 / L.block) ⟨.clc, 0, true⟩) p1
        true acq1 sc1⟩ := by
      change (X.tr i.1)[j1]? = _
      rw [hj, ← hk1]
    obtain ⟨pcr1, src1, bs1, rr1, hr1, hf1, hrr1, hcl1⟩ := hreads j1 _ _ _ _ hj1l he1
    have hbs := hag (g / L.block / 2) g i.1 j0 j1 pcw ev.pc p p1 pcr pcr1 acq acq1 sc sc1 a src1 bs
      bs1 rfl hic hj0 he1 (hc.trans hn).symm hj1 hfoot hr1 hf1
    subst hbs
    rw [hrr] at hrr1
    cases hrr1
    exact hnc hcl1
  · -- the thread's latest poll reads the response of the request itself
    have hnq : n = reqNo L X i := by omega
    obtain ⟨i2, s2, tg2, r2, hi2, hic2, -, hcnt2, -, hres2, hread⟩ :=
      hv (g / L.block / 2) g j0 pcw p acq sc rfl hj0
    have hbs := hread pcr a bs hj1 hfoot
    subst hbs
    rw [responseOf_clc] at hrr
    cases hrr
    have heq : i2 = i := by
      refine request_eq hpre hX ht hi2 ⟨pci, hei⟩ (by omega) ?_
      have hc2 : i2.1 / L.block / 2 = g / L.block / 2 := by omega
      have h2 : reqNo L X i2 = n := by
        simp only [reqNo, issuesBefore]
        rw [hc2]
        exact hcnt2
      exact h2.trans hnq
    subst heq
    rw [read_task hX ⟨pci, hei⟩ hres hres2] at hnc
    exact hnc (claims_task hpre htl)

/-- **Where a TMA store writes**, slot by slot: the element byte of its slice's column `x` and its
group's row `y` of its tile. -/
theorem store_writeLoc (hpre : Pre P L mem0) (ht : ThreadFacts L X) {g k pc a : Nat}
    {sp : TensorStore.Spec} {c : Consumer.D} {s : Fin 8} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) (hs : c.site = .tma s) :
    ∀ x y z, x < 32 → y < 128 → z < 2 → TensorStore.writeLoc sp x y z = some ((elementLoc P.dBase
      (outputRow c.m (g / L.block % 2) (Consumer.tidOf L g / 32 / 4) y)
      (outputCol c.n s x)).at z) := by
  intro x y z hx hy hz
  obtain ⟨s', hs', -, hm, hn, hrows, hred, horig, -⟩ := ht.store_tile hg he hσ
  rw [hs] at hs'
  cases hs'
  obtain ⟨hp, hmap⟩ := ht.store_map hg he hσ rfl
  rw [hpre.paramD] at hp
  obtain rfl : P.dMap = a := (Prod.mk.inj (Option.some.inj hp)).2
  rw [hpre.mapD] at hmap
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := sp
  simp only at hrows hred horig hmap ⊢
  subst hrows hred
  simp only [Option.some.injEq, Sigma.mk.injEq] at hmap
  obtain ⟨rfl, hdesc⟩ := hmap
  cases hdesc
  have hq : Consumer.tidOf L g / 32 / 4 < 2 := by
    have := ht.role_warp hg (len_of_get he).le hσ
    simp only [roleWarp] at this
    show g % L.block / 32 / 4 < 2
    omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have horigin : origin = outputOrigin (taskOfTile c.m c.n) (g / L.block % 2)
      (Consumer.tidOf L g / 32 / 4) s.val := by
    funext i
    rw [horig i]
    simp only [outputOrigin, tensorOrigin, tileM_taskOfTile _ hn, tileN_taskOfTile _ hn,
      outputCol, outputRow]
    split_ifs <;> push_cast <;> omega
  subst horigin
  have hw := output_writeLoc (base := P.dBase) (cls := P.dClass) (shared := sb)
    (taskOfTile_lt hm hn) hr hq s.isLt hx hy hz
  rw [hw, tileM_taskOfTile _ hn, tileN_taskOfTile _ hn]

/-- The first thread of warp group `q` of rank `r` of cluster `c`. -/
abbrev leadOf (L : Launch) (c r q : Nat) : Nat := (2 * c + r) * L.block + 128 * q

/-- **Every slot of every tile is a TMA store's**, in a complete execution without undefined
behaviour. -/
theorem outputCover (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) (hag : AllResponsesAgree L X)
    (hd : Complete L X) (hub : ¬ HasUb X) : OutputCover P L X := by
  intro t htl r hr q hq s
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hcs := hpre.cluster
  have hub' : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩ := fun g j pc f h => hub ⟨_, _, _, h⟩
  -- the lead thread of group `q` of rank `r` of cluster `c`
  have hlead : ∀ c, c < 512 → leadOf L c r q < L.threads ∧ leadOf L c r q % L.block / 32 < 8 ∧
      Consumer.first L (leadOf L c r q) = true ∧ leadOf L c r q / L.block = 2 * c + r ∧
      leadOf L c r q / L.block / 2 = c ∧ leadOf L c r q / L.block % 2 = r ∧
      Consumer.tidOf L (leadOf L c r q) / 32 / 4 = q ∧
      L.clusterOfCta (leadOf L c r q / L.block) = c := by
    intro c hc
    have h1 : leadOf L c r q / L.block = 2 * c + r := by simp only [leadOf, hblock]; omega
    have h2 : leadOf L c r q % L.block = 128 * q := by simp only [leadOf, hblock]; omega
    refine ⟨?_, by rw [h2]; omega, ?_, h1, by omega, by omega, ?_, ?_⟩
    · simp only [Launch.threads, leadOf, hblock, hgrid]
      omega
    · simp only [Consumer.first, Consumer.tidOf, h2, decide_eq_true_eq]
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> decide
    · simp only [Consumer.tidOf, h2]
      omega
    · rw [clusterOfCta_eq hpre, h1]
      omega
  -- a cluster `c` whose lead thread exited processed task `t` as its task `E`
  have hstore : ∀ c E pc, c < 512 → (X.tr (leadOf L c r q)).getLast? = some ⟨pc, .exit⟩ →
      E < okPolls (Bar.loc L (leadOf L c r q / L.block) ⟨.clc, 0, true⟩) (X.tr (leadOf L c r q)) →
      (∀ t', t' < 512 → (E = 0 ∧ t' = c ∨ 0 < E ∧ ∃ i s tg, X.ClcIssue i s tg ∧
        i.1 / L.block = 2 * c ∧ issuesBefore L X c i.1 i.2 = E - 1 ∧
        X.clcState.response (Clc.requestId i) = some (some t')) → t' = t) →
      ∃ g k pc a sp c', X.get (g, k) = some ⟨pc, .tensorStore a sp⟩ ∧
        Frame.stateAt (code L) X g k = some (some (.inr (.cons c'))) ∧ c'.site = .tma s ∧
        c'.m = tileM t ∧ c'.n = tileN t ∧ g / L.block % 2 = r ∧ Consumer.tidOf L g / 32 / 4 = q ∧
        ∀ x y z, x < 32 → y < 128 → z < 2 → TensorStore.writeLoc sp x y z =
          some ((elementLoc P.dBase (outputRow (tileM t) r q y)
            (outputCol (tileN t) s.val x)).at z) := by
    intro c E pc hc hlast hE hcase
    obtain ⟨hg, hw, hf, -, hcc, hrk, hgq, -⟩ := hlead c hc
    obtain ⟨k, pcs, a, sp, c', he, hσ, hs, hk⟩ := exit_store hX ht hg hw hf (hub' _) hlast hE s
    obtain ⟨-, -, -, hm, hn, -, -, -, htile⟩ := ht.store_tile hg he hσ
    obtain ⟨t', htl', htt, hcase'⟩ := tile_task hpre hX ht hv hg (len_of_get he).le htile
    rw [hk, Nat.add_sub_cancel, hcc] at hcase'
    have htt' := hcase t' htl' hcase'
    subst htt'
    simp only [tileOf, Prod.mk.injEq] at htt
    have hmt : c'.m = tileM t' := by simp only [tileM]; omega
    have hnt : c'.n = tileN t' := by simp only [tileN]; omega
    refine ⟨_, k, pcs, a, sp, c', he, hσ, hs, hmt, hnt, hrk, hgq, fun x y z hx hy hz => ?_⟩
    rw [store_writeLoc hpre ht hg he hσ hs x y z hx hy hz, hmt, hnt, hrk, hgq]
  obtain ⟨hg0, hw0, -, -, -, -, -, hcl0⟩ := hlead t htl
  rcases hd.1 _ hg0 with ⟨-, r0, hown⟩ | ⟨pc0, hlast0⟩
  · -- task `t` was canceled by one request, of a cluster `c` that ran
    rw [hcl0] at hown
    have hresp := (owned hX).owner_response r0 t hown
    obtain ⟨i, sp, tg, rfl, hi⟩ := hX.clc.2.1 _ _ hresp
    obtain ⟨pci, hei⟩ := hi
    have hh := Frame.lt_of_get hX hei
    obtain ⟨hcta, -, -⟩ := issue_leader hpre hX ht hei
    set c := i.1 / L.block / 2 with hcdef
    have hc : c < 512 := by
      have : i.1 / L.block < 1024 := by
        rw [← hgrid]
        exact (Nat.div_lt_iff_lt_mul (by rw [hblock]; decide)).mpr hh
      omega
    obtain ⟨hg, hw, -, -, hcc, -, -, hclc⟩ := hlead c hc
    have hne : X.tr i.1 ≠ [] := by
      intro hn
      have := len_of_get hei
      simp only [hn, List.length_nil] at this
      omega
    have hlaunch := hX.clc.2.2.2.2 ⟨i, sp, tg, pci, hei⟩ i.1 hh hne
    have hcli : L.clusterOfCta (i.1 / L.block) = c := by
      rw [clusterOfCta_eq hpre]
    rw [hcli] at hlaunch
    rcases hd.1 _ hg with ⟨-, r1, hown1⟩ | ⟨pc1, hlast1⟩
    · rw [hclc, hlaunch] at hown1
      cases hown1
    have hET := exit_task hpre hX ht hv hag hg hw hlast1 ⟨pci, hei⟩ (by rw [hcc]) htl hresp
    refine hstore c (reqNo L X i + 1) pc1 hc hlast1 hET fun t' htl' hcase => ?_
    rcases hcase with ⟨h0, -⟩ | ⟨-, i', s', tg', hi', hic', hn', hres'⟩
    · omega
    · have h1 : reqNo L X i' = issuesBefore L X c i'.1 i'.2 := by
        simp only [reqNo]
        rw [show i'.1 / L.block / 2 = c by omega]
      have heq : i' = i := request_eq hpre hX ht hi' ⟨pci, hei⟩ (by omega)
        (by rw [h1, hn', Nat.add_sub_cancel])
      subst heq
      rw [hresp] at hres'
      exact (Option.some.inj (Option.some.inj hres')).symm
  · -- cluster `t` ran its own task first
    obtain ⟨-, j, -, -, -, -, -, -, -, -, -, -, -, -, -, hcnt⟩ :=
      ht.cons_exit_tiles hg0 hw0 hlast0
    refine hstore t 0 pc0 htl hlast0 (by omega) fun t' _ hcase => ?_
    rcases hcase with ⟨-, rfl⟩ | ⟨h0, -⟩
    · rfl
    · omega

end ClcRing

end

end PTX.Kernels.Fp16Gemm8192.Proof
