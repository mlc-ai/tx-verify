-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.NthEv
import Lemmas.Tmem.PairProtocol

public section

/-! # Named barrier positions of each actual lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NamedBarTrace

open PTX PTX.Flow Wg0BarrierTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat}

private inductive Phase where
  | gate
  | opening (block : Nat)
  | pair (block : Nat)
  | maximum (block : Nat)
  | sumInit
  | sumRead
  | tile (j : Fin 4)
  | closing

private def Phase.kind (L : Launch) (g : Nat) : Phase → Kind
  | .gate => .bar 0 none .sync
  | .pair _ => .bar (10 + warpOf L g % 2) (some 64) .sync
  | .closing => .bar 12 none .sync
  | _ => .bar 9 (some 128) .sync

private def Phase.rank (P : Params) (L : Launch) (g : Nat) : Phase → Nat
  | .gate => 0
  | .opening k => 1 + 3 * k
  | .pair k => 2 + 3 * k
  | .maximum k => 3 + 3 * k
  | .sumInit => 1 + 3 * Wg0.blocksOf P L g
  | .sumRead => 2 + 3 * Wg0.blocksOf P L g
  | .tile j => 3 + 3 * Wg0.blocksOf P L g + j.val
  | .closing => if wgOf L g = 0 then 7 + 3 * Wg0.blocksOf P L g else 1

private def Phase.admitted (P : Params) (L : Launch) (g : Nat) : Phase → Prop
  | .gate | .closing => True
  | .opening k | .pair k | .maximum k => wgOf L g = 0 ∧ k < Wg0.blocksOf P L g
  | .tile j => wgOf L g = 0 ∧ j.val < 4
  | _ => wgOf L g = 0

private def Phase.source (K : Kernel) (e : Event) : Phase → Prop
  | .gate => e.pc = Site.barrier.pc
  | .opening _ => e.pc = Wg0.Site.wg0Sync.pc
  | .pair _ => e.pc = Wg0.Site.pairBar.pc
  | .maximum _ => e.pc = Wg0.Site.wg0Sync2.pc
  | .sumInit => e.pc = Wg0.Site.lseBar.pc
  | .sumRead => e.pc = Wg0.Site.lseBar2.pc
  | .tile j => e.pc = (Wg0.Site.epiBar j).pc
  | .closing => K.alignedAt e.pc = false

private inductive Classified : Machine.ThreadD → Phase → Prop
  | gate : Classified (.prologue .barrier) .gate
  | opening {d : Wg0.D} : d.site = .wg0Sync → Classified (.wg0 d) (.opening d.block)
  | pair {d : Wg0.D} : d.site = .pairBar → Classified (.wg0 d) (.pair d.block)
  | maximum {d : Wg0.D} : d.site = .wg0Sync2 → Classified (.wg0 d) (.maximum d.block)
  | sumInit {d : Wg0.D} : d.site = .lseBar → Classified (.wg0 d) .sumInit
  | sumRead {d : Wg0.D} : d.site = .lseBar2 → Classified (.wg0 d) .sumRead
  | tile {d : Wg0.D} {j : Fin 4} : d.site = .epiBar j → Classified (.wg0 d) (.tile j)
  | closing {d : Machine.ThreadD} : ScoreClosingGate.ClosingSite d → Classified d .closing

private theorem classify {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {id : Nat} {count : Option Nat} {mode : BarMode}
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .bar id count mode) : ∃ phase, Classified d phase := by
  have hs := RingGateEvents.bar_site hf hk
  cases d
  case prologue s =>
    change s = .barrier at hs
    subst s
    exact ⟨.gate, .gate⟩
  case wg0 d =>
    rcases hs with hs | hs | hs | hs | hs | hs | ⟨j, hs⟩
    · exact ⟨.opening d.block, .opening hs⟩
    · exact ⟨.pair d.block, .pair hs⟩
    · exact ⟨.maximum d.block, .maximum hs⟩
    · exact ⟨.sumInit, .sumInit hs⟩
    · exact ⟨.sumRead, .sumRead hs⟩
    · exact ⟨.closing, .closing hs⟩
    · exact ⟨.tile j, .tile hs⟩
  case head => exact hs.elim
  case done => exact hs.elim
  all_goals exact ⟨.closing, .closing hs⟩

private theorem closing_source {d : Machine.ThreadD} {e : Event}
    (hc : ScoreClosingGate.ClosingSite d) (ht : e.pc = (Machine.code P L g).pc d) :
    kernel.alignedAt e.pc = false := by
  rw [ht]
  cases d
  case wg0 d =>
    change d.site = .everyone at hc
    change kernel.alignedAt d.site.pc = false
    rw [hc]
    change kernel.alignedAt 1835 = false
    simp [Kernel.alignedAt, Flow.code_bar_10, Op.aligned]
  case mma d =>
    change d.site = .outBar at hc
    change kernel.alignedAt d.site.pc = false
    rw [hc]
    change kernel.alignedAt 2160 = false
    simp [Kernel.alignedAt, Flow.code_bar_11, Op.aligned]
  case tma d =>
    change d.site = .barrier at hc
    change kernel.alignedAt d.site.pc = false
    rw [hc]
    change kernel.alignedAt 2330 = false
    simp [Kernel.alignedAt, Flow.code_bar_12, Op.aligned]
  case index d =>
    change d.site = .barrier at hc
    change kernel.alignedAt d.site.pc = false
    rw [hc]
    change kernel.alignedAt 2585 = false
    simp [Kernel.alignedAt, Flow.code_bar_13, Op.aligned]
  case idle s =>
    change s = .sync at hc
    subst s
    change kernel.alignedAt 2604 = false
    simp [Kernel.alignedAt, Flow.code_bar_14, Op.aligned]
  case wg2 d =>
    change d.site = .barrier at hc
    change kernel.alignedAt d.site.pc = false
    rw [hc]
    change kernel.alignedAt 3610 = false
    simp [Kernel.alignedAt, Flow.code_bar_15, Op.aligned]
  all_goals exact hc.elim

private theorem event_matches {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {p : Phase} (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hp : Classified d p) :
    e.kind = p.kind L g ∧ p.source kernel e ∧ p.admitted P L g := by
  have hTag : e.pc = (Machine.code P L g).pc d := by
    obtain ⟨_, hat, hf⟩ := hf
    exact (fires_pc hf).trans hat.1.1
  cases hp
  case gate =>
    obtain ⟨_, _, hFire⟩ := RingGateEvents.fired_at_code hf Flow.code_bar_0
    exact ⟨congrArg Event.kind hFire.1, hTag, trivial⟩
  case closing hc =>
    exact ⟨ScoreClosingGate.closing_kind hpre hf hc, closing_source hc hTag, trivial⟩
  case pair d hs =>
    have hi : Wg0.Inv P L g d := (Exists.choose_spec hf).1.2
    exact ⟨Wg0PeerTrace.pair_kind hpre hf hs, hTag.trans (congrArg Wg0.Site.pc hs),
      hi.wg, hi.blockLt⟩
  all_goals
    rename_i hs
    have hi : Wg0.Inv P L g _ := (Exists.choose_spec hf).1.2
    refine ⟨Wg0BarrierTrace.bar9_kind hpre hf (by rw [hs]; trivial),
      hTag.trans (congrArg Wg0.Site.pc hs), ?_⟩
    first | exact ⟨hi.wg, hi.blockLt⟩ | exact ⟨hi.wg, Fin.isLt _⟩ | exact hi.wg

private theorem bar_form {e : Event} (h : Execution.isBar e = true) :
    ∃ id count mode, e.kind = .bar id count mode := by
  obtain ⟨_, kind⟩ := e
  cases kind <;> simp only [Execution.isBar, Bool.false_eq_true] at h
  exact ⟨_, _, _, rfl⟩

private theorem previous_of_mem {e : Event} (hm : e ∈ (X.tr g).take i) :
    ∃ j < i, X.get (g, j) = some e := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  have hlt : j < i := by simp only [List.length_take] at hj; omega
  have hjl : j < (X.tr g).length := by simp only [List.length_take] at hj; omega
  exact ⟨j, hlt, List.getElem?_eq_some_iff.mpr ⟨hjl, by simpa using he⟩⟩

private theorem gate_of_id_zero (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {e : Event} (he : X.get (g, i) = some e) (hc : Execution.isBarId 0 e = true) :
    Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)) := by
  obtain ⟨_, _, _, rfl⟩ := NamedBar.isBarId_form hc
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  rwa [(RingGateEvents.gate_source hf rfl).1] at hd

private theorem gate_count_max (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ((X.tr g).take i).countP (Execution.isBarId 0) ≤ 1 := by
  by_contra hn
  let p := Execution.isBarId 0
  obtain ⟨j, _, hj, hp, ho⟩ :=
    Tmem.Pair.countP_take_occ p (X.tr g) i 0 (by dsimp [p]; omega)
  obtain ⟨k, _, hk, hp', ho'⟩ :=
    Tmem.Pair.countP_take_occ p (X.tr g) i 1 (by dsimp [p]; omega)
  have hGet : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
  have hGet' : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hk
  obtain rfl := RingInitSources.gate_state_unique hGet hGet'
    (gate_of_id_zero hX hs ht hGet hp) (gate_of_id_zero hX hs ht hGet' hp')
  omega

private theorem gate_count_role (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {d : Machine.ThreadD} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hRole : ∀ s, d ≠ .prologue s) :
    ((X.tr g).take i).countP (Execution.isBarId 0) = 1 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨k, e', hk, he', hKind, _⟩ :=
    RingInitSources.gate_before_role hX (hs g hg).machine ht he hd hRole
  have hc : Execution.isBarId 0 e' = true := by simp [Execution.isBarId, hKind]
  have hSucc := PTX.Flow.countP_take_succ he' hc
  have hLe := PTX.Flow.countP_take_mono (Execution.isBarId 0) (X.tr g) (by omega : k + 1 ≤ i)
  have hMax := gate_count_max (g := g) (i := i) hX hs ht
  omega

private theorem no_bar_before_gate (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier))) :
    ((X.tr g).take i).countP Execution.isBar = 0 := by
  by_contra hn
  obtain ⟨j, hj, hjl, hBar, _⟩ :=
    Tmem.Pair.countP_take_occ Execution.isBar (X.tr g) i 0 (by omega)
  let f := (X.tr g)[j]
  have hGet : X.get (g, j) = some f := List.getElem?_eq_getElem hjl
  obtain ⟨id, count, mode, hk⟩ := bar_form hBar
  have hg := Frame.lt_of_get hX hGet
  obtain ⟨d, _, hd', hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht hGet (by
      intro fault h
      rw [hk] at h
      cases h)
  by_cases hPro : ∃ s, d = .prologue s
  · obtain ⟨s, rfl⟩ := hPro
    have hSite : s = .barrier := RingGateEvents.bar_site hf hk
    subst s
    have h := RingInitSources.gate_state_unique he hGet hd hd'
    omega
  · obtain ⟨k, ev, hk, hev, _, hGate⟩ :=
      RingInitSources.gate_before_role hX (hs g hg).machine ht hGet hd'
        (fun s h => hPro ⟨s, h⟩)
    have h := RingInitSources.gate_state_unique he hev hd hGate
    omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem prefix_sum {e : Event} (he : X.get (g, i) = some e) {id : Nat} {count : Option Nat}
    {mode : BarMode} (hBar : e.kind = .bar id count mode) :
    let pre := (X.tr g).take i
    pre.countP Execution.isBar = pre.countP (Execution.isBarId 0) +
      pre.countP (Execution.isBarId 9) + pre.countP (Execution.isBarId (10 + warpOf L g % 2)) := by
  let pre := (X.tr g).take i
  let pair := 10 + warpOf L g % 2
  have hPair : 10 ≤ pair ∧ pair < 12 := by dsimp [pair]; omega
  have cover (f : Event) (hm : f ∈ pre) (hfBar : Execution.isBar f = true) :
      Execution.isBarId 0 f = true ∨
      Execution.isBarId 9 f = true ∨ Execution.isBarId pair f = true := by
    obtain ⟨j, hlt, hGet⟩ := previous_of_mem hm
    obtain ⟨b, c, m, hk⟩ := bar_form hfBar
    have hg := Frame.lt_of_get hX hGet
    obtain ⟨_, _, _, hf⟩ :=
      RingSourceSites.fired_from_trace hX (hs g hg).machine ht hGet (by
        intro fault h
        rw [hk] at h
        cases h)
    obtain ⟨p, hp⟩ := classify hf hk
    have hKind := (event_matches hpre hf hp).1
    cases p <;> simp [Execution.isBarId, Phase.kind, hKind, pair]
    case closing =>
      have hEvent : f = ⟨f.pc, .bar 12 none .sync⟩ := by
        cases f
        exact congrArg (Event.mk _) hKind
      have hClose := hGet.trans (congrArg some hEvent)
      exact (ScoreClosingGate.no_bar_after_closing hpre hX hs ht hClose he hlt hBar).elim
  have hsCount : ∀ l : List Event,
      (∀ f ∈ l, Execution.isBar f = true →
        Execution.isBarId 0 f = true ∨ Execution.isBarId 9 f = true ∨
          Execution.isBarId pair f = true) →
      l.countP Execution.isBar = l.countP (Execution.isBarId 0) +
        l.countP (Execution.isBarId 9) + l.countP (Execution.isBarId pair) := by
    intro l h
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons,
        ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
      by_cases hf : Execution.isBar f = true
      · have exclude {b c : Nat} (hne : b ≠ c) (hb : Execution.isBarId b f = true) :
            Execution.isBarId c f = false :=
          Bool.eq_false_of_not_eq_true fun hc => hne (NamedBar.id_eq_of_isBarId hb hc)
        rcases h f List.mem_cons_self hf with h0 | h9 | hpair
        · have hn9 := exclude (by decide : 0 ≠ 9) h0
          have hnp := exclude (by omega : 0 ≠ pair) h0
          simp [hf, h0, hn9, hnp]
          omega
        · have hn0 := exclude (by decide : 9 ≠ 0) h9
          have hnp := exclude (by omega : 9 ≠ pair) h9
          simp [hf, hn0, h9, hnp]
          omega
        · have hn0 := exclude (by omega : pair ≠ 0) hpair
          have hn9 := exclude (by omega : pair ≠ 9) hpair
          simp [hf, hn0, hn9, hpair]
          omega
      · have hZero (b : Nat) : Execution.isBarId b f = false :=
          Bool.eq_false_of_not_eq_true fun h => hf (NamedBar.isBar_of_isBarId h)
        simp [hf, hZero]
  exact hsCount pre cover

private theorem no_soft_prefix (hWG : wgOf L g ≠ 0) {b : Nat} (hb : b = 9 ∨ b = 10 + warpOf L g % 2)
    :
    ((X.tr g).take i).countP (Execution.isBarId b) = 0 := by
  by_contra hn
  obtain ⟨j, _, hj, hBar, _⟩ :=
    Tmem.Pair.countP_take_occ (Execution.isBarId b) (X.tr g) i 0 (by omega)
  have hGet : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
  obtain ⟨tag, count, mode, hKind⟩ := NamedBar.isBarId_form hBar
  rw [hKind] at hGet
  have hg := Frame.lt_of_get hX hGet
  obtain ⟨_, _, _, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht hGet (by simp)
  obtain ⟨phase, hp⟩ := classify hf rfl
  obtain ⟨hShape, _, hAdmitted⟩ := event_matches hpre hf hp
  cases phase <;> try exact (hWG hAdmitted.1).elim
  case gate =>
    have hId : b = 0 := (Kind.bar.inj hShape).1
    rcases hb with hb | hb <;> omega
  case closing =>
    have hId : b = 12 := (Kind.bar.inj hShape).1
    rcases hb with hb | hb <;> omega
  all_goals exact (hWG hAdmitted).elim

omit hpre hX hs ht in
private def canBeWg0 : Option Machine.ThreadD → Prop
  | none | some (.prologue _) | some (.wg0 _) | some .done => True
  | _ => False

omit hpre hX hs ht in
private theorem wg0_next {d d' : Option Machine.ThreadD} {e : Event}
    (hw : wgOf L g = 0) (hd : canBeWg0 d) (hn : (Machine.machine P L g).next d e = some d') :
    canBeWg0 d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn with hg
          · have hw0 : w = 0 := Fin.ext (hg.symm.trans hw)
            subst w
            cases hn
            trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case wg0 d =>
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial
    case done => cases hn
    all_goals exact hd.elim

omit hpre hX hs ht in
private theorem wg0_at (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) {d : Machine.ThreadD} {e : Event}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hw : wgOf L g = 0) : canBeWg0 (some d) :=
  (hs.produces (hX.thr g (Frame.lt_of_get hX he))).prefix_induction
    (fun q _ => canBeWg0 q) trivial (fun _ _ _ _ _ h _ hn => wg0_next hw h hn)
    i (some d) hd

private theorem rank_at {d : Machine.ThreadD} {e : Event} {o : Option TState} {p : Phase}
    (he : X.get (g, i) = some e) (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hf : (Machine.machine P L g).Fired (some d) e o) (hp : Classified d p) {id : Nat}
    {count : Option Nat} {mode : BarMode} (hBar : e.kind = .bar id count mode) :
    ((X.tr g).take i).countP Execution.isBar = p.rank P L g := by
  have hSound := (hs g (Frame.lt_of_get hX he)).machine
  have hSum := prefix_sum hpre hX hs ht he hBar
  dsimp only at hSum
  cases hp
  case gate => exact no_bar_before_gate hX hs ht he hd
  case closing hClosing =>
    have hRole : ∀ s, d ≠ .prologue s := by
      intro s h
      subst d
      exact hClosing
    have hGate := gate_count_role hX hs ht he hd hRole
    by_cases hw : wgOf L g = 0
    · have hWg := wg0_at hX hSound he hd hw
      have hSoft : ∃ q, d = .wg0 q := by
        cases d <;> first | exact ⟨_, rfl⟩ | exact hClosing.elim | exact hWg.elim
      obtain ⟨q, rfl⟩ := hSoft
      have hSite : q.site = .everyone := hClosing
      have hNine := Wg0BarrierCount.count_at_wg0 hpre hX hSound he hd
      have hPair := Wg0PeerTrace.count_at_wg0 hpre hX hSound he hd
      have hInv : Wg0.Inv P L g q := (Exists.choose_spec hf).1.2
      have hLast := hInv.epilogueLast (by rw [hSite]; rfl)
      simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hSite] at hNine
      simp only [Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, hSite] at hPair
      simp only [Phase.rank, hw, ↓reduceIte]
      omega
    · have hNine := no_soft_prefix (i := i) hpre hX hs ht hw (.inl rfl)
      have hPair := no_soft_prefix (i := i) hpre hX hs ht hw (.inr rfl)
      simp only [Phase.rank, hw, ↓reduceIte]
      omega
  all_goals
    have hGate := gate_count_role hX hs ht he hd (by simp)
    have hNine := Wg0BarrierCount.count_at_wg0 hpre hX hSound he hd
    have hPair := Wg0PeerTrace.count_at_wg0 hpre hX hSound he hd
    rename_i hSite
    have hInv : Wg0.Inv P L g _ := (Exists.choose_spec hf).1.2
    have hLast := hInv.epilogueLast
    simp only [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hSite] at hNine
    simp only [Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, hSite] at hPair
    simp only [hSite, Wg0.Site.inEpilogue, Bool.false_eq_true, false_implies,
      true_implies] at hLast
    simp only [Phase.rank]
    omega

omit hpre hX hs ht in
private theorem phase_injective {p q : Phase} {h : Nat}
    (hWg : wgOf L g = wgOf L h) (hBlocks : Wg0.blocksOf P L g = Wg0.blocksOf P L h)
    (hP : p.admitted P L g) (hQ : q.admitted P L h)
    (hr : p.rank P L g = q.rank P L h) : p = q := by
  by_cases hw : wgOf L g = 0
  · have hw' : wgOf L h = 0 := hWg.symm.trans hw
    cases p <;> cases q <;>
      simp only [Phase.rank, Phase.admitted, hw, hw', hBlocks, ↓reduceIte, true_and] at *
    all_goals first | omega | (congr 1; omega)
  · have hw' : wgOf L h ≠ 0 := fun hh => hw (hWg.trans hh)
    cases p <;> cases q <;>
      simp only [Phase.rank, Phase.admitted, hw, hw', ↓reduceIte, false_and] at *
    all_goals contradiction

private theorem phase_event {tag id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g, i) = some ⟨tag, .bar id count mode⟩) :
    ∃ p : Phase, ((X.tr g).take i).countP Execution.isBar = p.rank P L g ∧
      p.admitted P L g ∧ p.source kernel ⟨tag, .bar id count mode⟩ ∧
      .bar id count mode = p.kind L g := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  obtain ⟨p, hp⟩ := classify hf rfl
  obtain ⟨heq, hsrc, hadm⟩ := event_matches hpre hf hp
  exact ⟨p, rank_at hpre hX hs ht he hd hf hp rfl, hadm, hsrc, heq⟩

/-- Each barrier ID determines the participant count of every actual arrival. -/
theorem count_of_id {tag id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g, i) = some ⟨tag, .bar id count mode⟩) :
    count = if id = 9 then some 128 else if id = 10 ∨ id = 11 then some 64 else none := by
  obtain ⟨p, _, _, _, hKind⟩ := phase_event hpre hX hs ht he
  cases p <;> simp only [Phase.kind, Kind.bar.injEq] at hKind <;>
    obtain ⟨rfl, rfl, rfl⟩ := hKind
  case pair =>
    have hParity : warpOf L g % 2 = 0 ∨ warpOf L g % 2 = 1 := by omega
    rcases hParity with h | h <;> simp [h]
  all_goals decide

/-- The actual barrier operands fall into the launch, softmax, pair and closing gates. -/
theorem gate_operands {tag id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g, i) = some ⟨tag, .bar id count mode⟩) :
    X.IsBarrier (g, i) 0 none tag ∨ X.IsBarrier (g, i) 9 (some 128) tag ∨
      (∃ p : Fin 2, X.IsBarrier (g, i) (10 + p.val) (some 64) tag) ∨
      X.IsBarrier (g, i) 12 none tag := by
  obtain ⟨p, _, _, _, hKind⟩ := phase_event hpre hX hs ht he
  cases p <;> simp only [Phase.kind, Kind.bar.injEq] at hKind <;>
    obtain ⟨rfl, rfl, rfl⟩ := hKind
  case gate => exact .inl he
  case pair =>
    exact .inr (.inr (.inl ⟨⟨warpOf L g % 2, Nat.mod_lt _ (by decide)⟩, he⟩))
  case closing => exact .inr (.inr (.inr he))
  all_goals exact .inr (.inl he)

/-- Same-warp named barriers with the same ordinal use the same operands and aligned source. -/
theorem agree {h j tag tag' id id' : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    (hw : SameWarp L g h) (he : X.get (g, i) = some ⟨tag, .bar id count mode⟩)
    (he' : X.get (h, j) = some ⟨tag', .bar id' count' mode'⟩)
    (hOrd : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    id = id' ∧ count = count' ∧
      ((kernel.alignedAt tag || kernel.alignedAt tag') = true → tag = tag') := by
  obtain ⟨p, hp, ha, hSrc, hKind⟩ := phase_event hpre hX hs ht he
  obtain ⟨q, hq, hb, hSrc', hKind'⟩ := phase_event hpre hX hs ht he'
  have hWarp : warpOf L g = warpOf L h := by
    have h := hw.2
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using h
  have hGroup : wgOf L g = wgOf L h := by unfold warpOf at hWarp; unfold wgOf; omega
  have hBlock : Wg0.blocksOf P L g = Wg0.blocksOf P L h := by
    have hCta := hw.1.2.2
    simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, ctaOf, hCta]
  have hEq := phase_injective hGroup hBlock ha hb (hp.symm.trans (hOrd.trans hq))
  subst q
  have hPred : p.kind L g = p.kind L h := by cases p <;> simp [Phase.kind, hWarp]
  obtain ⟨hId, hCount, _⟩ := Kind.bar.inj (hKind.trans (hPred.trans hKind'.symm))
  refine ⟨hId, hCount, ?_⟩
  intro hAligned
  cases p <;> simp only [Phase.source] at hSrc hSrc'
  case closing => simp [hSrc, hSrc'] at hAligned
  all_goals exact hSrc.trans hSrc'.symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NamedBarTrace
