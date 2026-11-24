-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Order.ElectOrdinal
public import Lemmas.Order.WarpBarOrdinal
public import Lemmas.Step.WarpShfl
public import Lemmas.Step.WarpVote
public import Lemmas.Step.WarpElect
public import Lemmas.Step.WarpBar
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Flow.NotBulk
public import Lemmas.MBarrier.BarWaiting
public import Lemmas.Flow.VoteSeq

@[expose] public section

/-! # Progress at the warp collectives

A warp collective (`shfl.sync`, `elect.sync`, `bar.warp.sync`, `vote.sync`) is performed by the
lanes of a warp together: Core admits a lane's event only with the events of the other lanes of
its instance (DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER, DEP-WARP-VOTE). `isWarpColl`
counts them, and `kindShape` reads an event's static part (`CollShape`: the shuffle's mode and
lane operands, or the member mask).

* **No lane is ahead** (`no_ahead`). When a lane's `n`-th warp collective has a static part fixed
  by its warp and `n`, with full masks (`WarpRec`), the number of shuffles, elections, warp
  barriers and ballots among a lane's first `n` collectives is a function of the warp and `n`
  (`count_shape`). A lane `h` that has made more collectives than a lane `g` that has not exited
  has made its `n`-th, `n` the number `g` has made; that event has returned, so its needs are
  filled (DEP-ORDER): `g` has an event of the same kind and ordinal, which it has not made. A
  ballot's ordinal counts the mode votes with its mask too, so a kernel without mode votes is
  assumed (`no_voteMode`).
* **A lane is released** with a released lane of its warp at the same collective when its last
  event never blocks (`Unblocking`, `released_of_unblocking`), is the same register request
  (`released_of_reg`), or a warp-collective `tcgen05` event of the same ordinal
  (`released_of_tc`).
* **The warp performs one instance** (`coll_batch`) when every lane is released and reaches, by
  local steps, a template of one static part at one position (`LanesAt`): a shuffle, an election,
  a warp barrier or a ballot. -/

namespace PTX.Sched

open PTX Classical

noncomputable section

/-- A warp-collective event: a shuffle, an election, a warp barrier or a ballot. -/
def isWarpColl : Event → Bool
  | ⟨_, .shfl ..⟩ | ⟨_, .elect ..⟩ | ⟨_, .warpBar ..⟩ | ⟨_, .vote ..⟩ => true
  | _ => false

/-- The static part of a warp collective: the shuffle's mode and lane operands, or the member
mask of an election, a warp barrier or a ballot. -/
inductive CollShape where
  | shfl (mode : ShflMode) (b c : Nat)
  | elect (mask : Nat)
  | warpBar (mask : Nat)
  | vote (mask : Nat)

/-- The static part of a warp-collective event kind. -/
def kindShape : Kind → Option CollShape
  | .shfl m _ b c _ _ => some (.shfl m b c)
  | .elect mask _ _ => some (.elect mask)
  | .warpBar mask _ => some (.warpBar mask)
  | .vote mask _ _ => some (.vote mask)
  | _ => none

/-- The static part of a warp-collective template. -/
def tmplShape : Tmpl → Option CollShape
  | .shfl m _ b c _ => some (.shfl m b c)
  | .elect mask _ => some (.elect mask)
  | .warpBar mask _ => some (.warpBar mask)
  | .vote mask _ _ => some (.vote mask)
  | _ => none

/-- The member mask names every lane of the warp (a shuffle has none). -/
def CollShape.Full : CollShape → Prop
  | .shfl .. => True
  | .elect m | .warpBar m | .vote m => m = 4294967295

/-- A kind of last event that never blocks its thread: no cluster-barrier operation, register
request, warp-collective `tcgen05` event (the paired Tensor Memory operations among them), named
barrier or bulk or `cp.async` group wait (`Step.Released`). An MMA or a commit (`tcgen05.mma`,
`tcgen05.commit`) is issued by one thread and does not block it. -/
def Unblocking : Kind → Prop
  | .cluster .. | .setMaxReg .. | .bar .. | .bulkWait .. | .asyncWait _ => False
  | .tc kd => isTcColl { pc := 0, kind := .tc kd } = false
  | _ => True

/-- The kind of a warp collective's static part: shuffle, election, warp barrier, ballot. -/
def CollShape.tag : CollShape → Nat
  | .shfl .. => 0 | .elect _ => 1 | .warpBar _ => 2 | .vote _ => 3

/-- Every lane is a member of the full mask. -/
theorem full_member {lane : Nat} (hl : lane < 32) : electMember 4294967295 lane := by
  refine ⟨hl, ?_⟩
  have h32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
  rw [h32, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hl

/-- **The events of one kind among a lane's first warp collectives** are counted by the static
parts, a function of the warp and the ordinal. -/
theorem count_shape {κ : Type} (F : κ → Nat → CollShape) (c : κ) {l : List Event}
    (hrec : ∀ k e, l[k]? = some e → isWarpColl e = true →
      kindShape e.kind = some (F c ((l.take k).countP isWarpColl)))
    (q : Event → Bool) (r : CollShape → Bool) (hq : ∀ e, q e = true → isWarpColl e = true)
    (hqr : ∀ e s, kindShape e.kind = some s → q e = r s) :
    ∀ k, k ≤ l.length → (l.take k).countP q =
      (List.range ((l.take k).countP isWarpColl)).countP (fun i => r (F c i)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hlt : k < l.length := by omega
    have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hget, Option.toList_some, List.countP_append, List.countP_append,
      ih (by omega)]
    by_cases hc : isWarpColl l[k] = true
    · have hs := hrec k _ hget hc
      simp [hc, List.range_succ, hqr _ _ hs]
    · have hqf : q l[k] = false := by
        cases h : q l[k]
        · rfl
        · exact absurd (hq _ h) hc
      simp [hqf, hc]

/-- The kind tests of the four warp collectives. -/
theorem shfl_tag (e : Event) (s : CollShape) (h : kindShape e.kind = some s) :
    Execution.isShfl e = (s.tag == 0) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [kindShape] at h <;> subst h <;> rfl

theorem elect_tag (e : Event) (s : CollShape) (h : kindShape e.kind = some s) :
    isElectEv e = (s.tag == 1) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [kindShape] at h <;> subst h <;> rfl

theorem warpBar_tag (e : Event) (s : CollShape) (h : kindShape e.kind = some s) :
    Execution.isWarpBar e = (s.tag == 2) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [kindShape] at h <;> subst h <;> rfl

theorem vote_tag (e : Event) (s : CollShape) (h : kindShape e.kind = some s) :
    Flow.isBallot e = (s.tag == 3) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [kindShape] at h <;> subst h <;> rfl

theorem shfl_coll (e : Event) (h : Execution.isShfl e = true) : isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e; cases k <;> simp_all [Execution.isShfl, isWarpColl]

theorem elect_coll (e : Event) (h : isElectEv e = true) : isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e; cases k <;> simp_all [isElectEv, isWarpColl]

theorem warpBar_coll (e : Event) (h : Execution.isWarpBar e = true) : isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e; cases k <;> simp_all [Execution.isWarpBar, isWarpColl]

theorem vote_coll (e : Event) (h : Flow.isBallot e = true) : isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e; cases k <;> simp_all [Flow.isBallot, isWarpColl]

/-! ### Kernels without mode votes -/

/-- A template that fires no mode vote (`vote.sync` with `.all`, `.any` or `.uni`). -/
def NotVoteMode : Tmpl → Prop
  | .voteMode .. => False
  | _ => True

/-- Whether an instruction is a mode vote. -/
def voteModeOp : Op → Bool
  | .warp w => match w.kind with
    | .vote .ballot _ => false
    | .vote _ _ => true
    | _ => false
  | _ => false

theorem widen_notVoteMode {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotVoteMode m) :
    NotVoteMode (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notVoteMode {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotVoteMode r) :
    NotVoteMode (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than a mode vote fires no mode vote. -/
theorem eventTmpl_notVoteMode {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : voteModeOp op = false) : NotVoteMode (eventTmpl A L g t op) := by
  have hw : ∀ m pc, NotVoteMode m → NotVoteMode (m.thenWaitLd pc) := fun m _ h => by
    cases m <;> trivial
  cases op
  case warp w =>
    simp only [eventTmpl, warpTmpl]
    split
    case h_3 =>
      rename_i mode _ _ _ _ hb _ hk _ _ _
      simp only [voteModeOp, hk] at hop
      cases mode <;> simp_all
    all_goals try simp only [shflTmpl, voteTmpl, reduxTmpl, matchTmpl,
      activemaskTmpl, electTmpl, warpBarTmpl]
    all_goals repeat' first
      | trivial
      | split
  all_goals simp only [eventTmpl]
  all_goals try refine Flow.tcLdTmpl_pres hw (fun _ => trivial) ?_
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notVoteMode
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVoteMode)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notVoteMode)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A mode vote is fired by a mode vote instruction. -/
theorem fires_voteMode_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {mode : VoteMode} {m : Nat} {a d : Bool} (hk : e.kind = .voteMode mode m a d) :
    voteModeOp op = true := by
  cases hq : voteModeOp op
  · exfalso
    have hm := eventTmpl_notVoteMode (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotVoteMode] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- **A kernel without mode-vote instructions performs no mode vote.** -/
theorem no_voteMode {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hK : K.code.all (fun ins => !voteModeOp ins.op) = true) (hX : Consistent L K A mem0 X)
    {i : EvId} {pc : Nat} {mode : VoteMode} {m : Nat} {a d : Bool} :
    X.get i ≠ some ⟨pc, .voteMode mode m a d⟩ :=
  fun he => Flow.no_kind_of_code hX voteModeOp (fun k => ∃ mode m a d, k = .voteMode mode m a d)
    (fun _ ⟨_, _, _, _, h⟩ => by cases h) (fun hf ⟨_, _, _, _, hk⟩ => fires_voteMode_op hf hk)
    hK he ⟨_, _, _, _, rfl⟩

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Flow.Code K A L g} {κ : Type} {key : Nat → κ}

/-- **The recorded static parts**: a lane's `n`-th warp collective has the static part `F c n`
of its warp's key `c`, every mask naming the whole warp. -/
def WarpRec (C : (g : Nat) → Flow.Code K A L g) (X : Execution) (key : Nat → κ) : Prop :=
  ∃ F : κ → Nat → CollShape, (∀ c n, (F c n).Full) ∧
    ∀ {g k : Nat} {e : Event} {d : (C g).D}, g < L.threads → Frame.stateAt C X g k = some (some d) →
      X.get (g, k) = some e → isWarpColl e = true →
      kindShape e.kind = some (F (key g) (((X.tr g).take k).countP isWarpColl))

/-- The recorded static parts, for every launched thread of a safe tracked execution. -/
theorem shape_rec (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).Sound) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) {F : κ → Nat → CollShape}
    (hrec : ∀ {g k : Nat} {e : Event} {d : (C g).D}, g < L.threads →
      Frame.stateAt C X g k = some (some d) → X.get (g, k) = some e → isWarpColl e = true →
      kindShape e.kind = some (F (key g) (((X.tr g).take k).countP isWarpColl)))
    {x : Nat} (hx : x < L.threads) :
    ∀ k e, (X.tr x)[k]? = some e → isWarpColl e = true →
      kindShape e.kind = some (F (key x) (((X.tr x).take k).countP isWarpColl)) := by
  intro k e he hc
  obtain ⟨d, hd⟩ := Frame.state_of_noUb hsound hX htr hub (g := x) (k := k) he
  exact hrec hx hd he hc

/-- A recorded warp collective of a launched thread has a full mask, when its kind has one. -/
theorem rec_full {F : κ → Nat → CollShape} (hfull : ∀ c n, (F c n).Full)
    {c : κ} {n : Nat} {e : Event} {s : CollShape}
    (hs : kindShape e.kind = some (F c n)) (he : kindShape e.kind = some s) : s.Full := by
  rw [he] at hs
  rw [Option.some.inj hs]
  exact hfull c n

/-- A recorded warp collective with a member mask has the full mask. -/
theorem rec_mask (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).Sound) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) (hw : WarpRec C X key) {x k : Nat} {e : Event} {s : CollShape}
    (he : X.get (x, k) = some e) (hc : isWarpColl e = true) (hs : kindShape e.kind = some s) :
    s.Full := by
  obtain ⟨F, hfull, hrec⟩ := id hw
  have hx : x < L.threads := by
    by_contra hx
    have := len_of_get he
    rw [hX.outside x (by omega)] at this
    simp at this
  exact rec_full hfull (shape_rec hX hsound htr hub hrec hx k e he hc) hs

/-- **No lane is past a lane that has not exited.** A lane of the warp of `g`, whose run has
not stopped, has made at most as many warp collectives as `g`. -/
theorem no_ahead (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
    (hk : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).Sound) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) (hw : WarpRec C X key) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    (hlt : (X.tr g).countP isWarpColl < (X.tr h).countP isWarpColl) : False := by
  obtain ⟨F, hfull, hrec⟩ := id hw
  have hh : h < L.threads := hs.1.2.1
  have hsh : SameWarp L h g := sameWarp_symm hs
  have hkey : key h = key g := (hk hs).symm
  have hrg := shape_rec hX hsound htr hub hrec hg
  have hrh := shape_rec hX hsound htr hub hrec hh
  obtain ⟨j, e, hj, hc, hjn⟩ := MbarRing.Slot.exists_nth_countP isWarpColl
    (xs := X.tr h) (c := (X.tr g).countP isWarpColl) hlt
  have hjl : j ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp hj).1.le
  have hse := hrh j e hj hc
  rw [hjn, hkey] at hse
  -- the events of a kind before `h`'s `n`-th warp collective are as many as in `g`'s trace
  have cnt : ∀ (q : Event → Bool) (i : Nat), (∀ e, q e = true → isWarpColl e = true) →
      (∀ e s, kindShape e.kind = some s → q e = (s.tag == i)) →
      ((X.tr h).take j).countP q = (X.tr g).countP q := by
    intro q i hq hqr
    rw [count_shape F (key h) hrh q (fun s => s.tag == i) hq hqr j hjl,
      ← List.take_length (l := X.tr g),
      count_shape F (key g) hrg q (fun s => s.tag == i) hq hqr _ le_rfl, hjn, hkey,
      List.take_length]
  have hnx : ∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩ := fun k pc hk => hr.no_exit hk
  have hlg : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [isWarpColl, Bool.false_eq_true] at hc
  case shfl m a b c recv ok =>
    have hc' := cnt Execution.isShfl 0 shfl_coll shfl_tag
    rcases Step.shfl_lane_of_ready hX hj ⟨⟨_, _, _, _, _, _, _, hj⟩, rfl⟩ hsh with
      ⟨j', hk'⟩ | ⟨k, pce, hex, -⟩
    · have := Step.ShflK.lt_count hk'
      simp only at this
      omega
    · exact hnx k pce hex
  case elect mask inst leader =>
    have hc' := cnt isElectEv 1 elect_coll elect_tag
    have hef : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l →
        mask = 4294967295 := fun {e} _ _ _ _ he' =>
      rec_mask hX hsound htr hub hw (x := e.1) (k := e.2) he' rfl rfl
    have hel : X.Elect (h, j) pc mask inst leader := hj
    have hmem : ∀ {x y} z pc' m i l, X.Elect (x, z) pc' m i l → electMember m (laneOf L y) :=
      fun z _ _ _ _ he' => by
        rw [hef he']; exact full_member (Nat.mod_lt _ (by decide))
    obtain ⟨x, hp⟩ := ElectOrd.partner hX hsh hel (hmem j _ _ _ _ hel)
    have heq := ElectOrd.ordinal_eq hX hsh (fun z => hmem z) (fun z => hmem z) hp
    obtain ⟨_, _, _, _, _, _, _, -, hx⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hx)
    have := PTX.countP_take_lt (p := isElectEv) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [elections] at heq
    omega
  case warpBar mask inst =>
    have hc' := cnt Execution.isWarpBar 2 warpBar_coll warpBar_tag
    have hmask : ∀ {x} (hx : x < L.threads) {y m i}, X.WarpBar (x, y) m i → m = 4294967295 := by
      intro x hx y m i ⟨p, hp⟩
      exact rec_full hfull (shape_rec hX hsound htr hub hrec hx y _ hp rfl) rfl
    have hwb : X.WarpBar (h, j) mask inst := ⟨pc, hj⟩
    obtain ⟨x, hp⟩ := WarpBar.partner hX hsh hwb (by rw [hmask hh hwb]; exact full_member hlg)
    have heq := WarpBar.ordinal_eq hX hsh
      (fun y m i hy => by rw [hmask hh hy]; exact full_member hlg)
      (fun y m i hy => by rw [hmask hg hy]; exact full_member (Nat.mod_lt _ (by decide))) hp
    obtain ⟨_, _, -, p', hp'⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hp')
    have := PTX.countP_take_lt (p := Execution.isWarpBar) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [warpBars] at heq
    omega
  case vote mask a ballot =>
    have hc' := cnt Flow.isBallot 3 vote_coll vote_tag
    have hm : mask = 4294967295 := rec_full hfull hse rfl
    subst hm
    -- a vote event of a launched thread counts as a full-mask vote exactly when it is a ballot
    have hvc : ∀ x, x < L.threads → ∀ ev ∈ X.tr x,
        (voteClass ev.kind).any (·.mask == 4294967295) = true ↔ Flow.isBallot ev = true := by
      intro x hx ev hev
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hev
      have hget : X.get (x, k) = some (X.tr x)[k] := List.getElem?_eq_getElem hk
      revert hget
      generalize (X.tr x)[k] = ev
      intro hget
      obtain ⟨pc', kd⟩ := ev
      cases kd <;> simp [voteClass, Flow.isBallot]
      case vote m' a' b' => exact rec_mask hX hsound htr hub hw hget rfl rfl
      case voteMode md m' a' d' => exact fun _ => no_voteMode hK hX hget
    have hbit : (4294967295 : Nat).testBit (laneOf L g) = true := (full_member hlg).2
    have hk : X.MaskK voteClass (h, j) 4294967295 (((X.tr h).take j).countP
        fun ev => (voteClass ev.kind).any (·.mask == 4294967295)) := ⟨⟨_, _, hj, rfl, rfl⟩, rfl⟩
    rcases Step.vote_lane_of_ready hX hk hsh hbit with ⟨j', hk'⟩ | ⟨k, pce, hex⟩
    · have hlt := Step.MaskK.lt_count hk'
      unfold Step.maskCount at hlt
      rw [List.countP_congr (hvc g hg), List.countP_congr
        (fun ev hev => hvc h hh ev (List.mem_of_mem_take hev))] at hlt
      omega
    · exact hnx k pce hex

/-! ### The lanes of a warp at one warp collective -/

/-- A thread without events is released. -/
theorem released_nil {h : Nat} (h0 : X.tr h = []) : Step.Released L X h :=
  Step.Released.of_get fun q hq => by simp [Execution.get, h0] at hq

/-- A thread whose last event never blocks is released. -/
theorem released_of_unblocking {h : Nat} {q : Event}
    (hq : X.get (h, (X.tr h).length - 1) = some q) (hu : Unblocking q.kind) :
    Step.Released L X h := by
  refine Step.Released.of_get fun q' hq' => ?_
  rw [hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨pc, k⟩ := q
  cases k with
  | tc kd => cases kd <;> simp_all [Unblocking, isTcColl, Kind.resume, TcKind.resume]
  | _ => simp_all [Unblocking, Kind.resume]

/-- A thread whose last event is a register request of the same ordinal and operands as the last
event of a released thread of its warp is released: the needs of both are the requests of the
warp (DEP-ORDER). -/
theorem released_of_reg {g h pc n ig : Nat} {inc : Bool}
    (hqg : X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n ig⟩)
    (hrel : Step.Released L X g)
    (hs : SetMaxNReg.SameRequest L X (g, (X.tr g).length - 1) (h, (X.tr h).length - 1)) :
    Step.Released L X h :=
  ⟨fun _ _ _ _ => SetMaxNReg.ready_of_sameRequest hqg hs (hrel.ready _ _ hqg rfl)⟩

/-- A thread whose last event is a warp-collective `tcgen05` event other than a paired Tensor
Memory operation, of the ordinal of the last event of a released lane of its warp, is released:
every lane of the warp has made its event of that ordinal (the needs of the released lane's
event, `tcNeeds`). -/
theorem released_of_tc {g h k : Nat} (hs : SameWarp L g h) (hrel : Step.Released L X g)
    (hKg : X.TcK (g, (X.tr g).length - 1) k) (hK : X.TcK (h, (X.tr h).length - 1) k)
    (hres : ∀ pc grp dst act, X.get (h, (X.tr h).length - 1) ≠
      some ⟨pc, .tc (.resource grp dst act)⟩) : Step.Released L X h := by
  obtain ⟨⟨qg, hqg, hcg⟩, hog⟩ := hKg
  obtain ⟨pcg, kdg, rfl⟩ := isTcColl_tc hcg
  have hrg := hrel.ready _ _ hqg
    (by cases kdg <;> simp_all [isTcColl, Kind.resume, TcKind.resume])
  have hd : ∀ h', h' < L.threads → SameWarp L h h' → ∃ j, X.TcK (h', j) k := by
    intro h' _ hw'
    have hw : SameWarp L h' g := sameWarp_symm (Step.sameWarp_trans hs hw')
    obtain ⟨x, -, j, rfl, hj⟩ := hrg _ (tcNeed_mem hqg hcg (mem_warpLanes_of_sameWarp hw))
    exact ⟨j, hog ▸ hj⟩
  obtain ⟨⟨q, hq, hc⟩, -⟩ := id hK
  obtain ⟨pc, kd, rfl⟩ := isTcColl_tc hc
  exact ⟨fun _ _ _ _ => tc_ready_of_done hs.1.2.1 hq
    (fun grp dst act he => hres pc grp dst act (by rw [hq, he])) hK hd⟩

/-! ### The templates of each static part -/

theorem tmplShape_shfl {m : Tmpl} {md : ShflMode} {b c : Nat}
    (h : tmplShape m = some (.shfl md b c)) : ∃ a k, m = .shfl md a b c k := by
  cases m <;> simp [tmplShape] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

theorem tmplShape_elect {m : Tmpl} {mask : Nat} (h : tmplShape m = some (.elect mask)) :
    ∃ k, m = .elect mask k := by
  cases m <;> simp [tmplShape] at h
  subst h
  exact ⟨_, rfl⟩

theorem tmplShape_warpBar {m : Tmpl} {mask : Nat} (h : tmplShape m = some (.warpBar mask)) :
    ∃ t, m = .warpBar mask t := by
  cases m <;> simp [tmplShape] at h
  subst h
  exact ⟨_, rfl⟩

theorem tmplShape_vote {m : Tmpl} {mask : Nat} (h : tmplShape m = some (.vote mask)) :
    ∃ a k, m = .vote mask a k := by
  cases m <;> simp [tmplShape] at h
  subst h
  exact ⟨_, _, rfl⟩

/-- The lanes of `g`'s warp reach, by local steps, templates of the static part `s` at `pc`. -/
abbrev LanesAt (K : Kernel) (A : List Assumption) (L : Launch) (X : Execution) (g pc : Nat)
    (s : CollShape) : Prop :=
  ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
    Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
    t1.pc = pc ∧ tmplShape m = some s

/-- **The warp performs one instance of the collective**: a counted extension. The assumptions
keep their constraints when the lanes' events, which read no memory, are appended (`hasm`). -/
theorem coll_batch (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {g pc : Nat}
    {s : CollShape} (hg : g < L.threads) (hfull : s.Full) (hl : LanesAt K A L X g pc s)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Step.Launched L X h)
    (hasm : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hrels : ∀ h, SameWarp L g h → Step.Released L X h) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hmem : ∀ h, electMember 4294967295 (laneOf L h) := fun h =>
    full_member (Nat.mod_lt _ (by decide))
  cases s with
  | shfl md b c =>
    have hex : ∀ h, ∃ a : Value, SameWarp L g h → ∃ t t1 k, Run K A L h {} (X.tr h)
        (some t) ∧ Relation.ReflTransGen (Tau K A L h) t t1 ∧
        out K A L h t1 = .ev (.shfl md a b c k) ∧ t1.pc = pc := by
      intro h
      obtain ⟨t, t1, m, -, -, -, -, hm⟩ := hl g ⟨⟨hg, hg, rfl⟩, rfl⟩
      obtain ⟨a0, -, -⟩ := tmplShape_shfl hm
      by_cases hs : SameWarp L g h
      · obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
        obtain ⟨a, k, rfl⟩ := tmplShape_shfl hm
        exact ⟨a, fun _ => ⟨t, t1, k, hr, hτ, hout, hpc⟩⟩
      · exact ⟨a0, fun h' => (hs h').elim⟩
    choose A hA using hex
    refine Step.shfl_counted_extension hX hb (pc := pc) (m := md) A (fun _ => b) (fun _ => c) hg
      hst hrels (fun h hs recv ok => ?_) (fun ev h => hasm _ ev h)
    obtain ⟨t, t1, k, hr, hτ, hout, hpc⟩ := hA h hs
    exact ⟨t, t1, _, hr, hτ, _, hout, recv, ok, by rw [hpc], rfl⟩
  | elect mask =>
    have hm : mask = 4294967295 := hfull
    subst hm
    obtain ⟨leader, hlm, hdet⟩ := Step.exists_leader (g := g) hX (hmem g)
    refine Step.elect_counted_extension hX (pc := pc) hg
      (fun lane hl => Step.warp_full hb hg hl.1) (fun h _ => hmem h) hlm hdet hst hrels
      (fun h hs inst => ?_) (fun _ => hasm _ _ fun _ => rfl)
    obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
    obtain ⟨k, rfl⟩ := tmplShape_elect hm
    exact ⟨t, t1, _, hr, hτ, _, hout, inst, leader, by rw [hpc], rfl⟩
  | warpBar mask =>
    have hm : mask = 4294967295 := hfull
    subst hm
    refine Step.warpBar_counted_extension hX (fun _ => pc) hg
      (fun lane hl => Step.warp_full hb hg hl.1) (fun h _ => hmem h) hst hrels
      (fun h hs inst => ?_) (fun _ => hasm _ _ fun _ => rfl)
    obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
    obtain ⟨u, rfl⟩ := tmplShape_warpBar hm
    exact ⟨t, t1, _, hr, hτ, _, hout, inst, by rw [hpc], rfl⟩
  | vote mask =>
    have hm : mask = 4294967295 := hfull
    subst hm
    have hex : ∀ h, ∃ a : Bool, SameWarp L g h → ∃ t t1 k, Run K A L h {} (X.tr h)
        (some t) ∧ Relation.ReflTransGen (Tau K A L h) t t1 ∧
        out K A L h t1 = .ev (.vote 4294967295 a k) ∧ t1.pc = pc := by
      intro h
      by_cases hs : SameWarp L g h
      · obtain ⟨t, t1, m, hr, hτ, hout, hpc, hm⟩ := hl h hs
        obtain ⟨a, k, rfl⟩ := tmplShape_vote hm
        exact ⟨a, fun _ => ⟨t, t1, k, hr, hτ, hout, hpc⟩⟩
      · exact ⟨false, fun h' => (hs h').elim⟩
    choose A hA using hex
    refine Step.vote_counted_extension hX hb (pc := pc) A hg (fun h _ => (hmem h).2) hst
      hrels (fun h hs ballot => ?_) (fun ev h => hasm _ ev h)
    obtain ⟨t, t1, k, hr, hτ, hout, hpc⟩ := hA h hs
    exact ⟨t, t1, _, hr, hτ, _, hout, ballot, by rw [hpc], rfl⟩

end

end PTX.Sched
