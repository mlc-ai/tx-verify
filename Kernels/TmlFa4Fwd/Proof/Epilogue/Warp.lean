-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Glue
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ledger
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Lemmas.Kernel.Source.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Coll
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Lemmas.Flow.WarpScan
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The lanes of the output warp are followed

Every lane of warp 13 is followed by the thread machine, and every state holds the reference
values (`good`): `Frame.followedOn` restricted to the lanes of warp 13 (`Q`), with the reference
invariant `Ref` and the order by the warp collectives up to an event (`μ`). At a startup state the
words the shuffles returned so far are the shared base and the warp index 13 (`StartAt`), at a
role state the role's values hold (`Fits`) and the ghost counts have their closed forms (`Led`),
and no lane of warp 13 is at a stub. A returned value comes from its source (plan G5): a load from
the launch words (`Reads.lean`, the read-only input), a shuffle from the source lane's operand at
the same instance (`start_recv` at the startup, `shfl_recv` in the role) and a ballot from the
predicates of all lanes at the same instance (`vote_bits`). The source lanes are followed up to the
instance because their earlier events have fewer collectives (`upTo_of_prev`); a lane that would be
ahead in one kind of collective and behind in the other contradicts the order of the common
sequence (`Position`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The lanes of warp 13. -/
abbrev Q (L : Launch) (g : Nat) : Prop := InWarp L 13 g

/-- **The reference invariant of a lane of warp 13**: at a startup state its words and counts,
at a role state the reference values and the ledger's closed forms; no stub. -/
def Ref (p : Params) (L : Launch) (g : Nat) :
    (Startup.D ⊕ (Σ i, (frag p L g i).D)) × (Cls → Nat) → Prop
  | (.inl s, n) => StartAt L 13 s n ∧ n .vote = 0 ∧ Led n (M p L g).init
  | (.inr ⟨.epilogue, d⟩, n) => Fits p L g d (n .shfl) (n .vote) ∧ 5 ≤ n .all ∧ Led n d
  | (.inr ⟨.mma, _⟩, _) | (.inr ⟨.correction, _⟩, _) | (.inr ⟨.loader _, _⟩, _)
  | (.inr ⟨.stub _, _⟩, _) | (.inr ⟨.softmax, _⟩, _) => False

/-- Lane `g`'s state before its `k`-th event is followed and holds the reference values. -/
abbrev Good (p : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  Frame.FollowedAt (thread p L) (Ref p L) X g k

/-- The value a shuffle site sends. -/
def opnd (L : Launch) (g : Nat) (d : D) : BitVec 64 :=
  match d.site with
  | .down _ => d.w
  | .up _ j => partialAt L g d j.val
  | .total _ | .pre _ => prefixD L g d
  | .tiles _ => d.tl
  | _ => 0

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The events before the fifth of a lane with good states are the startup's.** -/
theorem prologue_ev (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (hj : j < 5) (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L X g j) :
    isFullVote e = false ∧ e.kind ≠ .exit ∧ (Execution.isShfl e = true → j < 3) ∧
      e.pc < 2768 ∧ ∀ c, ¬ StartCls c → cls L g c e = false := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  have ha := count_all hσ (List.getElem?_eq_some_iff.mp he).1.le
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · obtain ⟨hE, -, hpc⟩ := start_fired hp hX he hσ
    obtain ⟨h1, h2, h3, h4, h5⟩ := start_kind hR.1 hE
    have := startAt_le hR.1
    exact ⟨h1, h2, fun h => by have := h3 h; omega, by omega,
      fun c hc => Bool.eq_false_iff.mpr fun h => hc (h5 c h)⟩
  · exact absurd hR.2.1 (by omega)
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- **From the fifth event on, a good state of a lane is a role state**, and its event has the
site's shape. -/
theorem good_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {j : Nat}
    {e : Event} (hj5 : 5 ≤ j) (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : Good p L X g j) :
    ∃ d n, Frame.stateAt (thread p L) X g j = some (some (inj p L g d n)) ∧
      Fits p L g d (n .shfl) (n .vote) ∧ Ev p L g d e := by
  obtain ⟨⟨σ, n⟩, hσ, hR⟩ := good_state hp hX he hub hG
  have ha := count_all hσ (List.getElem?_eq_some_iff.mp he).1.le
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact absurd (startAt_le hR.1).1 (by omega)
  · exact ⟨d, n, hσ, hR.1, (fired hp hX he hσ).1⟩
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- A shuffle site's event sends the site's value. -/
theorem ev_opnd {d : D} {pc : Nat} {mode : ShflMode} {a r : Value} {b c : Nat} {ok : Bool}
    (hE : Ev p L g d ⟨pc, .shfl mode a b c r ok⟩) : a = .bits 32 (opnd L g d) := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases s <;> simp only [Ev] at hE <;>
    first
    | (obtain ⟨_, _, h⟩ := hE; simp only [Kind.shfl.injEq] at h; exact h.2.1)
    | simp_all [isStore]

/-- The kind of event a site fires, as far as the collectives and the return go. -/
theorem ev_class {d : D} {e : Event} (hE : Ev p L g d e) :
    (Execution.isShfl e = true → d.site.shfl = true) ∧
      (isFullVote e = true → ∃ l, d.site = .vote l) ∧
      (e.kind = .exit → ∃ l, d.site = .exit l) := by
  obtain ⟨h1, h2⟩ := ev_counts hE
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [sh, h, ↓reduceIte] at h1; split at h1 <;> simp_all
  · simp only [vt, h, ↓reduceIte] at h2; revert h2; cases d.site <;> simp [Site.ballot]
  · obtain ⟨pc, kind⟩ := e
    simp only at h
    subst h
    cases hs : d.site <;> simp_all [Ev, isStore]

/-- The induction hypothesis: the lanes of warp 13 hold the reference values before their
events with at most `n` collectives before them. -/
abbrev GoodUpTo (p : Params) (L : Launch) (X : Execution) (n : Nat) : Prop :=
  Proof.GoodUpTo (Ref p L) X 13 n

/-- **No lane of the warp is at a ballot past at most the shuffles and exactly the ballots of a
shuffle state.** -/
theorem no_vote (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {d : D}
    {ns nv : Nat} (hF : Fits p L g d ns nv) (hs : d.site.shfl = true) (h j : Nat) (e : Event)
    (_ : InWarp L 13 h) (hc : h / L.block = g / L.block) (he0 : X.get (h, j) = some e)
    (hv0 : isFullVote e = true) (hG : Good p L X h j)
    (hs0 : Frame.cnt X Execution.isShfl h j ≤ ns) (hc0 : Frame.cnt X isFullVote h j = nv) :
    False := by
  simp only [Frame.cnt] at hs0 hc0
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl; simp [isFullVote, voteClass] at hv0
  have hj05 : 5 ≤ j := by
    by_contra hlt
    have := (prologue_ev hp hX (by omega) he0 hub hG).1
    rw [hv0] at this; cases this
  obtain ⟨d0, n0, hσ0, hF0, hE0⟩ := good_at hp hX hj05 he0 hub hG
  obtain ⟨l, hl⟩ := (ev_class hE0).2.1 hv0
  obtain ⟨hs0', hv0'⟩ := counts hσ0
  have := shfl_lt_vote hF hF0 hc.symm hs hl (by omega)
  omega

/-- **No lane of the warp is at a shuffle past at most the ballots and exactly the shuffles of a
ballot state.** -/
theorem no_shfl (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {d : D}
    {ns nv : Nat} {l : Bool} (hF : Fits p L g d ns nv) (hs : d.site = .vote l) (h j : Nat)
    (e : Event) (_ : InWarp L 13 h) (hc : h / L.block = g / L.block)
    (he1 : X.get (h, j) = some e) (hs1 : Execution.isShfl e = true) (hG : Good p L X h j)
    (hv1 : Frame.cnt X isFullVote h j ≤ nv) (hc1 : Frame.cnt X Execution.isShfl h j = ns) :
    False := by
  simp only [Frame.cnt] at hv1 hc1
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by rintro pc f rfl; simp [Execution.isShfl] at hs1
  have hj15 : 5 ≤ j := by
    by_contra hlt
    have := (prologue_ev hp hX (by omega) he1 hub hG).2.2.1 hs1
    have := countP_take_le_length Execution.isShfl (X.tr h) j
    have := fits_three hF
    omega
  obtain ⟨d1, n1, hσ1, hF1, hE1⟩ := good_at hp hX hj15 he1 hub hG
  obtain ⟨hs1', hv1'⟩ := counts hσ1
  have := shfl_lt_vote hF1 hF hc ((ev_class hE1).1 hs1) hs (by omega)
  omega

/-- **No lane of the warp has returned past at most the counts of a collective state.** -/
theorem no_exit (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {d : D}
    {ns nv : Nat} (hF : Fits p L g d ns nv) (hs : d.site.shfl = true ∨ ∃ l, d.site = .vote l)
    (h j pc : Nat) (_ : InWarp L 13 h) (hc : h / L.block = g / L.block)
    (hx : X.get (h, j) = some ⟨pc, .exit⟩) (hG : Good p L X h j)
    (hsx : Frame.cnt X Execution.isShfl h j ≤ ns) (hvx : Frame.cnt X isFullVote h j ≤ nv) :
    False := by
  simp only [Frame.cnt] at hsx hvx
  have hx5 : 5 ≤ j := by
    by_contra hlt
    exact (prologue_ev hp hX (by omega) hx (by rintro _ _ ⟨⟩) hG).2.1 rfl
  obtain ⟨dx, nx, hσx, hFx, hEx⟩ := good_at hp hX hx5 hx (by rintro _ _ ⟨⟩) hG
  obtain ⟨l, hl⟩ := (ev_class hEx).2.2 rfl
  obtain ⟨hsx', hvx'⟩ := counts hσx
  have hFx' := hFx
  simp only [Fits, hl] at hFx'
  rcases hs with hs | ⟨l', hs⟩
  · have := shfl_lt_exit hF hc.symm hs hFx'
    omega
  · exact vote_exit hF hc.symm hs hFx' (by omega)

/-- **What a lane's shuffle receives**: the value its source lane sends at the same site. -/
theorem shfl_recv (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {pc : Nat}
    {mode : ShflMode} {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n)))
    (hF : Fits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L X (n .shfl + n .vote)) :
    ∃ d' nv', Fits p L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) d' (n .shfl) nv' ∧
      d'.site = d.site ∧
      recv = .bits 32 (opnd L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) d') := by
  obtain ⟨hcs, -⟩ := counts hσ
  have hsite := (ev_class (fired hp hX he hσ).1).1 rfl
  have hsC := (lane_facts hp hg hw
    (Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c)).2.2.1
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs, -⟩ := shfl_src hp hX hg hw he hcs IH
    (no_vote hp hX hF hsite) (no_exit hp hX hF (.inl hsite))
  simp only [Frame.cnt] at hjs
  have h3 := fits_three hF
  have hj5 : 5 ≤ j := by
    by_contra hlt
    have := (prologue_ev hp hX (by omega) hj (by rintro _ _ ⟨⟩) hG).2.2.1 rfl
    have := countP_take_le_length Execution.isShfl
      (X.tr (g - laneOf L g + (shflSource mode (laneOf L g) b c).1)) j
    omega
  obtain ⟨d', n', hσ', hF', hE'⟩ := good_at hp hX hj5 hj (by rintro _ _ ⟨⟩) hG
  obtain ⟨hs', -⟩ := counts hσ'
  have hsite' := (ev_class hE').1 rfl
  have hns : n .shfl = n' .shfl := by omega
  rw [← hns] at hF'
  exact ⟨d', _, hF', shfl_same hF hF' hsC.symm hsite hsite' rfl, ev_opnd hE'⟩

/-- Two ballot states of lanes of one CTA with one ballot count are at one position. -/
theorem vote_same {h : Nat} {d d' : D} {ns nv ns' nv' : Nat} {l l' : Bool}
    (hF : Fits p L g d ns nv) (hF' : Fits p L h d' ns' nv')
    (hc : g / L.block = h / L.block) (hs : d.site = .vote l) (hs' : d'.site = .vote l')
    (hv : nv = nv') : d'.site = d.site ∧ ns' = ns := by
  obtain ⟨n0, hP, R, hE, -, hns⟩ := vote_pos hF hs
  obtain ⟨n0', hP', R', hE', -, hns'⟩ := vote_pos hF' hs'
  have h0 := passStart_v0 hP
  have h0' := passStart_v0 hP'
  obtain rfl : l = l' := by
    cases l <;> cases l' <;> simp_all
  obtain ⟨rfl, -⟩ := PassStart.same hc hP (hv ▸ hP')
  rw [hc] at hE
  obtain rfl := hE.unique hE'
  exact ⟨by rw [hs, hs'], by omega⟩

/-- **A ballot's bits are the predicates of all lanes at the same ballot.** -/
theorem vote_bits (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {pc mask : Nat}
    {a : Bool} {bv : BitVec 32}
    (he : X.get (g, k) = some ⟨pc, .vote mask a bv⟩)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n)))
    (hF : Fits p L g d (n .shfl) (n .vote)) (IH : GoodUpTo p L X (n .shfl + n .vote)) :
    ∀ i < 32, ∃ di nvi, Fits p L (g - laneOf L g + i) di (n .shfl) nvi ∧ di.site = d.site ∧
      bv.getLsbD i = votePred p L (g - laneOf L g + i) di := by
  obtain ⟨-, hcv⟩ := counts hσ
  have hev := (fired hp hX he hσ).1
  have hmask : mask = 2 ^ 32 - 1 ∧ ∃ l, d.site = .vote l := by
    obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
    cases s <;> simp only [Ev] at hev <;> simp_all [isStore]
  obtain ⟨rfl, l, hl⟩ := hmask
  intro i hi
  have := vote_src (P := fun h b => ∃ di nvi, Fits p L h di (n .shfl) nvi ∧ di.site = d.site ∧
      b = votePred p L h di) hp hX hg hw he hcv IH
    (no_shfl hp hX hF hl) (no_exit hp hX hF (.inr ⟨l, hl⟩))
    (fun h j ej _ hc hej hfv hG hsj hcnt => by
      have hubj : ∀ pc f, ej ≠ ⟨pc, .ub f⟩ := by
        rintro pc f rfl; simp [isFullVote, voteClass] at hfv
      have hj5 : 5 ≤ j := by
        by_contra hlt
        have := (prologue_ev hp hX (by omega) hej hubj hG).1
        rw [hfv] at this; cases this
      obtain ⟨di, ni, hσi, hFi, hEi⟩ := good_at hp hX hj5 hej hubj hG
      obtain ⟨li, hli⟩ := (ev_class hEi).2.1 hfv
      obtain ⟨-, hvi⟩ := counts hσi
      simp only [Frame.cnt] at hcnt
      obtain ⟨hsite, hns⟩ := vote_same hF hFi hc.symm hl hli (by omega)
      rw [hns] at hFi
      obtain ⟨pcj, kj⟩ := ej
      obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := di
      simp only at hli
      subst hli
      simp only [Ev] at hEi
      obtain ⟨bj, hkj⟩ := hEi
      subst hkj
      exact ⟨pcj, _, bj, rfl, _, _, hFi, hsite, rfl⟩) i hi
  exact this

/-- The partial sum an `up` site sends is the reference partial sum of its round. -/
theorem partialAt_eq {late : Bool} {r : Nat} {j : Fin 5} {d : D}
    (h : RoundVals p late (laneOf L g) r j.val d) :
    partialAt L g d j.val = psum p late r j.val (laneOf L g) := by
  obtain ⟨htl, hu⟩ := h
  fin_cases j
  · simp [partialAt, psum, htl]
  · have h0 := hu 0 (by decide)
    simp only [uAt] at h0
    simp [partialAt, psum, upd, htl, h0]
  · have h0 := hu 0 (by decide)
    have h1 := hu 1 (by decide)
    simp only [uAt] at h0 h1
    simp [partialAt, psum, upd, htl, h0, h1]
  · have h0 := hu 0 (by decide)
    have h1 := hu 1 (by decide)
    have h2 := hu 2 (by decide)
    simp only [uAt] at h0 h1 h2
    simp [partialAt, psum, upd, htl, h0, h1, h2]
  · have h0 := hu 0 (by decide)
    have h1 := hu 1 (by decide)
    have h2 := hu 2 (by decide)
    have h3 := hu 3 (by decide)
    simp only [uAt] at h0 h1 h2 h3
    simp [partialAt, psum, upd, htl, h0, h1, h2, h3]

theorem shflSource_idx31 (lane b : Nat) : (shflSource .idx lane b 31).1 = b % 32 := by
  have h := shflSource_idx lane (offset := b % 32) (Nat.mod_lt _ (by decide))
  simp only [shflSource] at h ⊢
  simp only [Nat.mod_mod] at h ⊢
  rw [h]

theorem truncBits_addi (x : BitVec 64) (n : Int) : truncBits 32 (addi x n) = addi x n := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, truncBits, BitVec.toNat_ofNat]; omega

theorem truncBits_popc (x : BitVec 64) : truncBits 32 (popc x) = popc x := by
  obtain ⟨n, hn, h⟩ := popc_W x
  rw [h]; exact r32_W (by omega)

set_option maxHeartbeats 4000000 in
/-- **What a scan shuffle must return, from its source lane**: the value the source lane sends
from the same site with the same shuffle count. Pure: the source fact comes from the execution
(`shfl_recv`, or the MMA warp's). -/
theorem expect_shfl_of_src {w : Nat} (hp : Pre p L m) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) {d : D} {ns : Nat} {pc : Nat} {mode : ShflMode}
    {a recv : Value} {b c : Nat} {ok : Bool} (hev : Ev p L g d ⟨pc, .shfl mode a b c recv ok⟩)
    (hsrc : ∃ d' nv', Fits p L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) d' ns nv' ∧
      d'.site = d.site ∧
      recv = .bits 32 (opnd L (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) d')) :
    Expect p L g d ns ⟨pc, .shfl mode a b c recv ok⟩ := by
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨d', nv', hF', hsite, hrecv⟩ := hsrc
  have hsl := Step.shflSource_lt mode hl b c
  obtain ⟨-, -, hsC, hsL, -⟩ := lane_facts hp hg hw hsl
  cases hs : d.site
  all_goals first
    | (simp only [Expect, hs]; done)
    | (have hk := hev
       simp only [Ev, hs] at hk
       obtain ⟨_, _, hk⟩ := hk
       cases hk
       simp only [Expect, hs]
       rw [hrecv]
       simp only [opnd, hsite, hs]
       simp only [Fits, hsite, hs] at hF')
  case down k' =>
    intro r n0 v0 hP hR hns
    obtain ⟨r', n1, v1, hP', hR', hns1, -, -, hw'⟩ := hF'
    obtain ⟨rfl, -⟩ := PassStart.same hsC.symm hP hP'
    obtain rfl : r = r' := by omega
    rw [hw', hsL, shflSource_down_one]
    simp only [dnv]
    split <;> split <;> first | rfl | omega
  case up k' j =>
    intro r n0 v0 hP hR hns
    obtain ⟨r', n1, v1, hP', hR', hns1, -, -, hRV⟩ := hF'
    obtain ⟨rfl, -⟩ := PassStart.same hsC.symm hP hP'
    obtain rfl : r = r' := by omega
    rw [partialAt_eq (by rw [hsL] at hRV ⊢; exact hRV), hsL]
    have hj : 2 ^ j.val < 32 := by have := j.isLt; interval_cases (j.val) <;> decide
    rw [shflSource_up hj]
    simp only [upSrc]
    split <;> rfl
  case total k' =>
    intro r n0 v0 hP hR hns
    obtain ⟨r', n1, v1, hP', hR', hns1, -, -, hRV⟩ := hF'
    obtain ⟨rfl, -⟩ := PassStart.same hsC.symm hP hP'
    obtain rfl : r = r' := by omega
    rw [prefixD_eq hRV, hsL, shflSource_idx31]
    rfl
  case pre l =>
    intro R n0 v0 hP hE hns
    obtain ⟨R', n1, v1, hP', hEV', -, -, hRV, -⟩ := hF'
    rw [hsC] at hEV'
    obtain rfl := hE.unique hEV'.1
    rw [prefixD_eq hRV, hsL, shflSource_idx31, truncBits_addi]
  case tiles l =>
    intro R n0 v0 hP hE
    obtain ⟨R', n1, v1, hP', hEV', -, -, hRV, -⟩ := hF'
    rw [hsC] at hEV'
    obtain rfl := hE.unique hEV'.1
    rw [hRV.1, hsL, shflSource_idx31, truncBits_popc]

/-- **What a ballot must return, from the lanes of its warp**: the predicates the lanes hold at
the same site with the same shuffle count. -/
theorem expect_vote_of_bits {w : Nat} (hp : Pre p L m) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = w) {d : D} {ns : Nat} {pc mask : Nat} {a : Bool}
    {bv : BitVec 32} {l : Bool} (hs : d.site = .vote l)
    (hbits : ∀ i < 32, ∃ di nvi, Fits p L (g - laneOf L g + i) di ns nvi ∧ di.site = d.site ∧
      bv.getLsbD i = votePred p L (g - laneOf L g + i) di) :
    Expect p L g d ns ⟨pc, .vote mask a bv⟩ := by
  simp only [Expect, hs]
  intro R n0 v0 hP hE hns i hi
  obtain ⟨di, nvi, hFi, hsi, hbit⟩ := hbits i hi
  obtain ⟨hiT, hiW, hiC, hiL, -⟩ := lane_facts hp hg hw hi
  rw [hbit]
  simp only [Fits, hsi, hs] at hFi
  obtain ⟨R', n1, v1, hP', hEV', -, -, hRV⟩ := hFi
  rw [hiC] at hEV'
  obtain rfl := hE.unique hEV'.1
  rw [votePred, prefixD_eq hRV, hEV'.2.2.2.1, hEV'.2.1, hiL]
  simp [predv, ctaW, hiC]

/-- A collective site fires a collective. -/
theorem ev_coll {d : D} {e : Event} (hev : Ev p L g d e) :
    (d.site.shfl = true ∨ ∃ l, d.site = .vote l) → isColl e = true := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  rintro (hs | ⟨l, hs⟩) <;> simp only [isColl, Bool.or_eq_true]
  · left; simp only [sh, hs, ↓reduceIte] at h1; split at h1 <;> simp_all
  · right; simp only [vt, hs, Site.ballot, ↓reduceIte] at h2; split at h2 <;> simp_all

/-- **What every event of a lane that holds the reference values returns is what the reference
says**, from the lanes of its warp before it. -/
theorem expect (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 13) {k : Nat} {d : D} {e : Event}
    (he : X.get (g, k) = some e)
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n)))
    (hF : Fits p L g d (n .shfl) (n .vote))
    (IH : isColl e = true → GoodUpTo p L X (n .shfl + n .vote)) :
    Expect p L g d (n .shfl) e := by
  have hev := (fired hp hX he hσ).1
  have IH' := fun h => IH (ev_coll hev h)
  obtain ⟨pc, kind⟩ := e
  cases hs : d.site with
  | word k' => exact expect_word hp hReads he hs hF hev
  | q0 => exact expect_q hp hReads he (.inl hs) hF hev
  | q1 => exact expect_q hp hReads he (.inr hs) hF hev
  | down _ | up _ _ | total _ | pre _ | tiles _ =>
    have hE := hev
    simp only [Ev, hs] at hE
    obtain ⟨recv, ok, rfl⟩ := hE
    exact expect_shfl_of_src hp hg hw hev
      (shfl_recv hp hX hg hw he hσ hF (IH' (.inl (by simp [hs, Site.shfl]))))
  | vote l =>
    have hE := hev
    simp only [Ev, hs] at hE
    obtain ⟨b, hb⟩ := hE
    subst hb
    exact expect_vote_of_bits hp hg hw hs (vote_bits hp hX hg hw he hσ hF (IH' (.inr ⟨l, hs⟩)))
  | _ => simp only [Expect, hs]

/-- The first state of every thread holds `Ref`. -/
theorem ref_init : Ref p L g (thread p L g).init := by
  show Ref p L g (.inl ⟨.sh 0, 0, 0, 0⟩, fun _ => 0)
  refine ⟨⟨rfl, rfl, by simp, by simp⟩, rfl, rfl, rfl, rfl, rfl, fun st => ?_⟩
  fin_cases st <;> exact ⟨rfl, rfl⟩

/-- The output warp's ledger is zero through the startup. -/
theorem led_start {n : Cls → Nat} {e : Event}
    (hn : ∀ c, ¬ StartCls c → Code.bump (cls L g) n e c = n c) (hL : Led n (M p L g).init) :
    Led (Code.bump (cls L g) n e) (M p L g).init := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  exact ⟨(hn _ (by simp [StartCls])).trans h1, (hn _ (by simp [StartCls])).trans h2,
    (hn _ (by simp [StartCls])).trans h3, (hn _ (by simp [StartCls])).trans h4,
    fun st => ⟨(hn _ (by simp [StartCls])).trans (h5 st).1,
      (hn _ (by simp [StartCls])).trans (h5 st).2⟩⟩

/-- **The startup steps a lane of warp 13 well**: the shuffles return the reference words, and
after the barrier the dispatch enters the output warp's first state. -/
theorem start_step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {k : Nat} {s : Startup.D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hR : Ref p L g (.inl s, n))
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → Q L j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L) X j) :
    Frame.StepGood (thread p L) (Ref p L) g (.inl s, n) e :=
  start_step_of (Z := fun n => Led n (M p L g).init) hp hX hg hw (by decide) (by decide)
    (fun _ => ref_init) (fun _ _ => rfl) (fun _ _ _ h => ⟨h.1, h.2.1⟩)
    (fun _ _ _ r d n _ _ h => by
      rcases r with _ | _ | _ | _ | r | _
      on_goal 6 => exact h.elim
      · have := fits_three h.1; omega
      · exact h.elim
      · exact h.elim
      · exact h.elim
      · exact h.elim)
    (fun _ _ hn hL => led_start hn hL)
    (fun s n e hb hS hv hL hE hn => by
      obtain ⟨site, x1, x2, x3⟩ := s
      simp only at hb
      subst hb
      simp only [StartAt] at hS
      simp only [Startup.Ev] at hE
      obtain ⟨h3, h4, rfl, rfl⟩ := hS
      have e2 : Epilogue.scmpi .ne .b (Epilogue.andi (13#64) (-2)) 14 = true := by decide
      have e3 : Epilogue.scmpi .eq .b (13#64) 13 = true := by decide
      simp only [Code.enter, exit, Startup.enterOf, e2, e3, ↓reduceIte, Gate, roleOf,
        beq_self_eq_true, Bool.and_self]
      refine ⟨⟨?_, (hn _ (by simp [StartCls])).trans hv⟩, ?_, led_start hn hL⟩
      · obtain ⟨pc, kind⟩ := e
        simp only at hE
        subst hE
        simp [Code.bump, cls, Execution.isShfl, h3]
      · simp [Code.bump, cls]; omega)
    he hσ hR hprev

set_option maxHeartbeats 1000000 in
/-- **Every event of a lane of warp 13 at a state that holds `Ref` makes a good step** once no
lane of warp 13 is bad at an earlier collective position. -/
theorem step (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (g k : Nat) (σ : (thread p L g).D) (e : Event)
    (hQ : Q L g) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hR : Ref p L g σ)
    (hprev : ∀ j, Frame.lexOrder (μ X) j (g, k) → Q L j.1 →
      ¬ Frame.Bad (thread p L) (Ref p L) X j) :
    Frame.StepGood (thread p L) (Ref p L) g σ e := by
  obtain ⟨hg, hw⟩ := hQ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_step hp hX hg hw he hσ hR hprev
  · obtain ⟨hF, h5, hL⟩ := hR
    obtain ⟨hcs, hcv⟩ := counts hσ
    have hev := (fired hp hX he hσ).1
    have hE : Expect p L g d (n .shfl) e :=
      expect hp hX hReads hg hw he hσ hF fun hce => by
        have := upTo_of_prev (fun _ => ref_init) he hce hprev
        rwa [countColl ((X.tr g).take k), hcs, hcv] at this
    have hnext : (thread p L g).next (inj p L g d n) e =
        ((M p L g).next d e).map (Option.map fun d' => inj p L g d' (Code.bump (cls L g) n e)) := by
      show (((M p L g).next d e).map (Option.map fun d' => (Sum.inr ⟨Role.epilogue, d'⟩ :
        (glued p L g).D))).map (Option.map fun d' => (d', Code.bump (cls L g) n e)) = _
      rcases (M p L g).next d e with _ | _ | d' <;> rfl
    have hne := next_ne (ent := ent p L) hF hE
    show (thread p L g).next (inj p L g d n) e ≠ some none ∧ _
    rw [hnext]
    rcases hn : (M p L g).next d e with _ | _ | d₁
    · exact ⟨by simp, fun _ h => by simp at h⟩
    · exact absurd hn hne
    · refine ⟨by simp, fun σ' h => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hF' := fits_next (ent := ent p L) hF hE hev hn
      refine ⟨?_, by simp [Code.bump, cls]; omega, led_step hL hev hn⟩
      exact hF'
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim
  · exact hR.elim

/-- **Every lane of warp 13 is followed, and its states hold the reference values**: by the
order induction on the collectives up to an event, restricted to the lanes of warp 13. -/
theorem good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hReads : Epilogue.CuQReadsFromLaunch p X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 13) (k : Nat) : Good p L X g k :=
  Frame.followedOn (C := thread p L) (J := Ref p L) (Q := Q L) (Frame.inductive_lex (μ X))
    (fun _ _ => ref_init) (step hp hX hReads) ⟨hg, hw⟩ k

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
