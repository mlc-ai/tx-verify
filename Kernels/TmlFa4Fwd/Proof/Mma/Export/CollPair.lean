-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollSite
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollOfCls
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Lag
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collectives of two lanes of the MMA warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (CollTag tagOf MCls mma_cls mma_exit_cls)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

private theorem mmaShape_eq {d d' : Mma.D} {n n' : Cls → Nat} {u u' : Unit}
    (h : d.site = d'.site)
    (hb : ∀ l, d.site = .pre l ∨ d.site = .tiles l → d.v.sc.bal = d'.v.sc.bal) {h' : Nat} :
    mmaShape p L g (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n) =
      mmaShape p L h' (.inr ⟨.mma, .inr ⟨u', d'⟩⟩, n') := by
  obtain ⟨site, v⟩ := d
  obtain ⟨site', v'⟩ := d'
  simp only at h hb
  subst h
  cases site with
  | pre l =>
    have := hb l (.inl rfl)
    simp only [mmaShape, this]
  | tiles l =>
    have := hb l (.inr rfl)
    simp only [mmaShape, this]
  | _ => rfl

private theorem tag_start {x : Nat} {σ : (thread p L x).D} {j : Fin 3}
    (h : tagOf p L x σ = some (.start j)) : ∃ x1 x2 x3 n, σ = (.inl ⟨.sh j, x1, x2, x3⟩, n) := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp [tagOf] at h
    subst h
    exact ⟨_, _, _, _, rfl⟩
  all_goals first
    | (simp [tagOf] at h; done)
    | (rcases d with s | ⟨u, d⟩
       · simp [tagOf] at h
       · simp only [tagOf] at h
         split at h <;> simp at h)

private theorem tag_site {x : Nat} {σ : (thread p L x).D} {s : Mma.Site}
    (h : tagOf p L x σ = some (.site s)) :
    ∃ d n, σ = (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n) ∧ d.site = s ∧ s.wcoll = true := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s' | ⟨_ | _ | _ | _ | r | _, d⟩
  · obtain ⟨site, x1, x2, x3⟩ := s'
    cases site <;> simp [tagOf] at h
  all_goals first
    | (simp [tagOf] at h; done)
    | (rcases d with s' | ⟨u, d⟩
       · simp [tagOf] at h
       · simp only [tagOf] at h
         split at h <;> simp at h
         rename_i hw
         subst h
         exact ⟨d, n, rfl, rfl, hw⟩)

/-- A blocking event of an MMA role state leads to a state at no collective. -/
private theorem block_next {d : Mma.D} {e : Event} {ent : Nat → Value}
    (hev : Mma.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f) (hb : ¬ Sched.Unblocking e.kind) :
    ∃ d', (Mma.code p L g ent).next d e = some (some d') ∧ d'.site.wcoll = false := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  have hk := mma_ev_kind hev hub
  cases s <;> simp only [Mma.Ev] at hev
  case bar1 => exact ⟨_, rfl, rfl⟩
  case bar2 l => exact ⟨_, rfl, rfl⟩
  case relinq l => exact ⟨_, rfl, rfl⟩
  case dealloc l => exact ⟨_, rfl, rfl⟩
  all_goals exfalso; apply hb
  case qk | pv =>
    rcases hev with ⟨_, _, _, _, h⟩ | ⟨f, h⟩
    · subst h; rfl
    · exact absurd h (hub f)
  case cm =>
    rcases hev with ⟨_, h, -⟩ | ⟨f, h⟩
    · subst h; rfl
    · exact absurd h (hub f)
  all_goals cases hk <;> first
    | exact trivial
    | (exfalso; simp [Epilogue.Ev, Mma.Site.toE] at hev)

/-- A state at the choice's shuffles. -/
private theorem mma_choice (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) {x k : Nat} {d : Mma.D} {n : Cls → Nat} {l : Bool} (hx : x < L.threads)
    (hwx : Prologue.warpIndex L x = 12)
    (hσ : Frame.stateAt (thread p L) X x k = some (some (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n)))
    (hl : d.site = .pre l ∨ d.site = .tiles l) :
    ∃ ns nv, Epilogue.Fits p L x (Mma.toE d) ns nv ∧
      ((Mma.toE d).site = .pre l ∨ (Mma.toE d).site = .tiles l) := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(x, j), pc, _, hf⟩
  obtain ⟨-, hF⟩ := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hx hwx k).2 _ hσ hub0
  have he : d.site.early = false := by rcases hl with h | h <;> rw [h] <;> rfl
  refine ⟨_, _, (Mma.mfits_main he hF).2.1, ?_⟩
  rcases hl with h | h
  · left; show d.site.epi = _; rw [h]; rfl
  · right; show d.site.epi = _; rw [h]; rfl

/-- The lanes of the MMA warp of CTA `c`. -/
def MmaLane (L : Launch) (c x : Nat) : Prop :=
  x < L.threads ∧ Prologue.warpIndex L x = 12 ∧ x / L.block = c

/-- **The classification of the MMA warp's states** by their collectives. -/
def mmaCls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (c : Nat) :
    CollCls p L X (MmaLane L c) (mmaShape p L) CollTag where
  tag := tagOf p L
  role _ := False
  cls x := MCls p L x
  at_ := fun {_ _ σ} hA hσ => (mma_collAt hp hX hA.1 hA.2.1 hσ).trans
    (by rw [Mma.tagOf_isSome σ])
  pos := fun {_ _ σ} hA hP => (Mma.tagOf_isSome σ).trans
    (mma_isP hp hX (launchFollow hp hX) hub hA.1 hA.2.1 hP)
  ok := fun hA hσ => by
    rw [mma_cnt_eq hp hX (launchFollow hp hX) hub hA.1 hA.2.1 hσ]
    exact mma_cls hp hX hub hA.1 hA.2.1 hσ
  order := fun hA hA' h1 h2 hle => h1.order hp hA'.1 (hA'.2.2.trans hA.2.2.symm) h2 hle
  static := by
    intro x y k k' σ σ' a hA hA' hσ hσ' hx hx'
    cases a with
    | start j =>
      obtain ⟨x1, x2, x3, n, rfl⟩ := tag_start hx
      obtain ⟨y1, y2, y3, n', rfl⟩ := tag_start hx'
      exact ⟨rfl, rfl⟩
    | site s =>
      obtain ⟨d, n, rfl, hd, hsw⟩ := tag_site hx
      obtain ⟨d', n', rfl, hd', -⟩ := tag_site hx'
      have hsite : d.site = d'.site := hd.trans hd'.symm
      refine ⟨show d.site.pc = d'.site.pc by rw [hsite], mmaShape_eq hsite fun l hl => ?_⟩
      obtain ⟨_, _, hF, h1⟩ := mma_choice hp hX hub hA.1 hA.2.1 hσ hl
      obtain ⟨_, _, hF', h2⟩ := mma_choice hp hX hub hA'.1 hA'.2.1 hσ' (by rw [← hsite]; exact hl)
      exact Epilogue.bal_same (d := Mma.toE d) (d' := Mma.toE d')
        (hA.2.2.trans hA'.2.2.symm) hF hF' h1 (by show d'.site.epi = d.site.epi; rw [hsite])
  exit := by
    intro x y N t a k pc σ' hA hA' c1 hσ' he
    rw [mma_cnt_eq hp hX (launchFollow hp hX) hub hA'.1 hA'.2.1 hσ']
    refine c1.lt_exit (hA'.2.2.trans hA.2.2.symm) ?_
    rcases Mma.open_ev hp hX (launchFollow hp hX) hA'.2.1 he (fun f h => by cases h) with
      ⟨s, n, hσ1, -, -, hi', hev⟩ | ⟨s, n, hσ1, -, -, hev⟩ | ⟨d, n, hσ1, -, -, -, hev⟩
    · exact (start_not_exit hi'.2 hev).elim
    · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · have h1 := (show Frame.stateAt (thread p L) X y k = _ from hσ').symm.trans hσ1
      obtain rfl := Option.some.inj (Option.some.inj h1)
      obtain ⟨l, hl⟩ := mma_exit_site hev
      exact mma_exit_cls hp hX hub hA'.1 hA'.2.1 hσ' hl
  entry := fun _ _ _ hr => hr.elim
  last := by
    intro h i σ e hA he hσ hb
    have hwh := hA.2.1
    suffices hs : (thread p L h).next σ e ≠ none ∧
        ∀ σ', (thread p L h).next σ e = some (some σ') → mmaAt p L h σ' = false from
      ⟨hs.1, fun σ' hσ' => .inl (by
        have := hs.2 σ' hσ'
        rw [← Mma.tagOf_isSome] at this
        simpa using this)⟩
    have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(h, i), e.pc, f, by
      rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
    have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hA.1 hwh i).2 _ hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
    · obtain ⟨h1, h2⟩ := start_last hp hX hwh (by decide) (by decide) he hσ hR.1 hb
      refine ⟨h1, fun σ' hσ' => ?_⟩
      obtain ⟨σ', n'⟩ := σ'
      rcases h2 _ hσ' with ⟨s', hs', hj⟩ | ⟨i', hi'⟩
      · simp only at hs'
        subst hs'
        simp only [mmaAt]
      · simp only at hi'
        subst hi'
        cases i' <;> rfl
    · rcases d with s | ⟨u, d⟩
      · cases s with
        | set => exact ⟨fun hc => (by cases hc), fun σ' h => by cases h; rfl⟩
        | wr => exact ⟨fun hc => (by cases hc), fun σ' h => by cases h; rfl⟩
        | alloc =>
          have hnx : (thread p L h).next (.inr ⟨.mma, .inl .alloc⟩, n) e =
              some (some (.inr ⟨.mma, Code.enter (Mma.S p L h (Mma.ent p L))
                (fun _ => Mma.code p L h (Mma.ent p L)) Mma.Start.exit
                (if laneOf L h = 0 then .wr else .enter)⟩, Code.bump (cls L h) n e)) := rfl
          refine ⟨fun hc => ?_, fun σ' hσ' => ?_⟩
          · have h0 := hnx.symm.trans hc
            cases h0
          · obtain rfl := Option.some.inj (Option.some.inj (hnx.symm.trans hσ'))
            split_ifs <;> rfl
        | enter =>
          exfalso
          rcases Mma.open_ev hp hX (launchFollow hp hX) hwh he hne with ⟨s', n', hσ', -⟩ |
            ⟨s', n', hσ', -, hinv, -⟩ | ⟨d', n', hσ', -⟩
          · rw [hσ] at hσ'; cases hσ'
          · rw [hσ] at hσ'
            cases hσ'
            have h2 : Mma.Start.exit .enter = none := hinv.2
            cases h2
          · rw [hσ] at hσ'; cases hσ'
      · have hev := (Mma.mfired hp hX he hσ).1
        obtain ⟨d', hd', hwc⟩ := block_next (ent := Mma.ent p L) hev hne hb
        have hnx : (thread p L h).next (Mma.minj p L h d n) e =
            some (some (Mma.minj p L h d' (Code.bump (cls L h) n e))) := by
          rw [Mma.next_minj, hd']; rfl
        refine ⟨fun hc => ?_, fun σ' hσ' => ?_⟩
        · have h0 := hnx.symm.trans hc
          cases h0
        have := hnx.symm.trans hσ'
        obtain rfl := Option.some.inj (Option.some.inj this)
        exact hwc

/-- **The collectives of two lanes of the MMA warp.** -/
theorem mma_pair (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hs : SameWarp L g h) (hw : Prologue.warpIndex L g = 12) :
    Sched.WarpPair m (Progress.timed p L) X (CollAt p L) (mmaShape p L) g h :=
  warpPair_of_cls hp hX hub (mmaCls hp hX hub (g / L.block)) hs ⟨hs.1.1, hw, rfl⟩
    ⟨hs.1.2.1, hs.2.symm.trans hw, hs.1.2.2.symm⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
