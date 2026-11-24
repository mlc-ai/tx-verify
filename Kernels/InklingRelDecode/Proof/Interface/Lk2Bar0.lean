-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk2Lock
public import Kernels.InklingRelDecode.Proof.Interface.Lk2NumPre
public import Kernels.InklingRelDecode.Proof.Interface.ShapeLoaderPage
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSameValue

@[expose] public section

/-!
# The loop-entry counters of the loader and of the MMA warp

At its loop entry (`bar0`) the loader carries `i = num_pre` and `n = num_iters` of its CTA, the MMA
warp `i = 0` and `n = num_iters`. `n` is `LoaderPage` (`ShapeLoaderPage.lean`) and `WordsInv`
(`ShapeWords.lean`); `i = num_pre` is the read of the first element of the loader's vector load
(`NumPreRead`), and the MMA warp's `i = 0` is its first state's. So two lanes of a warp carry the
same counters at `bar0` (`Bar0Counters`, `Lk2Lock.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The counter a state has before the loop's entry: the loader's is `num_pre` from the read of
its first element, the MMA warp's is 0. -/
def IPre (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .w (.loader d _) => (d.site = .ld1 ∨ d.site = .bar0) →
      d.i = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)
  | .w (.mma d _) => (d.site = .setMaxReg ∨ d.site = .ldNum ∨ d.site = .bar0) → d.i = 0
  | _ => True

theorem loader_next_pre {d d' : Loader.D} {e : Event} {np : Nat}
    (h : Loader.next L g d e = some (some d')) (hnp : np < 2 ^ 31)
    (hi : (d.site = .ld1 ∨ d.site = .bar0) → d.i = np)
    (h0 : d.site = .ld0 → ∃ pc ac bs, e = ⟨pc, .rd ac bs⟩ ∧ bs = (b32 np).toBytes.map some) :
    (d'.site = .ld1 ∨ d'.site = .bar0) → d'.i = np := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  by_cases hs : s = .ld0
  · subst hs
    obtain ⟨pc, ac, bs, rfl, rfl⟩ := h0 rfl
    simp only [Loader.next, rebuild_b32, Option.some.injEq] at h
    subst h
    intro _
    simp only [Loader.readI, Raw.word32Of_b32, Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only at hi
    cases s <;> first
      | exact absurd rfl hs
      | (simp only [Loader.next, Loader.afterIter, Loader.readN] at h
         (repeat' split at h) <;>
           first
           | (simp at h; done)
           | (simp only [Option.some.injEq] at h
              subst h
              simp_all))

theorem mma_next_pre {d d' : Mma.D} {e : Event}
    (h : Mma.next L g d e = some (some d'))
    (hi : (d.site = .setMaxReg ∨ d.site = .ldNum ∨ d.site = .bar0) → d.i = 0) :
    (d'.site = .setMaxReg ∨ d'.site = .ldNum ∨ d'.site = .bar0) → d'.i = 0 := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  simp only at hi
  cases s <;> simp only [Mma.next, Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext,
    Mma.pvNext] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       simp_all)

/-- **The dispatch enters the MMA warp at its first site with the counter 0.** -/
theorem dispatch_mma {e : Event} {P : Loader.Pro} {a : WComp.WSt}
    (h : WComp.dispatch L g P e = some (some a)) {d : Mma.D} {P' : Loader.Pro}
    (ha : a = .mma d P') : d.site = .setMaxReg ∧ d.i = 0 := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    rcases (EvW.ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
      simp only [WComp.roleStart] at h
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
    · split at h
      · split_ifs at h
        · simp only [Option.some.injEq] at h
          subst h
          simp only [WComp.WSt.mma.injEq] at ha
          obtain ⟨rfl, -⟩ := ha
          exact ⟨rfl, rfl⟩
        · cases h
      · cases h
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
    · simp only [Option.some.injEq] at h
      subst h
      cases ha
  · cases h
  · cases h

/-- **A composed worker step keeps `IPre`.** -/
theorem ipre_wstep (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hp : NumPreRead Q L X) {k : Nat} {e : Event}
    {s0 a : WComp.WSt} (he : X.get (g, k) = some e) (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.w s0))) (hi : IPre Q L g (.w s0))
    (h : WComp.next L g s0 e = some (some a)) : IPre Q L g (.w a) := by
  cases s0 with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨s, P⟩ := w
      simp only at hs
      subst hs
      cases a with
      | loader d' P' =>
        have hd := dispatch_loader (by simpa [WComp.next] using h) rfl
        intro h'
        rcases h' with h' | h' <;> rw [hd] at h' <;> cases h'
      | mma d' P' =>
        have hd := dispatch_mma (by simpa [WComp.next] using h) rfl
        intro _
        exact hd.2
      | _ => trivial
    · rw [EvW.next_worker_map hs] at h
      obtain ⟨w', hw, rfl⟩ := EvW.map_map_some h
      trivial
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_idle_map hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      trivial
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_loader_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      refine loader_next_pre hd ?_ hi ?_
      · have : ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ≤ 3 := by
          unfold ProA.numPre
          exact Nat.min_le_right _ _
        omega
      · intro h0
        obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
        obtain ⟨t, hgd, hfire⟩ := hF
        have hr := hf.reach hg hσ
        have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
          ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
        unfold EvW.LdShape at hsh
        rw [h0] at hsh
        obtain ⟨ac, bs, he2, hloc, hsz, -⟩ := hsh
        exact ⟨_, ac, bs, he2, hp (pc := Loader.Site.pc .ld0) (a := ac) (bs := bs)
          (by rw [← he2]; exact he) hσ (by show d.site = .ld0; exact h0) hloc hsz⟩
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · rw [EvW.next_mma_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      exact mma_next_pre hd hi
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · have h' : some (some (WComp.WSt.exit ⟨.ret, P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      trivial
    · cases h

/-- **Every state keeps `IPre`.** -/
theorem ipre_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hp : NumPreRead Q L X) :
    ∀ (k : Nat) (s : TSt), St Q L X g k = some (some s) → IPre Q L g s := by
  refine stateAt_induction (IPre Q L g) ?_ ?_
  · show IPre Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> trivial
  · intro k e s s' he' hσ hi hnx
    have he : X.get (g, k) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    cases s with
    | d s0 =>
      rw [next_d] at hnx
      obtain ⟨a, -, h⟩ := map_map_eq_some_some hnx
      subst h
      trivial
    | w s0 =>
      rw [next_w] at hnx
      obtain ⟨a, ha, h⟩ := map_map_eq_some_some hnx
      subst h
      exact ipre_wstep hpre hX hf hp he hg hσ hi ha

/-- **The lanes of a warp carry the same counters at the loop entry.** -/
theorem bar0Counters_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    (hp : NumPreRead Q L X) : Bar0Counters Q L X where
  loader := by
    intro g h a b d d' P P' hw hsa hsb hd hd'
    have hc : g / L.block = h / L.block := hw.1.2.2
    have h1 := ipre_inv hpre hX hf hp (g := g) a _ hsa
    have h2 := ipre_inv hpre hX hf hp (g := h) b _ hsb
    have p1 := page_inv hpre hX hf hn (g := g) a _ hsa
    have p2 := page_inv hpre hX hf hn (g := h) b _ hsb
    have n1 := p1.1 (by simp [preLoop, hd])
    have n2 := p2.1 (by simp [preLoop, hd'])
    have i1 := h1 (Or.inr hd)
    have i2 := h2 (Or.inr hd')
    rw [ProA.cta_eq_of_block hc .z, ProA.cta_eq_of_block hc .x] at i1 n1
    exact ⟨by rw [i1, i2], by rw [n1, n2]⟩
  mma := by
    intro g h a b d d' P P' hw hsa hsb hd hd'
    have hc : g / L.block = h / L.block := hw.1.2.2
    have h1 := ipre_inv hpre hX hf hp (g := g) a _ hsa
    have h2 := ipre_inv hpre hX hf hp (g := h) b _ hsb
    have w1 := words_inv hpre hX hf hb hn (g := g) a _ hsa
    have w2 := words_inv hpre hX hf hb hn (g := h) b _ hsb
    have n1 := (w1.2.2 (by rw [hd]; decide) (by rw [hd]; decide)).1
    have n2 := (w2.2.2 (by rw [hd']; decide) (by rw [hd']; decide)).1
    rw [ProA.cta_eq_of_block hc .z, ProA.cta_eq_of_block hc .x] at n1
    exact ⟨by rw [h1 (Or.inr (Or.inr hd)), h2 (Or.inr (Or.inr hd'))], by rw [n1, n2]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
