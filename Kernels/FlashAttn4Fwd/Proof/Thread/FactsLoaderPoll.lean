-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp

@[expose] public section

/-! # The loader's part of `Cross.PollAgree`

Two lanes of warp 14 polling at one position in one round poll one barrier with one parity. The
position names the site (`Loader.poll_site_inj`). At an item poll the round is the item (a use of
the item's first four) or the item's trips and the trip (a use of each trip) (`Counts.rounds`), so
the two lanes are at the same item and trip (`Loader.mul_add_inj`); at a drain poll the state is
past every item. The lanes are in one CTA, so they have one item count, and the ring registers are
those of one use (`Loader.ring_eq`). The barrier and the parity of a poll are those of the site and
the ring use (`Loader.wait_fact`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Loader
open Work

/-- Two poll sites at one position are one site. -/
theorem poll_site_inj (s s' : Site) (h : s.pc ∈ waitPcs) (h' : s'.pc ∈ waitPcs)
    (hp : s.pc = s'.pc) : s = s' := by
  rcases site_wait s' h' with ⟨u, rfl⟩ | ⟨k, rfl⟩ | rfl
  · exact wait_pc_inj s u h hp
  · rcases site_wait s h with ⟨u, rfl⟩ | ⟨k', rfl⟩ | rfl
    · exfalso; revert hp; revert k; cases u <;> decide
    · revert hp; revert k k'; decide
    · exfalso; revert hp; revert k; decide
  · rcases site_wait s h with ⟨u, rfl⟩ | ⟨k', rfl⟩ | rfl
    · exfalso; revert hp; cases u <;> decide
    · exfalso; revert hp; revert k'; decide
    · rfl

/-- A number written as `a N + b` with `b < N` determines `a` and `b`. -/
theorem mul_add_inj {a b a' b' N : Nat} (h : a * N + b = a' * N + b') (hb : b < N)
    (hb' : b' < N) : a = a' ∧ b = b' := by
  have hN : 0 < N := by omega
  have h1 : (a * N + b) / N = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hb, Nat.add_zero]
  have h2 : (a' * N + b') / N = a' := by
    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hb', Nat.add_zero]
  have h3 : (a * N + b) % N = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have h4 : (a' * N + b') % N = b' := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  exact ⟨by rw [← h1, h, h2], by rw [← h3, h, h4]⟩

/-- The ring use and the Q parity count of a state are functions of its site, item, trip and
the item count. -/
theorem ring_eq {g h : Nat} {a b : D} (hs : a.site = b.site) (hns : a.site ≠ .setMaxReg)
    (hT : T L g = T L h)
    (hi : a.site.inItem = true → a.i = b.i) (ht : a.site.inTrip = true → a.t = b.t) :
    kvB L g a = kvB L h b ∧ qB L g a = qB L h b := by
  obtain ⟨sa, ia, ta, xa, ya, za⟩ := a
  obtain ⟨sb, ib, tb, xb, yb, zb⟩ := b
  simp only at hs hns hi ht
  subst hs
  cases sa <;> (try cases ‹UseK›) <;> simp_all [kvB, qB, Site.inItem, Site.inTrip]

/-- At use `u`'s poll site, the use's rounds: the item, or the item's trips and the trip. -/
theorem roundOf_wait {g : Nat} {d : D} {u : UseK} (hs : d.site = .wait u) :
    roundOf L g d u = if u.trip then d.i * (n L - 1) + d.t else d.i := by
  obtain ⟨site, i, t, x, y, z⟩ := d
  simp only at hs
  subst hs
  cases u <;> simp [roundOf, Site.inTrip, Site.ord, UseK.word, UseK.trip]

end Loader

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`Cross.PollAgree` for warp 14**: two lanes polling at one position in one round poll one
barrier with one parity. -/
theorem Cross.PollAgree_loader : ∀ {g h k k' pc p p' : Nat} {m m' : Loc}
    {ok ok' acq acq' : Bool} {sc sc' : MbarScope} {d d' : ThreadD}, warpOf L g = 14 →
    SameWarp L g h → St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ →
    pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k') → m = m' ∧ p % 2 = p' % 2 := by
  intro g h k k' pc p p' m m' ok ok' acq acq' sc sc' d d' hw hs _ _ he he' hr
  have hcta : ctaOf L g = ctaOf L h := hs.1.2.2
  have hwh : warpOf L h = 14 := by have := hs.2; simp only [warpOf] at hw ⊢; omega
  obtain ⟨a, ta, ia, oa, -, hJa, hha, hia, hca, hfa⟩ :=
    Loader.origin hpre hX ht he nofun (by simp [Prologue.ProKind]) hw
  obtain ⟨b, tb, ib, ob, -, hJb, hhb, hib, hcb, hfb⟩ :=
    Loader.origin hpre hX ht he' nofun (by simp [Prologue.ProKind]) hwh
  obtain ⟨ba, -, hma, -, -, hba, hpa⟩ :=
    Loader.wait_fact hpre (Frame.lt_of_get hX he) hJa hia hha hca hfa rfl
  obtain ⟨bb, -, hmb, -, -, hbb, hpb⟩ :=
    Loader.wait_fact hpre (Frame.lt_of_get hX he') hJb hib hhb hcb hfb rfl
  have hpca : pc = a.site.pc := Loader.fires_pc hfa
  have hpcb : pc = b.site.pc := Loader.fires_pc hfb
  have hwa := OpPcsFast.mem Loader.kernel_wait_pcs hca (Loader.waitOp_of hfa rfl)
  have hwb := OpPcsFast.mem Loader.kernel_wait_pcs hcb (Loader.waitOp_of hfb rfl)
  have hsite : a.site = b.site := Loader.poll_site_inj _ _ hwa hwb (hpca.symm.trans hpcb)
  have hT : Work.T L g = Work.T L h := by
    simp only [Work.T, Work.cid, clusterOf]
    rw [hcta]
  -- the item and the trip, from the rounds at an item poll
  have hit : (a.site.inItem = true → a.i = b.i) ∧ (a.site.inTrip = true → a.t = b.t) := by
    rcases Loader.site_wait a.site hwa with ⟨u, hu⟩ | ⟨kk, hu⟩ | hu
    · have hra := hJa.rounds u
      have hrb := hJb.rounds u
      have hpu : (Loader.Site.wait u).pc = pc := by rw [← hu, ← hpca]
      rw [hpu] at hra hrb
      have hround : Loader.roundOf L g a u = Loader.roundOf L h b u := by
        rw [← hra, ← hrb, hr]
      rw [Loader.roundOf_wait hu, Loader.roundOf_wait (hsite ▸ hu)] at hround
      cases hu' : u.trip
      · simp only [hu', Bool.false_eq_true, ↓reduceIte] at hround
        refine ⟨fun _ => hround, fun htr => ?_⟩
        rw [hu] at htr
        cases u <;> simp [Loader.UseK.trip, Loader.Site.inTrip] at hu' htr
      · simp only [hu', ↓reduceIte] at hround
        have hta := hia.trip (by
          rw [hu]; cases u <;> simp_all [Loader.UseK.trip, Loader.Site.inTrip])
        have htb := hib.trip (by
          rw [← hsite, hu]; cases u <;> simp_all [Loader.UseK.trip, Loader.Site.inTrip])
        obtain ⟨h1, h2⟩ := Loader.mul_add_inj hround (by omega) (by omega)
        exact ⟨fun _ => h1, fun _ => h2⟩
    · rw [hu]; exact ⟨fun h => by simp [Loader.Site.inItem] at h,
        fun h => by simp [Loader.Site.inTrip] at h⟩
    · rw [hu]; exact ⟨fun h => by simp [Loader.Site.inItem] at h,
        fun h => by simp [Loader.Site.inTrip] at h⟩
  have hns : a.site ≠ .setMaxReg := by
    rcases Loader.site_wait a.site hwa with ⟨u, hu⟩ | ⟨kk, hu⟩ | hu <;> rw [hu] <;> simp
  obtain ⟨hB, hQ⟩ := Loader.ring_eq hsite hns hT hit.1 hit.2
  refine ⟨?_, ?_⟩
  · rw [hma, hmb, hba, hbb, hsite, hB, hcta]
  · rw [hpa, hpb, hsite, hB, hQ]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
