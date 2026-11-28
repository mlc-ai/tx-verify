-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Protocol.KV.PreloadDue
import Kernels.InklingRelDecode.Proof.Protocol.KV.Ordinal

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing

private theorem due_blk {Q L X m g y p n} (hX : Consistent L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hg : g < L.threads) (hne : X.tr g ≠ []) (hy : y < L.threads)
    (hc : y / L.block = g / L.block) (due : Due Q L X g y p n) (short : (X.tr y).countP p < n) :
    Blk (schedule Q L) X g :=
  blk_of_lagsN hX hu hg hne hy (congrArg L.clusterOfCta hc) fun _ =>
    ⟨fun _ _ he => (short.not_ge (due.1 _ _ he)),Nat.lt_of_not_ge fun h => short.not_ge (due.2 h)⟩

private theorem sum_arr (δ n : Nat) : ∑ b, dueArr δ n b = n := by
  simp [Fin.sum_univ_two,dueArr]
  omega

private theorem sum_cp (δ n : Nat) : ∑ b, dueCp δ n b = 8*n := by
  simp [Fin.sum_univ_three,dueCp]
  omega

private theorem warps (b : Fin 3) : (if b = 2 then 6 else b.val) < 8 := by
  split <;> omega

private theorem copy_inj {Q L m X c} (hp : Pre Q L m) (hc : c < L.grid) :
    Function.Injective (copyLane L X c) := by
  intro a b hab
  have ha := (leader_warp (X := X) hp hc (warps a)).2.2
  have hb := (leader_warp (X := X) hp hc (warps b)).2.2
  change copyLane L X c a % L.block / 32 = _ at ha
  change copyLane L X c b % L.block / 32 = _ at hb
  rw [hab,hb] at ha
  exact (by decide : ∀ i j : Fin 3, (if j = 2 then 6 else j.val) =
    (if i = 2 then 6 else i.val) → i = j) a b ha

private theorem arr_props {Q L m c} (hp : Pre Q L m) (hc : c < L.grid) (b : Fin 2) :
    arrivalLane L c b < L.threads ∧ arrivalLane L c b / L.block = c := by
  simp only [arrivalLane,Launch.threads,hp.block]
  split <;> omega

theorem ready_blk {Q L m X g l q sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : ¬ HasUb X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (hi : Mbar.InitRows L X) (_won : WonCommit L X)
    (words : RoleBytes L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨2462,.wait l q false true sc⟩) :
    WaitBlk (schedule Q L) X g l q := by
  classical
  have hf := followed X hX
  obtain ⟨s,rfl,hq⟩ := next_slot (r := .ready) rows hn
  let c := g / L.block
  let l := Ring.ready.obj L c s
  let n := okPolls l (X.tr g) + 1
  let δ := preload Q L c s
  have hg := hn.lt
  have hc : c < L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have hw : Waiting L m X .ready c s g := ⟨rfl,q,sc,hn⟩
  have ring := ready_slot hp hX hf (rows X hX) hi hc s
  obtain ⟨st,hst⟩ := Unit.final_of_init hX ring.full_init ring.full_noInval
    (wait_published hp hX hw)
  refine ⟨st,hst,fun hpar => ?_⟩
  have hle := ready_phase hX ring slot_fits (g := g)
    (fun he hm => hm ▸ commit_before_wait hp hX followed rows hw he hm) hst
  change st.phase ≤ okPolls l (X.tr g) + 1 at hle
  change q%2 = (okPolls l (X.tr g) + 0)%2 at hq
  have hpast : st.phase < n := by dsimp [n]; omega
  have ne := (poll_floor hp hf (by decide) hn).1
  have short := ready_short hX ring slot_fits hst
  rcases short with ha | hpkt
  · have inj : Function.Injective (arrivalLane L c) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [arrivalLane] at *
    have hsum := arrivals_recorded hX ring slot_fits _ inj
    change ∑ b, (X.tr (arrivalLane L c b)).countP (arrivesOn l) ≤ _ at hsum
    by_contra! hblk
    have allDue (b : Fin 2) : dueArr δ n b ≤ (X.tr (arrivalLane L c b)).countP (arrivesOn l) := by
      by_contra! h
      obtain ⟨hy,hc'⟩ := arr_props hp hc b
      apply hblk (due_blk hX hu hg ne hy hc' _ h)
      fin_cases b
      · exact preload_arrive_due hp hX hf hw
      · exact loader_arrive_due hp hX hf rows words (.of_noUb hu) hw
    have bound := (Finset.sum_le_sum fun b _ => allDue b).trans hsum
    rw [sum_arr] at bound
    omega
  · by_cases ht : Descent.Obl L X .tensor
    · exact .inl ⟨.tensor,.inr (.inr (.inl rfl)),ht⟩
    have hsum := copies_recorded hX ring slot_fits (copyLane L X c) (copy_inj hp hc) ht
    change ∑ b, (X.tr (copyLane L X c b)).countP (issuesTo l) ≤ _ at hsum
    change _ < 8 * (st.phase+1) at hpkt
    by_contra! hblk
    have allDue (b : Fin 3) : dueCp δ n b ≤ (X.tr (copyLane L X c b)).countP (issuesTo l) := by
      by_contra! h
      obtain ⟨hy,hc',_⟩ := leader_warp (X := X) hp hc (warps b)
      apply hblk
      apply due_blk hX hu hg ne hy hc' _ h
      by_cases worker : b=2
      · subst b
        exact loader_copy_due hp hX hf rows words (.of_noUb hu) hw
      · exact preload_copy_due hp hX hf hw b worker
    have bound := (Finset.sum_le_sum fun b _ => allDue b).trans hsum
    rw [sum_cp] at bound
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
