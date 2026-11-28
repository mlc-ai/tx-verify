-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

private theorem split_token {n s K s' K' : Nat} (pos : 0 < n) (hK : K < n) (hK' : K' < n)
    (h : s * n + K = s' * n + K') : s = s' ∧ K = K' := by
  have h1 : (s * n + K) / n = s := by
    rw [Nat.mul_comm, Nat.mul_add_div pos, Nat.div_eq_of_lt hK, Nat.add_zero]
  have h2 : (s' * n + K') / n = s' := by
    rw [Nat.mul_comm, Nat.mul_add_div pos, Nat.div_eq_of_lt hK', Nat.add_zero]
  have hs : s = s' := by rw [← h1, ← h2, h]
  subst hs
  omega

/-- Two output elements at one location are one element. -/
theorem oLoc_inj {s K h c s' K' h' c' : Nat} (pos : 0 < Q.nTok) (hK : K < Q.nTok)
    (hK' : K' < Q.nTok) (hh : h < 12) (hh' : h' < 12) (hc : c < 128) (hc' : c' < 128)
    (e : oLoc Q s K h c = oLoc Q s' K' h' c') : s = s' ∧ K = K' ∧ h = h' ∧ c = c' := by
  have a := congrArg Loc.addr e
  simp only [oLoc, heads, headDim] at a
  have b : ((s * Q.nTok + K) * 12 + h) * 128 + c = ((s' * Q.nTok + K') * 12 + h') * 128 + c' := by
    omega
  have h1 : s * Q.nTok + K = s' * Q.nTok + K' := by omega
  obtain ⟨hs, hk⟩ := split_token pos hK hK' h1
  exact ⟨hs, hk, by omega, by omega⟩

/-- Two LSE elements at one location are one element. -/
theorem lseLoc_inj {s K h s' K' h' : Nat} (pos : 0 < Q.nTok) (hK : K < Q.nTok)
    (hK' : K' < Q.nTok) (hh : h < 12) (hh' : h' < 12)
    (e : lseLoc Q s K h = lseLoc Q s' K' h') : s = s' ∧ K = K' ∧ h = h' := by
  have a := congrArg Loc.addr e
  simp only [lseLoc, heads] at a
  have h1 : s * Q.nTok + K = s' * Q.nTok + K' := by omega
  obtain ⟨hs, hk⟩ := split_token pos hK hK' (by omega)
  exact ⟨hs, hk, by omega⟩

/-- The tokens of two requests meet only in one request. -/
theorem request_of_token (hp : Pre Q L m) {z z' a b : Nat} (hz : z < Q.b) (hz' : z' < Q.b)
    (ha : a < Q.qLen z) (hb : b < Q.qLen z') (e : Q.qStart z + a = Q.qStart z' + b) :
    z = z' ∧ a = b := by
  have key : ∀ {z z' a b : Nat}, z < z' → z' < Q.b → a < Q.qLen z →
      Q.qStart z + a = Q.qStart z' + b → False := by
    intro z z' a b lt hz' ha e
    have h1 := qStart_le hp (r := z) (by omega)
    have h2 := qStart_mono hp (r := z + 1) (r' := z') (by omega) hz'.le
    omega
  rcases Nat.lt_trichotomy z z' with lt | eq | gt
  · exact (key lt hz' ha e).elim
  · subst eq; exact ⟨rfl, by omega⟩
  · exact (key gt hz hb e.symm).elim

/-- The data-lane thread is fixed by its CTA coordinates, its row and its column half. -/
theorem thread_of_row (hp : Pre Q L m) {g g' : Nat} (hg : g < L.threads) (hg' : g' < L.threads)
    (lane : g % L.block < 128) (lane' : g' % L.block < 128)
    (hx : (L.ctaidOf (g / L.block)).get .x = (L.ctaidOf (g' / L.block)).get .x)
    (hy : (L.ctaidOf (g / L.block)).get .y = (L.ctaidOf (g' / L.block)).get .y)
    (hz : (L.ctaidOf (g / L.block)).get .z = (L.ctaidOf (g' / L.block)).get .z)
    (row : rowM (g % L.block) = rowM (g' % L.block))
    (bit : g % L.block / 16 % 2 = g' % L.block / 16 % 2) : g = g' := by
  have hc : g / L.block < L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads, Nat.mul_comm] using hg)
  have hc' : g' / L.block < L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads, Nat.mul_comm] using hg')
  rw [coordinates hp hc] at hx hy hz
  rw [coordinates hp hc'] at hx hy hz
  simp only [Dim3.get, kvHeads] at hx hy hz
  have rep : ∀ c : Nat, Q.b * (2 * (c / (2 * Q.b)) + c / Q.b % 2) + c % Q.b = c := by
    intro c
    have h1 := Nat.div_add_mod (c / Q.b) 2
    have h2 := Nat.div_add_mod c Q.b
    have h3 : c / Q.b / 2 = c / (2 * Q.b) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [h3] at h1
    rw [← h1] at h2
    exact h2
  have cta : g / L.block = g' / L.block := by
    rw [← rep (g / L.block), ← rep (g' / L.block), hx, hy, hz]
  have blk := hp.block
  have thr : g % L.block = g' % L.block := by
    unfold rowM at row
    omega
  have e1 := Nat.div_add_mod g L.block
  have e2 := Nat.div_add_mod g' L.block
  rw [cta, thr] at e1
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
