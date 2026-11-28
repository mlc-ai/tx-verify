-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # The rendezvous schedule of a data lane

A data thread meets the CTA barriers at these pcs in this order, not counting the optional
rescale rendezvous at 2326: the two startup syncs (12, 14), the setup sync (180), five syncs per
preloaded block, the two publication syncs (573, 575), four syncs per loop round (the first round
has only two), and the epilogue's two publication syncs and the final sync. `dataBar p lim t` is
the pc of the `t`-th, for `p` preloaded blocks and loop limit `lim`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The number of rendezvous of the loop, in the position counting of `Softmax.fixedCount`. -/
def loopEnd (lim : Nat) : Nat := 4*lim + (if lim = 0 then 2 else 0)

/-- The `v`-th rendezvous of the preload blocks. -/
def preloadBar (v : Nat) : Nat :=
  ([[192, 201, 212, 222, 227], [236, 243, 254, 264, 269], [278, 285, 296, 306, 311]].getD (v/5)
    []).getD (v%5) 0

/-- The four fixed rendezvous of a loop round, by position in the round. -/
def roundBar (u : Nat) : Nat := [2241, 2251, 999, 1012].getD (u%4) 0

/-- The rendezvous after the preloads, by position `u` from the first publication sync. -/
def dataTail (lim u : Nat) : Nat :=
  if u = 0 then 573
  else if u = 1 then 575
  else if u < loopEnd lim then roundBar u
  else if u = loopEnd lim then 2846
  else if u = loopEnd lim + 1 then 2849
  else 2850

def dataBar (p lim t : Nat) : Nat :=
  if t < 3 then [12, 14, 180].getD t 0
  else if t < 3+5*p then preloadBar (t-3)
  else dataTail lim (t-(3+5*p))

theorem loopEnd_ge (lim : Nat) : 2 ≤ loopEnd lim := by
  unfold loopEnd
  split <;> omega

theorem dataBar_startup (p lim : Nat) :
    dataBar p lim 0 = 12 ∧ dataBar p lim 1 = 14 ∧ dataBar p lim 2 = 180 := by
  simp [dataBar]

theorem dataBar_block (p lim b j : Nat) (hb : b < p) (hj : j < 5) :
    dataBar p lim (3+5*b+j) = preloadBar (5*b+j) := by
  have h1 : ¬ 3+5*b+j < 3 := by omega
  have h2 : 3+5*b+j < 3+5*p := by omega
  have h3 : 3+5*b+j-3 = 5*b+j := by omega
  simp only [dataBar, h1, h2, h3, ↓reduceIte]

theorem dataBar_tail (p lim u : Nat) : dataBar p lim (3+5*p+u) = dataTail lim u := by
  have h1 : ¬ 3+5*p+u < 3 := by omega
  have h2 : ¬ 3+5*p+u < 3+5*p := by omega
  have h3 : 3+5*p+u-(3+5*p) = u := by omega
  simp only [dataBar, h1, h2, h3, ↓reduceIte]

theorem dataBar_publish (p lim : Nat) :
    dataBar p lim (3+5*p) = 573 ∧ dataBar p lim (3+5*p+1) = 575 := by
  have a := dataBar_tail p lim 0
  have b := dataBar_tail p lim 1
  simp only [Nat.add_zero] at a
  rw [a, b]
  simp [dataTail]

theorem dataBar_round (p lim i r : Nat) (hr : r < 4) (hi : i < lim) (h : 2 ≤ 4*i+r) :
    dataBar p lim (3+5*p+(4*i+r)) = roundBar r := by
  have e : loopEnd lim = 4*lim := by
    unfold loopEnd
    split <;> omega
  have h4 : ¬ 4*i+r = 0 := by omega
  have h5 : ¬ 4*i+r = 1 := by omega
  have h6 : 4*i+r < 4*lim := by omega
  have h7 : (4*i+r)%4 = r := by omega
  have h8 : r%4 = r := by omega
  simp only [dataBar_tail, dataTail, h4, h5, e, h6, ↓reduceIte, roundBar, h7, h8]

theorem dataBar_epilogue (p lim : Nat) :
    dataBar p lim (3+5*p+loopEnd lim) = 2846 ∧ dataBar p lim (3+5*p+loopEnd lim+1) = 2849 ∧
      dataBar p lim (3+5*p+loopEnd lim+2) = 2850 := by
  have := loopEnd_ge lim
  have a1 := dataBar_tail p lim (loopEnd lim)
  have a2 := dataBar_tail p lim (loopEnd lim+1)
  have a3 := dataBar_tail p lim (loopEnd lim+2)
  rw [← Nat.add_assoc] at a2 a3
  rw [a1, a2, a3]
  refine ⟨?_,?_,?_⟩ <;> unfold dataTail <;> (repeat' split) <;> (first | rfl | omega)

end PTX.Kernels.InklingRelDecode.Proof.Lib
