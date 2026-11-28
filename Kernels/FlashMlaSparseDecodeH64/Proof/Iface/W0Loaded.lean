-- SPDX-License-Identifier: Apache-2.0
-- iface: W0Loaded producer=W1 status=stated domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The words a block has loaded when its code reaches a site

`W0Loaded l p`: after the events `l` of a lane of warps 0 to 3, a lane whose next event is at the
pc `p` of the loop (`p` at most the softmax-ready arrival, pc 1122) has loaded the words the
code up to `p` reads: the score halves (pcs 278 to 285) before the mask word (pc 289), the mask
word before the peer pairs, each peer pair (two reads at pc `477 + 5 k`) before the next, the
peer's row maximum (pc 572) after them; in the epilogue the accumulator words (pcs of
`w0OPcs`) before the rescales and the output chunks, the peer's row-sum word before the factor
and the log-sum-exp store; the rescale's stores and the staging stores read the same words.
A loaded word is not the default of `w0Words`, which is what the prefix facts of `W0Valid`
(`W0Early`: a word read is that of a valid block, or unread) need to speak of it.

It is a statement about the lane's events only (no state, no `HasUb`): it holds of the lane's
prefix before every event of a lane of warps 0 to 3. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- **The words loaded before the next event at pc `p`**, after the events `l` of the lane. -/
structure W0Loaded (l : List Event) (p : Nat) : Prop where
  /-- The score halves are loaded before the mask word. -/
  score : 289 ≤ p → p ≤ 1122 →
    (w0Words (w0Fin l).2).lo ≠ [] ∧ (w0Words (w0Fin l).2).hi ≠ []
  /-- The mask word is loaded before the peer pairs. -/
  mask : 289 < p → p ≤ 1122 → (w0Words (w0Fin l).2).mw ≠ .pred false
  /-- Each peer pair is loaded before the next site. -/
  pair : ∀ j < 8, 477 + 5 * j < p → p ≤ 1122 →
    (w0Words (w0Fin l).2).pw j ≠ (.pred false, .pred false)
  /-- The peer's row maximum is loaded before the vote. -/
  peerMax : 572 < p → p ≤ 1122 → (w0Words (w0Fin l).2).pm ≠ .pred false
  /-- The accumulator words are loaded before the rescales and the output chunks. -/
  acc : p ∈ [717, 814, 818, 915, 919, 1016, 1020, 1117, 1202, 1362, 1520, 1677,
      1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1491, 1492, 1493, 1494, 1495, 1496, 1497,
      1498, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1806, 1807, 1808, 1809, 1810, 1811,
      1812, 1813] → w0EpiO (w0Fin l).2 ≠ []
  /-- The peer's row-sum word is loaded before the factor and the log-sum-exp store. -/
  rowSum : p ∈ [1178, 1187, 1202, 1362, 1520, 1677,
      1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1491, 1492, 1493, 1494, 1495, 1496, 1497,
      1498, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1806, 1807, 1808, 1809, 1810, 1811,
      1812, 1813] → w0EpiPe (w0Fin l).2 ≠ .pred false

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
