-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow Control

def measure (d : D) := 4*574 - d.site.rank

theorem rank_bound (s : Site) : s.rank ≤ 4*574 := by
  cases s <;> repeat' first | decide | (rename_i j; revert j)

theorem measure_next {Q L g d dn ev} (hn : Control.next Q L g d ev = some (some dn)) :
    measure dn < measure d := by
  have lt := rank_next hn
  have bound := rank_bound dn.site
  unfold measure; omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue
