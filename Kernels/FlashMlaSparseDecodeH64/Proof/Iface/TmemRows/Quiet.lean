-- SPDX-License-Identifier: Apache-2.0
-- iface: TmemRow.Wg1 producer=A status=row-proved domain=consistent ahead=1
-- iface: TmemRow.Tma producer=A status=row-proved domain=consistent ahead=1
-- iface: TmemRow.Index producer=A status=row-proved domain=consistent ahead=1
-- iface: TmemRow.Dequant producer=D status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant

@[expose] public section

/-! # The roles without Tensor Memory: their rows

Warpgroup 1's head and idle code (pcs 1842–1849, 2587–2605), the TMA lane's (2162–2331), the
index warp's (2332–2586) and warpgroup 2's (2606–3610) hold no `tcgen05` site (`quiet_sites`), and
the final `ret` (3611) is none. The rows: no `tcgen05` event at a pc of these roles. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmemRow

end TmemRow

/-- **Row `TmemRow.Wg1`**: warpgroup 1 fires no `tcgen05` event. -/
def TmemRow.Wg1 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (Wg1At L) fun _ _ => False

/-- **Row `TmemRow.Tma`**: the TMA lane fires no `tcgen05` event. -/
def TmemRow.Tma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (TmaAt L) fun _ _ => False

/-- **Row `TmemRow.Index`**: the index warp fires no `tcgen05` event. -/
def TmemRow.Index (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (IndexAt L) fun _ _ => False

/-- **Row `TmemRow.Dequant`**: warpgroup 2 fires no `tcgen05` event. -/
def TmemRow.Dequant (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (DequantAt L) fun _ _ => False

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
