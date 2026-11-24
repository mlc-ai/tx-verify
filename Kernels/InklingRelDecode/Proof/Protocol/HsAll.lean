-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsPkg
public import Kernels.InklingRelDecode.Proof.Protocol.HsLife

@[expose] public section

/-!
# The S/P/O handshake package from the threads' states: umbrella

`HsData` (the package's data, `poll_class`), `HsMma` (the MMA lane's counts, `qkAt_of`,
`pvAt_of`), `HsFacts` (the commits, `SO.Facts`), `HsParity` (the parities of the handshake
polls), `HsRoute` (the counted fields of `Mbar.Route`), `HsStore` and `HsRdv` (`Sr.Lane.st`,
`soft_bar`), `HsPkg` (`PkgRest`, `pkg_of`), `HsLife` (`SO.TmemLife.alloc_before`).
-/
