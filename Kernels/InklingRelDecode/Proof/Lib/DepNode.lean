-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ReachJoint

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- A node of the dependency order: an issue or a return of a thread event or of its
asynchronous part. -/
abbrev DepNode := AsyncCopy.Ref × Bool

end PTX.Kernels.InklingRelDecode.Proof.Lib
