-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Lemmas.Kernel.CodeCheck
public import Tactics.KernelRfl

@[expose] public section

/-! # The roles' regions of the code and their exits (closed: `Closed.lean`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A fragment's region of the code and the pcs where control may leave it. -/
structure Decl where
  region : List (Nat × Nat)
  exits : List Nat

def startupDecl : Decl :=
  ⟨[(0, 180), (1901, 1908), (2768, 2770), (3099, 3103), (7742, 7747), (9205, 9206)],
    [179, 1907, 2769, 3102, 7746, 9205]⟩

def loaderDecl : Decl :=
  ⟨[(179, 1908), (2768, 2770), (3099, 3103), (7742, 7747), (9205, 9206)],
    [1907, 2769, 3102, 7746, 9205]⟩

def mmaDecl : Decl :=
  ⟨[(1907, 2768), (3099, 3103), (7742, 7747), (9205, 9206)], [3102, 7746, 9205]⟩

def epilogueDecl : Decl :=
  ⟨[(2769, 3103), (7742, 7747), (9205, 9206)], [3102, 7746, 9205]⟩

def softmaxDecl : Decl := ⟨[(3102, 7747), (9205, 9206)], [7746, 9205]⟩

def correctionDecl : Decl := ⟨[(7746, 9206)], [9205]⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
