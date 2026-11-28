-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

def startupDecl : RoleDecl := ⟨[(0, 28), (2331, 2333), (2337, 2338)], [27, 2337]⟩
def proADecl : RoleDecl := ⟨[(27, 575)], [574]⟩
def smDecl : RoleDecl := ⟨[(574, 2331), (2560, 2566)], [2565]⟩
def epiDecl : RoleDecl := ⟨[(2565, 2853), (2855, 2856)], []⟩
def dispatchDecl : RoleDecl :=
  ⟨[(2337, 2345), (2422, 2423), (2333, 2334), (2853, 2854), (2557, 2558)],
    [2344, 2422, 2333, 2853, 2557]⟩
def loaderDecl : RoleDecl := ⟨[(2344, 2422), (2337, 2338)], [2337]⟩
def mmaDecl : RoleDecl := ⟨[(2422, 2557), (2337, 2338)], [2337]⟩
def idleDecl : RoleDecl := ⟨[(2333, 2338)], [2337]⟩
def badRoleDecl : RoleDecl := ⟨[(2557, 2560), (2337, 2338)], [2337]⟩
def workerExitDecl : RoleDecl := ⟨[(2853, 2856)], []⟩

/-- Every region is closed up to its exits. -/
theorem closed : [startupDecl, proADecl, smDecl, epiDecl, dispatchDecl, loaderDecl, mmaDecl,
    idleDecl, badRoleDecl, workerExitDecl].all
    (fun d => CodeCheck.closedFrom d.region d.exits 0 kernel.code) = true := by
  kernel_rfl

/-- The startup's event instructions: its sites and the two roles' first instructions. -/
def startupSites : List Nat := [11, 12, 13, 14, 15, 17, 27, 2337]

theorem startup_sites : CodeCheck.sitesFrom startupDecl.region 0 kernel.code = startupSites := by
  kernel_rfl

/-- The prologue's event instructions: its sites and the softmax region's first instruction. -/
def proASites : List Nat :=
  [27, 34, 37, 41, 130, 134, 135, 138, 139, 142, 143, 146, 147, 150, 151, 154, 155, 158,
    159, 162, 163, 166, 167, 170, 171, 174, 175, 178, 179, 180, 192, 193, 197, 201, 202, 203,
    211, 212, 213, 217, 220, 222, 223, 226, 227, 228, 231, 236, 237, 241, 243, 244, 245, 253,
    254, 255, 259, 262, 264, 265, 268, 269, 270, 273, 278, 279, 283, 285, 286, 287, 295, 296,
    297, 301, 304, 306, 307, 310, 311, 312, 315, 388, 390, 392, 394, 396, 398, 400, 402, 404,
    406, 408, 410, 412, 414, 416, 418, 420, 422, 424, 426, 428, 430, 432, 434, 436, 438, 440,
    442, 444, 446, 448, 450, 452, 454, 456, 458, 460, 462, 464, 466, 468, 470, 472, 474, 476,
    478, 480, 482, 484, 486, 488, 490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 512,
    514, 526, 532, 538, 544, 550, 556, 562, 568, 569, 570, 571, 573, 574]

theorem proA_sites : CodeCheck.sitesFrom proADecl.region 0 kernel.code = proASites := by
  kernel_rfl

end PTX.Kernels.InklingRelDecode.Proof
