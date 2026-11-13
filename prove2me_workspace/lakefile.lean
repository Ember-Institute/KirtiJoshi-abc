import Lake
open Lake DSL

package «prove2me» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Platform pin: 0df444a360eaa60ab8c11dca51a86af692955474
require mathlib from "/home/admin-wsl/Coq/mathlib4-0df444a"

lean_lib «Definitions» where
lean_lib «Theorems» where
@[default_target]
lean_lib «Solutions» where
