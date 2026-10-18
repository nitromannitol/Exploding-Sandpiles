import Lake
open Lake DSL

package «exploding-sandpiles» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "78f4b2cec065fa2fb5116b06c41966855f62cf50"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «Exploding» where
  globs := #[.andSubmodules `Exploding]

/-- The comparator audit surface (`ExplodingAudit/*/Challenge.lean`,
`ExplodingAudit/*/Solution.lean`).  Deliberately **not** a default target: it builds only on
demand (`lake build ExplodingAudit`), so the ordinary project build is unchanged. -/
lean_lib «ExplodingAudit» where
  globs := #[.submodules `ExplodingAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
