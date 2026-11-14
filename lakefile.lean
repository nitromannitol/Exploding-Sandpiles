import Lake
open Lake DSL

package «exploding-sandpiles» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "7f773dd0aa66dbe1ed1080ae0248906b9cfe5215"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

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
