import Lake
open Lake DSL

require «verso-slides» from git "https://github.com/leanprover/verso-slides.git"@"main"

package «lean-database-slides» where
  version := v!"0.1.0"

lean_lib Slides where
  needs := #[`@verso/+Verso.Code.External:highlighted]

@[default_target] lean_exe «lean-database-slides» where
  root := `Main
