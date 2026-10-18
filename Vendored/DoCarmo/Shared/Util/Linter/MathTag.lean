module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/shared/Shared/Util/Linter/MathTag.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public meta import Lean

public meta section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# `Math/Eng/Mixed` docstring-tag linter

Enforces the Shared documentation convention: any declaration
whose docstring is present must begin with one of the tags
`**Math.**`, `**Eng.**`, or `**Mixed.**`.

Declarations without docstrings are silently skipped — the linter
mandates a tag *if* a docstring exists, not the docstring itself.

Activated by default. Silence locally with
`set_option linter.shared.mathTag false in <decl>`, or fix the tag.

See CLAUDE.md "Code quality / Math-Eng-Mixed tagging".
-/

open Lean Elab Linter

namespace Shared.Linter.MathTag

/--
The Shared Math/Eng/Mixed docstring-tag linter.

Every declaration with a docstring must begin its docstring with one of
`**Math.**`, `**Eng.**`, or `**Mixed.**`. The tag is the primary signal
when reading a file — Math reads as the textbook content, Eng is
engineering scaffolding, Mixed is a Math signature with engineering
proof body.
-/
register_option linter.shared.mathTag : Bool := {
  defValue := true
  descr := "Enforce **Math.**/**Eng.**/**Mixed.** docstring tag on declarations."
}

private def acceptedTags : List String := ["**Math.**", "**Eng.**", "**Mixed.**"]

private def hasAcceptedTag (s : String) : Bool :=
  let t := s.trimAsciiStart.toString
  acceptedTags.any fun tag => t.startsWith tag

@[inherit_doc linter.shared.mathTag]
def mathTagLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.shared.mathTag (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  unless hasAcceptedTag docString do
    let preview := (docString.trimAscii.toString.take 40).replace "\n" " "
    Linter.logLint linter.shared.mathTag docStx
      m!"docstring should start with **Math.**, **Eng.**, or **Mixed.** \
         (got: \"{preview}…\")"

initialize addLinter mathTagLinter

end Shared.Linter.MathTag

