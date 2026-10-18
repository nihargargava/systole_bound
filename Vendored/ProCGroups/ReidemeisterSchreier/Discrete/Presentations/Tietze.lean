module

public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorQuotientMutualMapData
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Core
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorReplacement
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Script

@[expose] public section

/-!
# Tietze equivalences and verified scripts

This aggregate separates semantic presentation equivalence from syntactic
transformations.  The core and generator/relator operation modules construct
certificates; `Tietze.Script` records well-typed elementary move sequences and
their trace and cost.
-/
