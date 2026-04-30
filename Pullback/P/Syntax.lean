import Lean
import Pullback.P.Basic
import Qq

open Lean
open Std

open Lean Meta Elab Term PrettyPrinter Delaborator

declare_syntax_cat pexpr
declare_syntax_cat ptype

syntax "ptype{" ptype "}" : term
syntax "pexpr{" pexpr "}" : term

namespace PType

syntax:50 ptype:51 "->" ptype:50 : ptype
syntax "(" ptype ")" : ptype
syntax "`(" term ")" : ptype
syntax "b(" term ")" : ptype

macro_rules
  | `(ptype{$a -> $b}) =>
      `(PType.fun (ptype{$a}) (ptype{$b}))
  | `(ptype{($x)}) =>
      `(ptype{$x})
  | `(ptype{`($x)}) => `($x)
  | `(ptype{b($x)}) => `(PType.ofBase $x)

end PType


namespace PExpr

syntax ident : pexpr
syntax:50 pexpr:50 pexpr:51 : pexpr
syntax "fun" ident ":" ptype "=>" pexpr : pexpr
syntax "let" ident ":=" pexpr "in" pexpr : pexpr
syntax "(" pexpr ")" : pexpr
syntax "`(" term ")" : pexpr
syntax "c(" term ")" : pexpr

macro_rules
  | `(pexpr{$x:ident}) =>
      `(PExpr.var $(Quote.quote x.getId))
  | `(pexpr{$f $x}) =>
      `(PExpr.app pexpr{$f} pexpr{$x})
  | `(pexpr{fun $x : $tx => $body}) =>
      `(PExpr.lam $(Quote.quote x.getId) ptype{$tx} pexpr{$body})
  | `(pexpr{let $x := $v in $b}) =>
      `(PExpr.letE $(mkIdent x.getId) pexpr{$v} pexpr{$b})
  | `(pexpr{($x)}) => `(pexpr{$x})
  | `(pexpr{`($x)}) => `($x)
  | `(pexpr{c($x)}) => `(PExpr.const $x)

end PExpr
