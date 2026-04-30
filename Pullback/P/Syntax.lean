import Lean
import Pullback.P.Basic
import Qq

open Lean
open Std

open Lean Meta Elab Term PrettyPrinter Delaborator

declare_syntax_cat rpexpr
declare_syntax_cat ptype

syntax "ptype{" ptype "}" : term
syntax "rpexpr{" rpexpr "}" : term

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

syntax ident : rpexpr
syntax:50 rpexpr:50 rpexpr:51 : rpexpr
syntax "fun" ident ":" ptype "=>" rpexpr : rpexpr
syntax "let" ident ":=" rpexpr "in" rpexpr : rpexpr
syntax "(" rpexpr ")" : rpexpr
syntax "`(" term ")" : rpexpr
syntax "c(" term ")" : rpexpr

macro_rules
| `(rpexpr{$x:ident}) =>
    `(RawPExpr.var $(Quote.quote x.getId))
| `(rpexpr{$f $x}) =>
    `(RawPExpr.app rpexpr{$f} rpexpr{$x})
| `(rpexpr{fun $x : $tx => $body}) =>
      `(RawPExpr.lam $(Quote.quote x.getId) ptype{$tx}
          rpexpr{$body})
| `(rpexpr{let $x := $v in $b}) =>
      `(RawPExpr.letE $(Quote.quote x.getId) rpexpr{$v}
          rpexpr{$b})
| `(rpexpr{($x)}) => `(rpexpr{$x})
| `(rpexpr{`($x)}) => `($x)
| `(rpexpr{c($x)}) => `(RawPExpr.const $x)

end PExpr
