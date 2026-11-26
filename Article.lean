import RKResearch.FiniteRootedTree
import RKResearch.OrderConditions
import VersoManual

open Verso.Genre Manual

#docs (Manual) article "Rooted trees and Runge–Kutta order conditions" :=
:::::::
{includeLiterate "." RKResearch.FiniteRootedTree "Finite rooted trees"}

{includeLiterate "." RKResearch.OrderConditions "Order conditions"}
:::::::

def main := manualMain article.toPart (config := {
  destination := ".lake/build/article"
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
})
