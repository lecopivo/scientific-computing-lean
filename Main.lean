import ScientificComputingInLean
import Verso.Genre.Manual

import DemoTextbook

open Verso.Genre.Manual

def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
  IO.println "Placeholder generator for output exercise and solution Lean code"


def main := manualMain (%doc ScientificComputingInLean) (extraSteps := [buildExercises])
                       (config := config)
                  -- (config := {extraJs:=["http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"]})
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/theme.css", "/static/inter/inter.css", "/static/firacode/fira_code.css", "/static/katex/katex.min.css"],
    extraJs := ["/static/katex/katex.min.js", "/static/math.js"]
    emitTeX := false
    emitHtmlSingle := false
  }
