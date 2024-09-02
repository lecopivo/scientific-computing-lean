import ScientificComputingInLean

import DemoTextbook

open Verso.Genre.Manual

def buildExercises (_ctxt : TraverseContext) (_state : TraverseState) : IO Unit :=
  IO.println "Placeholder generator for output exercise and solution Lean code"


def main := manualMain (%doc ScientificComputingInLean) (extraSteps := [buildExercises])
                       (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/theme.css", "/static/inter/inter.css", "/static/firacode/fira_code.css", "/static/katex/katex.min.css"],
    extraJs := ["/static/katex/katex.min.js", "/static/math.js", "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"]
    emitTeX := false
    emitHtmlSingle := false
  }
