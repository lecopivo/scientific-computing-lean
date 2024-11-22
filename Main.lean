import ScientificComputingInLean
-- import VersoManual

-- import DemoTextbook

open Verso.Genre.Manual


def main := manualMain (%doc ScientificComputingInLean)
                       (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/colors.css",
                 "/static/theme.css",
                 "/static/print.css",
                 "/static/fonts/source-serif/source-serif-text.css",
                 "/static/fonts/source-code-pro/source-code-pro.css",
                 "/static/katex/katex.min.css"],
    extraJs := ["/static/katex/katex.min.js",
                "/static/math.js",
                "/static/print.js",
                "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"],
    emitTeX := false,
    emitHtmlSingle := false, -- for proofreading
    logo := some "/static/lean_logo.svg",
    -- sourceLink := some "https://github.com/leanprover/reference-manual",
    -- issueLink := some "https://github.com/leanprover/reference-manual/issues"
  }
