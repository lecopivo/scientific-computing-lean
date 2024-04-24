# Setting Up Lean and SciLean

This section will guide you through setting up Lean and SciLean on your machine.

First, you need to install Lean. You can find instructions on how to do this:
- simplest way is [using VSCode](https://lean-lang.org/lean4/doc/quickstart.html)
- through command line 
  1. [Install `elan`](https://github.com/leanprover/elan?tab=readme-ov-file#installation) the Lean toolchain installer
  2. Run `elan update` to get the latest stable version of Lean
  3. Set up your code editor: [VSCode](https://lean-lang.org/lean4/doc/quickstart.html), [Emacs](https://github.com/leanprover-community/lean4-mode) or [Neovim](https://github.com/Julian/lean.nvim/)

Download and build SciLean:
```
git clone http://github.com/lecopivo/SciLean
cd SciLean
lake exe cache get
lake build
```

This book's code can be found in the `SciLean/test/ScientificComputingInLean` directory.
