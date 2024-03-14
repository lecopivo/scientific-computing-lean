# Introduction


## Why Lean for Scientific Computing?

If your job involves writing scientific computing software and you're a satisfied user of Python, Julia, R, Matlab, or C/C++, the idea of using Lean, an interactive theorem prover and dependently typed programming language, might seem completely bizarre. Lean is often advertised as a tool that allows you to write programs and prove their correctness, thus completely eliminating bugs. However, the sad truth is that proving the correctness of programs is still very challenging and can feel like an unnecessary hassle. This is especially true in scientific computing, where your primary concern is often whether you've chosen the right model to describe the real world, rather than worrying about minor bugs in your program.


If you write scientific computing software, you mainly require two things from your programming language: ease of use and performance. High-level programming languages like Python, Julia, R, or Matlab are popular for their ease of use, while languages like C/C++ or Fortran are used when you need maximum performance. Julia is somewhat unique among these languages, as it addresses both of these goals. It is often referred to as "solving the two-language problem," in contrast to languages like Python, which are essentially glue code between highly optimized C libraries.


Similar to Julia, the goal of SciLean is to provide a high-level programming language that is also performant for scientific computing. Because Lean is dependently types language and interactive theorem prover it offers completely new opportunities in terms of ease of use and has the potential to reimagine how we write scientific computing software.


### The Role of Dependent Types?

The main feature of Lean is that it is dependently type language, which allows you to prove mathematical statements or the correctness of programs. While this may not seem very relevant for scientific computing but the ability to formally state what a program is supposed to do is extremely useful. As a library author, you can formally state what your library does, and as a user, you know exactly what to expect. This guarantees that different libraries can be used together without issues and makes refactoring large codebases less painful.

  In a way, this is taking typed programming languages to the next level and the difficulties shares some similarities with the types vs untyped language debate. Typed programming languages gained a bad reputation early on for being bureaucratic, requiring types to be written everywhere and this led to the popularity of untyped programming languages. However, in modern typed programming languages, this bureaucracy is mostly gone and for building and maintaining large-scale libraries, the benefits of types outweigh the downsides.
  
  Dependently typed languages are currently stuck in this bureaucratic stage, similar to where typed languages were in the past. The key point is that while writing proofs can be very tedious, stating properties of programs is not. The goal of *SciLean* is to provide a useful library for scientific computing with precisely defined specifications. Only once the library gains popularity and reaches a certain level of stability can we go back and truly prove its full correctness.
  
  The decision to use Lean over any other dependently typed language is largely due to the existence of a vast library of formalized mathematics *Mathlib*, supported by a large and enthusiastic community. Scientific software is typically math-heavy, and it can leverage *Mathlib* to precisely specify the programs we write. A notable example of this is automatic differentiation in *SciLean*, which utilizes *Mathlib*'s theorems about differentiation to provide automatic/symbolic differentiation that is guaranteed to be correct.

### Benefits of Interactivity

Lean is primarily known as an interactive theorem prover, allowing you to state mathematical statements and iteratively prove them. In your code editor, you can view the goal statement you want to prove and a list of statements you already know to be true. Lean provides a set of tactics that combine known facts to simplify the goal statement until you reach a statement that is trivially true. While this interactive proving may not be directly relevant to scientific computing, the infrastructure enabling it is quite interesting. We will demonstrate how this infrastructure allows us to build an interactive computer algebra system and an interactive compiler/optimizer, which are highly relevant to scientific computing.

Traditionally, there has been a clear divide between languages focusing on symbolic computations (like Mathematica, Maple, etc.) and numerical computation (like Python, Julia, etc.). The latter often provide libraries for symbolic computations, but there is still a clear division between symbolic code and normal code. In Lean, any piece of code can be treated symbolically, and Lean's interactivity allows you to effectively open an interactive notebook at any point where you can perform symbolic manipulations on your code and paste it back to your source code. Later, we will demonstrate how this approach can be taken to an extreme where you write programs that are purely symbolic and then turn them into executable programs through a series of symbolic manipulations.


One of the challenges with high-level programming languages is that they heavily rely on compiler optimizations to achieve performant code. However, when these automatic optimizations fail, understanding what went wrong can be quite difficult. An interesting approach to this problem is called "program scheduling", where you initially write your programs in a straightforward manner and then transform them using a series of commands to a more efficient form. A notable example of this is the domain-specific programming language *Halide*, which allows you to write high-performance image processing code in this manner.

By leveraging Lean's interactivity, we can build a similar system where you write your program in a simple way and then interactively rewrite it to a more efficient form. An additional benefit of using Lean is that you can also obtain a proof that you haven't changed the meaning of the program.
