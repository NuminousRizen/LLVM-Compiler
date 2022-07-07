# LLVM-Compiler
A LLVM-IR Compiler written in Scala.

The compiler consists of a `Regular Expression` matcher (based on the Brzozowski method).

The compiler's `lexing` phase is based on the Sulzmann & Lu method.

The compiler also consists of a `parser` (implemented with parser combinators) for the (made up) functional language FUN.

Finally the actual `compiler` compiles the source code for the (made up) functional language FUN for the LLVM-IR through an internal intermediate CPS language.

---

I used Scala version 2.13.6 with Java 11, Ammonite version 2.4.0 and LLVM version 10.0.0 .

You are free to use my compiler as you wish; I cannot guarantee that this code will work on any version, so I recommend that you use the same versions that I did.
