# This repository contains Dafny programs developed for the DAIMPL Seminar . It serves as a collection of verified examples, exercises, and formal proofs implemented in Dafny, demonstrating formal verification techniques using specifications and automated reasoning.

Environment Setup 
 1. Install Dafny Use Visual Studio Code (VS Code) as your development environment and install the official Dafny extension. 
 Dafny Website: https://dafny.org/ 
 Installation Guide: https://dafny.org/latest/Installation 
 Steps: 
   1 Open VS Code 
   2 Go to the Extensions panel 
   3 Search for “Dafny” and install the official extension 
   4 Once installed, VS Code will automatically recognize `.dfy` files and provide verification and execution support

2. Install the Z3 SMT Solver Dafny uses the Z3 theorem prover as its backend verification engine.
 Z3 Repository: https://github.com/Z3Prover/z3

To verify a Dafny program: 
  1 Open any `.dfy` file in VS Code 
  2 Run the command “Dafny: Verify” via Ctrl + Shift + P 
  3 Or simply save the file — Dafny can verify automatically on save (if enabled) 
  Success: a green check mark appears at the bottom of VS Code 
  Failure: error messages and locations are shown in the Problems panel