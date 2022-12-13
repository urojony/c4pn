# $\tilde{r}(C_4, P_n)$
Program that finds upper bounds for online Ramsey numbers $\tilde{r} (C_4, P_n)$ for small values of n.

Detailed information about this program are presented in the following paper in Section 4 and Appendix A.

https://arxiv.org/abs/2211.12204

### Contents

The project contains two files:

- c4pn.cpp - source code,
- builderstrategies.zip - generated output.

### How to run

Download the source code and compile it with GNU C++ compiler (requires C++11 or newer). Program will create several files with strategies for Builder `C4P{n}_in_{e}_moves_{v}_verts.txt` (it will overwrite files if they previously existed).

The program was tested on GCC 12.2.0 and the following commands were used.

`g++ -Wall -O2 -std=gnu++11  -c c4pn.cpp -o c4pn.o
g++  -o c4pn c4pn.o  -s  `
