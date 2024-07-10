# $\tilde{r}(C_4, P_n)$
Program that finds upper bounds for online Ramsey numbers $\tilde{r} (C_4, P_n)$ for small values of n.

Detailed information about this program are presented in the following paper in Section 4 and Appendix A.

https://arxiv.org/abs/2211.12204

### Contents

The project contains five files:

- c4pn.cpp - source code,
- BuilderStrategies.zip - generated output,
- results.txt - values of rc function.
- verifier.py - additional verification using numpy and networkx
- verifieroutput.txt - output of the previous file

### How to run

1. Download the c4pn.cpp and verifier.py.
2. Compile c4pn.cpp with GNU C++ compiler (requires C++11 or newer). Program will create several files with strategies for Builder `C4P{n}_in_{e}_moves_{v}_verts.txt` (it will overwrite files if they previously existed).
3. Run verifier.py with python3 in the same folder as output files of c4pn.cpp. The verifier requires numpy and networkx.

The c4pn.cpp was tested on GCC 12.2.0 and the following commands were used.

`g++ -Wall -O2 -std=gnu++20  -c c4pn.cpp -o c4pn.o`

`g++  -o c4pn c4pn.o  -s`

The verifier.py was tested on Python 3.8.10 with numpy 1.21.5 and networkx 3.1 and the following command was used.

`python3 verifier.py
