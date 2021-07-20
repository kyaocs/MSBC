# Computing Maximum Structural Balanced Cliques in Signed Graphs

This project aims to detect the maximum strucutral balanced clique (MSBC) and the polarization factor (PF) in signed graphs.

MSBC is the executable, and is compiled on Ubuntu 18.04.5, with -O3 optimization.

bitcoin.txt is an example signed graph from [SNAP](https://snap.stanford.edu/data/soc-sign-bitcoin-otc.html)

## Running Format

./MSBC [1]input_graph [2]MSBC/Mtau/Mtau_bi [3]tau (optional)

**Running example for maximum structural balanced clique detection**

./MSBC ./bitcoin.txt MSBC 3

**Running example for polarization factor detection**

./MSBC ./bitcoin.txt Mtau

### Note

For MSBC detection, tau must be specified, which has been set as 3 by default.

For PF detection, tau is not needed.

## Graph Format

number of vertices \t number of edges \n

v0 \t v1 \t sign \n

v0 \t v2 \t sign \n

...

Note that each edge is stored twice and ordered here.
