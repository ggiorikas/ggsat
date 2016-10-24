## Description

A multithreaded DPLL SAT solver with a [HITS](https://en.wikipedia.org/wiki/HITS_algorithm) inspired static variable ordering heuristic.

## Compilation

On Linux, run `g++ -std=c++11 -O3 ggsat.cpp -lpthread -o ggsat`
  
On Windows, use Visual Studio and make sure you build with a Release config.

## Tests

First, get the relevant SATLIB benchmarks from [this page](http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).

Then, run `python test.py`

## License

MIT
