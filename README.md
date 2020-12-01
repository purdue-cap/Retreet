# Retreet
Retreet is a framework in which one can describe general recursive tree traversals, precisely represent iterations, schedules and dependences, and automatically check data-race-freeness and transformation correctness. (Details can be found in the [paper](https://arxiv.org/abs/1910.09521).)

# Installation

## Dependencies
- MONA with version >= 1.4

## Compilation
1. Install MONA on your system.
- Here is the [link](https://www.brics.dk/mona/download.html) to download the source package of MONA. Follow the instructions inside the package.
- You can also get the git version by running `git clone https://github.com/cs-au-dk/MONA`
2. Compile the program
- `cd` to the project directory and run `make`

# Running

## Checking fusibility
```
./exec.sh fuse <path to unfused traversals file> <path to fused traversal file> <path to file of relationship between unfused and fused traversals>
mona <path to generated mona file>
```

## Checking data-race-freeness
```
./exec.sh parallel <path to traversals file>
mona <path to generated mona file>
```

## Some running examples
The running examples are tested on a server with a 40-core, 2.2GHz CPU and 128GB memory running Fedora 26.

- Checking fusibility of a pair of size-counting traversals. (indeed fusible)
```
./runtest.sh fuse size_counting_fusible
```
- Checking fusibility of a pair of size-counting traversals. (indeed infusible)
```
./runtest.sh fuse size_counting_infusible
```
- Checking fusibility of three CSS minification traversals. (indeed fusible)
```
./runtest.sh fuse css
```
- Checking fusibility of a cycletree routing algorithm. (indeed fusible)
```
./runtest.sh fuse cycletree
```
- Checking fusibility of List shift and sum traversals. (indeed fusible)
```
./runtest.sh fuse shiftsum
```
- Checking parallelizability of a pair of size-counting traversals. (No data-race)
```
./runtest.sh parallel size_counting
```
- Checking parallelizability of a cycletree routing algorithm. (Do have data-race)
```
./runtest.sh parallel cycletree
```