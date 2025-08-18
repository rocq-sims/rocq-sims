# rocq-sims

This library defines various notions of simulation, and associated coinduction up-to principles,
including a novel mutually coinductive characterization of divergence-sensitive weak simulation.

The draft paper [*The Sims: A Family of Simulations for Verified Compilation*](https://www-verimag.imag.fr/~chappen/sims-draft-v1.pdf)
documents this library.

## Theories

Source files of our development are in `theories/`.

- `LTS.v` defines LTSs
- `Divergence.v` coinductively defines divergence and divergence preservation on LTSs
- `Sims.v` contains our parameterized definition of simulation (section 4), of which mudiv-simulation (section 3) is a particular case
- `SimExample.v` gives an example of a simulation proof (section 3.5).
- `DivSim.v` compares our definition with classical divergence-sensitive simulation
- `FreeSim.v` compares our definition with FreeSim
- `IndSim.v` compares our definition with (inductive-coinductive) normed simulation
- `UB.v` defines an LTS transformer to augment a transition system with undefined behaviors
- `LTSSum.v` defines the union of two LTSs and extends our transitivity result to simulation results on heterogeneous LTSs
- `CTree.v` instantiates our theory on CTrees (section 5)
- `IndSimCounterExample.v` contains an example of a simulation result that holds for mudiv-simulation but not for normed simulation

## Authors

- Nicolas Chappe

## License

This library is released under the GNU Lesser General Public License 3.0, or any later version.

## How to build

This development mainly depends on Rocq >= 8.19 and the `coinduction` library.
The CTree instantiation depends on the CTree library. This is a global dependency for now.

`opam install . --deps-only` builds the library, then `dune build` builds it.
