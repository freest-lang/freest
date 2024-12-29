# The FreeST programming language

FreeST is a typed concurrent programming language where processes communicate via message-passing. Learn more at [freest-lang.github.io](https://freest-lang.github.io/).

# Build
For now, use the Haskell tool [Stack](https://docs.haskellstack.org/en/stable/).

To build FreeST, run the following command on the root of this project.
```
stack build
```
This will install (and build) GHC and all the project dependencies on an isolated location.

If you want to use the `freest` compiler as a command line program, you need to install it. Just run the following command.
```
stack install
```

# Run
To run (?) a FreeST program through stack (without the executable installed), just run the following command from the root of the project.
```
stack run PATH
```
Where `PATH` is the path to a FreeST file. A FreeST file should have the same name as the module it defines, and have extension `.fst`.

Try running one of the programs found in the valid program test suite:
```
stack run freest/test/prog/valid/functional/Fact/Fact.fst
```

If you have the executable installed, you can skip `stack` and run the following command anywhere.
```
freest PATH
```

# Test
We have several test suites. The general command is
```
stack test TARGET
```
Where `TARGET` may be
* `:unit`, to run the unit tests
* `:prog`, to run the program tests

## Test arguments
To pass arguments to the test suite through stack, use the `--ta ARGS` (`--test-arguments ARGS`) option, where `ARGS` is a quote-enclosed string containing the command line arguments to be passed. 

For HSpec suites (`:unit` and `:prog`), see the available options [here](https://hspec.github.io/options.html). A typical scenario is filtering which tests to run. This can be done with the `-m PATTERN` (`--match=PATTERN`) option, where `PATTERN` is the string that the tests to be run should match. The match can occur in any part of the path to the test. 

For example, to run only valid program tests, use
```
stack test :prog --ta "-m Valid"
```
To run a test named `Foo`, use
```
stack test :prog --ta "-m Foo"
```
