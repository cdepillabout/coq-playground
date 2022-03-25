<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Playground for Coq Code

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]

[docker-action-shield]: https://github.com/cdepillabout/coq-playground/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/cdepillabout/coq-playground/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/cdepillabout/coq-playground/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/cdepillabout/coq-playground/actions?query=workflow:"Nix%20CI"




This repo is just a collection of unrelated Coq code.  This is mostly a
dumping ground of various things I'm playing around with.

## Meta

- Author(s):
  - Dennis Gosnell (initial)
- License: [BSD 3-Clause "New" or "Revised" License](LICENSE)
- Compatible Coq versions: 8.13 or later
- Additional dependencies: none
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Playground for Coq Code
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coq-playground
```

To instead build and install manually, do:

``` shell
git clone https://github.com/cdepillabout/coq-playground.git
cd coq-playground
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

### Building

If you're using Nix, you can get into a shell with Coq available by running
`nix develop`:

```console
$ nix develop
```

You can build all the Coq files in this repo with `make`:

```console
$ make
```

After building, you can open up any of the files in
[`theories/`](./theories/) in `coqide` in order to work through the proofs.

You can regenerate the files in this repo (like `README.md`) from the
[`meta.yml`](./meta.yml) file by cloning
[`coq-community/templates`](https://github.com/coq-community/templates) and
running `generate.sh`:

```console
$ /some/path/to/coq-community/templates/generate.sh
```

You can also generate HTML documentation with `coqdoc`:

```console
$ make html
```
