Getting prerequisites
=====================

OCaml setup
-----------

You must have a working OPAM. On Linux, install OPAM via your package manager,
run `opam init`, then follow the instructions to configure your environment.

To install all the required OPAM packages, we suggest checking out
https://github.com/project-everest/everest then running `./everest opam`, which
will take care of installing all the package we need.

Make sure you have added the OPAM bits to your `.bashrc` and that you have
reloaded your shell to have all the environment variables, or at least run
`$(eval opam env)`.

F\*
---

Binary package or from source.

Remember to export `FSTAR_HOME` in both cases!

KreMLin
-------

Checkout https://github.com/FStarLang/kremlin/ and run `make`. Remember to
export `KREMLIN_HOME`!

HACL\* OPAM package
-------------------

This is the OCaml bindings for the C EverCrypt library.

You will need a checkout of HACL\*, currently on branch `vdum_ctypes_evercrypt`,
hopefully regular `master` soon. In HACL\*:

```bash
$ cd hacl-star
$ make -j <reasonable-factor>
$ make -C dist/gcc-compatible/ install-hacl-raw
$ cd bindings/ocaml && dune install
```

You can confirm you have a correct setup by running `ocamlfind list`, which
should show both `hacl-star` and `hacl-star-raw`.
