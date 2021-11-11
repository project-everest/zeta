In rough dependence order

### Zeta.Steel.Parser

Tahina owns.

It represents a kind of minimalistic port of LowParse

### Zeta.ApplicationTypes.fsti

The main spec-level interface to be defined by the application. It's
opened by nearly all other modules.

### Zeta.Steel.FormatsManual

Tahina owns.

It sets the log format. Probably to be replaced with an auto-generated one.

It also provides signatures for some parsers and serializers of app
and stamped records. These could be moved somewhere else

### Zeta.Steel.KeyUtils

Some simple utilities on internal keys

### Zeta.Steel.ThreadStateModel

Nik and Arvind share this one.

The main specification of a Steel verifier thread.

Defines the `thread_state_model` type.

### Zeta.Steel.Correctness

Arvind owns.

It related ThreadStateModel to Zeta.Intermediate.Verifier and provides
the main semantic correctness lemma.

### Zeta.Steel.VerifierTypes

Defines the concrete type of a verifier's thread state,
`thread_state_t`

And an invariant on that state `thread_state_inv`.

And a selector that allows reading a `thread_state_t` as a
`thread_state_model` for specification.

### Zeta.Steel.Application.fsti

Defines the signature of `run_app_function`, which must be implemented
by an application instance. The spec relates it to
ThreadStateModel.run_app.

### Zeta.Steel.AggregateEpochHashes.fsti

Defines the type `aggregate_epoch_hashes` and an invariant associated
with it. It type is a record that holds a reference to the global
epoch hashes and max_certified epoch. Both are protected by a single
lock.

### Zeta.Steel.Verifier.fsti

Nik own this one.

The Steel implementation of a verifier thread. Its main function is
`verify_entries`, which takes an input log, and output array, an
aggregate_epoch_hashes, and verifies it according the to spec given in
ThreadStateModel.

### Zeta.Steel.Main.fsti

Aseem owns this one.

The top-level interface, providing `verify_entries` and `max_certified_epoch`


### Other files

HashAccumulator + some files in `to_be_restored` are kind of leaves in
the develpoment.
