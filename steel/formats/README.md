* qd/Zeta.Formats.Aux.rfc Contains the qd format of types used by Zeta

  To rebuild, you need a build of EverParse
    - `make quackyducky lowparse -jN` in everparse
    - this should give you the qd executable and lowparse checked files

  Set EVERPARSE_HOME to the working copy of EverParse
  
  Then, `make qd -jN` in this directory (steel/formats)
  
    - this will produce the parsers and serializers, both spec and
      Low*, for the formats in the rfc

    - Note, you can add OTHERFLAGS='--admit_smt_queries true' if
      you're in a hurry and not building a final artifact
    
* To expose a parser and/or serializer for a type in the rfc

  1. In $ZETA_HOME/steel/Zeta.Steel.LogEntry.Spec.fsti

     Give the signatures for the parser and serializer spec

  2. In $ZETA_HOME/steel/Zeta.Steel.LogEntry.fsti

     Give the signature in Steel of the Low* implementation.
     
     The name needs to be prefixed with `zeta__` because the
     declaration in the Steel interface has to match the name in the
     Low* implementation and both are extracted with -no_prefix by
     Karamel.

     e.g., see zeta__serialize_stamped_record

     We usually also include a wrapper without the zeta__ prefix, for
     convenience of calling from Zeta.

  3. Then, in the $ZETA_HOME/steel/formats/spec directory, edit
     Zeta.Steel.LogEntry.Spec.fst, providing definitions for the
     signatures assumed in the corresponding .fsti in step 1

  4. Compile the spec directory using `make spec`

  5. Then in $ZETA_HOME/steel/formats/lowstar/Zeta.LowStar.LogEntry.fsti

     Add Low* signatures corresponding to the ones given in step 2
     above. The parser and serializer types from Zeta.LowStar.Parser
     are the Low* equivalent to the ones in Zeta.Steel.Parser

  6. Then in $ZETA_HOME/steel/formats/lowstar/Zeta.LowStar.LogEntry.fst

     Provide a Low* impl of the signatures given in 5 (using the
     LowParse.Low combinators)

  7. Then, do a `make` in $ZETA_HOME/steel/formats and that should
     verify and extract everything


Note, see 64bf46274222634766a595a6a34a4c1957a4a090 for an example
addition of a timestamp serializer
  
     


  