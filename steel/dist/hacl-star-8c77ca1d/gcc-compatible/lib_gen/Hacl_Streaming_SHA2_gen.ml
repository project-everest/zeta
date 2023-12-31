let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Streaming_SHA2_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Streaming_SHA2_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Streaming_SHA2_c_stubs.c"));
   Format.printf
     "#include \"Hacl_Streaming_SHA2.h\"\n#include \"internal/Hacl_Streaming_SHA2.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Streaming_SHA2_bindings.Bindings)