module Veritas.Epoch
include Veritas.Formats.Types

assume val epoch_id : Type0

noeq
type epoch_hash_entry = {  
  t_id : thread_id;
  e_id : epoch_id;
  hadd : hash_value;
  hevict : hash_value;
}
