#include "krml_bridge.h"
#include "LowParse.h"
#include <New_p.h>

kb_new_p kb_new_p_reader(uint8_t *base, uint32_t len, uint32_t pos)
{
    LowParse_Slice_slice sl = {
        .base = base,
        .len = len
    };

    New_p_new_p new_param = New_p_new_p_reader(sl, pos);
    return (kb_new_p) { .k = new_param.k, .s = new_param.s };
}
