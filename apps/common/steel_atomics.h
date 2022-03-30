#pragma once

static inline bool Steel_ST_Reference_cas_u32(uint32_t *r, uint32_t v_old, uint32_t v_new)
{
    __sync_bool_compare_and_swap(r, v_old, v_new);
}
