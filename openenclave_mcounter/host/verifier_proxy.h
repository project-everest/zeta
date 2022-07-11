#pragma once

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

    void verifier_init(const char *type, uint32_t flags);

    int verifier_verify_log (uint8_t threadId,
                             uint8_t *inp,
                             size_t inpLen,
                             uint8_t *out,
                             size_t outBufSize,
                             size_t *outLen);

#ifdef __cplusplus
}
#endif
