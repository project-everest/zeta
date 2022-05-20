#include <ZetaFormatsApplicationTypes.h>
#include <Zeta_Steel_Main.h>
#include <Zeta_Steel_Main.c>

/* shorter name for thread state */
typedef Zeta_Steel_VerifierTypes_thread_state_t vthread_state_t;

/* shorter name for verifier record */
typedef Zeta_Steel_VerifierTypes_kv record_t;

bool
Zeta_Steel_ApplicationTypes_eq_value_type(
  app_val_t v0,
  app_val_t v1
)
{
    /* TODO: Implement equality  */
    return v0 == v1;
}

extern void
Hacl_Blake2b_32_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *_dummy
);

Zeta_Steel_KeyUtils_raw_key
Zeta_Steel_Application_key_type_to_base_key(app_key_t k)
{
    uint8_t buf[4096];
    uint8_t hbuf[32];

    uint32_t n = App_key_app_key_lserializer(k, buf, 0);
    Hacl_Blake2b_32_blake2b(32, hbuf, n, buf, 0, 0);

    Zeta_Steel_KeyUtils_raw_key bk =
    {
        .significant_digits = 256,
        .k = read_hash_u256(hbuf)
    };

    return bk;
}

const app_key_t* get_record_key (const record_t* record)
{
    return &(record.key.case_ApplicationKey);
}

const app_val_t* get_record_val (const record_t* record)
{
    return &(record.value.case_DValue.v);
}
