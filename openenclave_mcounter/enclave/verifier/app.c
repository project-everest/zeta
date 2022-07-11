#include <ZetaFormatsApplicationTypes.h>
#include <Zeta_Steel_Main.h>
#include <Zeta_Steel_Main.c>

#include <App_val.h>
#include <New_counter_param.h>
#include <LowParse.h>
#include <App_key.h>
#include <Incr_counter_param.h>
#include <Slot.h>
#include <Get_counter_param.h>

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

#define _CHECK(x)                                                              \
  if (!(x)) {                                                                  \
    return (verify_runapp_result){.tag = Run_app_verify_failure, .wrote = 0};  \
  }

const app_key_t* _get_record_key (const record_t* record)
{
    return &(record->key.case_ApplicationKey);
}

const app_val_t* _get_record_val (const record_t* record)
{
    return &(record->value.case_DValue.v);
}

void _set_record_val (vthread_state_t *t, slot_t s, const app_val_t* val)
{
    Zeta_Steel_LogEntry_Types_value new_val = {
        .tag = Zeta_Steel_LogEntry_Types_DValue,
        .case_DValue = {
            .tag = FStar_Pervasives_Native_Some,
            .v = *val
        }
    };

    Zeta_Steel_Main_write_store (*t, s, new_val);
}

int _isnull (const record_t *record)
{
    return record->value.case_DValue.tag == FStar_Pervasives_Native_None;
}

int _isnonnull (const record_t *record)
{
    return !(_isnull(record));
}

verify_runapp_result new_counter
(
    uint8_t *_base, uint32_t _len,
    uint8_t *_out, uint32_t _out_len, uint32_t _out_offset,
    vthread_state_t *_t
)
{
    uint32_t wrote = 0;

    LowParse_Slice_slice _sl = { .base = _base, .len = _len };

    New_counter_param_new_counter_param _param = New_counter_param_new_counter_param_reader(_sl, 0);

    /* read the store entry corresponding to slot s_r */
    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv _e_r =
        Zeta_Steel_Main_read_store(*_t, _param.s_r);

    /* check: slot s_r is not empty */
    _CHECK(_e_r.tag != FStar_Pervasives_Native_None);

    /* check: slot contains app-key & val */
    _CHECK(_e_r.v.value.tag == Zeta_Steel_LogEntry_Types_DValue);


    App_key_app_key *k = &(_param.k);

    
    const app_key_t *pkey = _get_record_key(&(_e_r.v));
    app_val_t new_val = 0;

    /* we are operating on the correct record */
    _CHECK (*k == *pkey);

    /* the value of the key is null (counter for key k does not exist) */
    _CHECK (_isnull(&(_e_r.v)));

    /* update the value of the record */
    _set_record_val(_t, _param.s_r, &new_val);


    return (verify_runapp_result) { .tag = Run_app_success, .wrote = wrote };
}


verify_runapp_result incr_counter
(
    uint8_t *_base, uint32_t _len,
    uint8_t *_out, uint32_t _out_len, uint32_t _out_offset,
    vthread_state_t *_t
)
{
    uint32_t wrote = 0;

    LowParse_Slice_slice _sl = { .base = _base, .len = _len };

    Incr_counter_param_incr_counter_param _param = Incr_counter_param_incr_counter_param_reader(_sl, 0);

    /* read the store entry corresponding to slot s_r */
    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv _e_r =
        Zeta_Steel_Main_read_store(*_t, _param.s_r);

    /* check: slot s_r is not empty */
    _CHECK(_e_r.tag != FStar_Pervasives_Native_None);

    /* check: slot contains app-key & val */
    _CHECK(_e_r.v.value.tag == Zeta_Steel_LogEntry_Types_DValue);


    App_key_app_key *k = &(_param.k);

    
    const app_key_t *pkey = _get_record_key(&(_e_r.v));
    const app_val_t *prev_val = _get_record_val(&(_e_r.v));
    app_val_t new_val = *prev_val + 1;

    /* we are operating on the correct record */
    _CHECK (*k == *pkey);

    /* update the value of the record */
    _set_record_val(_t, _param.s_r, &new_val);

    /* output the previous value */
    wrote = App_val_app_val_lserializer (*prev_val, _out, _out_offset);
    _out_offset += wrote;


    return (verify_runapp_result) { .tag = Run_app_success, .wrote = wrote };
}


verify_runapp_result get_counter
(
    uint8_t *_base, uint32_t _len,
    uint8_t *_out, uint32_t _out_len, uint32_t _out_offset,
    vthread_state_t *_t
)
{
    uint32_t wrote = 0;

    LowParse_Slice_slice _sl = { .base = _base, .len = _len };

    Get_counter_param_get_counter_param _param = Get_counter_param_get_counter_param_reader(_sl, 0);

    /* read the store entry corresponding to slot s_r */
    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv _e_r =
        Zeta_Steel_Main_read_store(*_t, _param.s_r);

    /* check: slot s_r is not empty */
    _CHECK(_e_r.tag != FStar_Pervasives_Native_None);

    /* check: slot contains app-key & val */
    _CHECK(_e_r.v.value.tag == Zeta_Steel_LogEntry_Types_DValue);


    App_key_app_key *k = &(_param.k);

    
    const app_key_t *pkey = _get_record_key(&(_e_r.v));
    const app_val_t *prev_val = _get_record_val(&(_e_r.v));

    /* we are operating on the correct record */
    _CHECK (*k == *pkey);

    /* output the previous value */
    wrote = App_val_app_val_lserializer (*prev_val, _out, _out_offset);
    _out_offset += wrote;


    return (verify_runapp_result) { .tag = Run_app_success, .wrote = wrote };
}


verify_runapp_result
Zeta_Steel_Application_run_app_function(
  runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  Zeta_Steel_VerifierTypes_thread_state_t t
)
{
    uint8_t *log_param_base = log_array + pl_pos;

    switch (pl.fid) {

    case 0: return new_counter(log_param_base, pl.rest, out, out_len, out_offset, &t);

    case 1: return incr_counter(log_param_base, pl.rest, out, out_len, out_offset, &t);

    case 2: return get_counter(log_param_base, pl.rest, out, out_len, out_offset, &t);

    default:
        break;
    }

    return (verify_runapp_result)
    {
        .tag = Run_app_verify_failure,
        .wrote = 0
    };
}
