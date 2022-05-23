""" Classes related to a Zeta application """

import re

def translate_check_statements (code):
    p = re.compile(r'_check')
    return p.sub('_CHECK', code)

def translate_key_calls (code):
    p = re.compile(r'_key\s*\(\s*(\w+)\s*\)')
    return p.sub(r'_get_record_key(&(_e_\1.v))', code)

def translate_val_calls (code):
    p = re.compile(r'_val\s*\(\s*(\w+)\s*\)')
    return p.sub(r'_get_record_val(&(_e_\1.v))', code)

def translate_set_val_calls (code):
    p = re.compile(r'_setvalue\s*\(\s*(\w+)\s*,\s*(\w+)\s*\)')
    return p.sub(r'_set_record_val(_t, _param.s_\1, &\2)', code)

def translate_is_null_calls (code):
    p = re.compile(r'_isnull\s*\(\s*(\w+)\s*\)')
    return p.sub(r'_isnull(&(_e_\1.v))', code)

def translate_output_match (match_obj):
    type_name = match_obj.group('name')
    serializer = f'{type_name}_{type_name}_lserializer'.capitalize()
    val = match_obj.group('val')
    return f'''wrote = {serializer} ({val}, _out, _out_offset);
    _out_offset += wrote'''

def translate_output(code):
    p = re.compile(r'_output_(?P<name>\w+)\s*\(\s*(?P<val>[\w\*]+)\s*\)')
    return re.sub(p, translate_output_match, code)

class StateFn:
    """
    A state transition function of the Zeta state machine.

    Attributes:
        name: name of the function
        params: non-record input parameters
    """
    def __init__ (self, name, params, output, body):
        self.name = name
        self.params = params
        self.body = body
        self.output = output

    def get_function_header (self):
        return f'''verify_runapp_result {self.name}
(
    uint8_t *_base, uint32_t _len,
    uint8_t *_out, uint32_t _out_len, uint32_t _out_offset,
    vthread_state_t *_t
)'''

    def everparse_param_name (self):
        return f"{self.name}_param"

    def get_param_type (self):
        param_name = self.everparse_param_name()
        type_name = f'{param_name}_{param_name}'
        return type_name.capitalize()

    def get_record_param_prefix (self, r):
        c = f'''
    uint32_t wrote = 0;

    /* read the store entry corresponding to slot s_{r} */
    FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv _e_{r} =
        Zeta_Steel_Main_read_store(*_t, _param.s_{r});

    /* check: slot s_{r} is not empty */
    _CHECK(_e_{r}.tag != FStar_Pervasives_Native_None);

    /* check: slot contains app-key & val */
    _CHECK(_e_{r}.v.value.tag == Zeta_Steel_LogEntry_Types_DValue);'''

        return c

    def get_function_prefix (self):
        c = f'''LowParse_Slice_slice _sl = {{ .base = _base, .len = _len }};

    {self.get_param_type()} _param = {self.get_param_type()}_reader (_sl, 0);'''

        for t,n in self.params:
            if t == 'app_record':
                c += '\n'
                c += self.get_record_param_prefix(n)

        return c

    def get_function_postfix (self):
        return f'''return (verify_runapp_result) {{ .tag = Run_app_success, .wrote = wrote }};'''

    def translate_function_body(self):
        b = translate_check_statements(self.body)
        b = translate_key_calls(b)
        b = translate_val_calls(b)
        b = translate_set_val_calls(b)
        b = translate_is_null_calls(b)
        b = translate_output(b)
        return b

    def gen_verifier_code (self):
        """
        Return a string C definition of the function
        """
        return f'''{self.get_function_header()}
{{
    {self.get_function_prefix()}

    {self.translate_function_body()}

    {self.get_function_postfix()}
}}
        '''

    def gen_everparse_param_type (self):
        """
        Return a string that represents the parameter type of the function in everparse
        """
        s = "struct {\n"

        for (t,n) in self.params:
            # Transform app_record parameters to slot params
            if t == 'app_record':
                t = 'slot'
                n = f's_{n}'

            s += f'  {t} {n};\n'

        s += f'}} {self.everparse_param_name()};\n'

        return s

    def gen_host_decl (self):
        """
        Return a string C declaration of the class representing the function
        """
        pass

    def gen_host_def (self):
        pass

class App:
    """
    A zeta application
    """
    def __init__ (self, name, type_defs, fn_defs):

        self.name = name
        self.type_defs = type_defs
        self.fn_defs = fn_defs

    def write_verifier_code (self, file_path):
        with open(file_path, 'a') as f:
            for fn in self.fn_defs:
                f.write('\n\n')
                f.write(fn.gen_verifier_code())

def gen_everparse_types (app):
    """
    Generate the text with everparse definitions for the app
    """

    # carry over the type definitions specified in the app
    s = '/* Application specified types */\n'
    s += app.type_defs + "\n"

    # add the type definition for a slot
    s += '/* Slot type */\n'
    s += 'uint16 slot;\n\n'

    # add type defs for state transition functions
    s += '/* Application state transition function parameter types */\n'
    for f in app.fn_defs:
        s += f.gen_everparse_param_type() + '\n'
    return s
