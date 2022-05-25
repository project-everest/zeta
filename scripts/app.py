""" Classes related to a Zeta application """

import re
from paths import *

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

def get_everparse_type_c_name(t):
    if t == 'uint64':
        return 'uint64_t'
    return f'{t}_{t}'.capitalize()

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

    def has_output(self):
        return self.output != 'void'

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
        return get_everparse_type_c_name(self.everparse_param_name())

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

    def get_param_prefix (self, t, n):
        return f'    {get_everparse_type_c_name(t)} *{n} = &(_param.{n});'

    def get_function_prefix (self):
        c = f'''LowParse_Slice_slice _sl = {{ .base = _base, .len = _len }};

    {self.get_param_type()} _param = {self.get_param_type()}_reader (_sl, 0);'''

        for t,n in self.params:
            c += '\n'
            if t == 'app_record':
                c += self.get_record_param_prefix(n)
            else:
                c += self.get_param_prefix(t,n)
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

    def get_host_class_name (self):
        return self.name.title()

    def sub_name (self, code):
        p = re.compile(r'@name@')
        return p.sub(self.get_host_class_name(), code)

    def get_host_class_constr_param (self):
        code = ''
        for t,n in self.params:
            if code != '':
                # non-first argument
                code += f''',
            '''
            if t == 'app_record':
                code += f'''const Record* {n}'''
            else:
                code += f'''const {get_everparse_type_c_name(t)}* {n}'''
        return code

    def get_host_param_member_decl (self):
        code = ''
        for t,n in self.params:
            if t == 'app_record':
                code += f'''
        Record {n}_;'''
            else:
                code += f'''
        {get_everparse_type_c_name(t)} {n}_;'''
        return code

    def sub_constr_param(self, code):
        p = re.compile('@const_param@')
        return p.sub(self.get_host_class_constr_param(), code)

    def get_host_class_constr_decl (self):
        tmp_file = get_template_dir() / 'statefn_constr.h.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.sub_name(code)
            code = self.sub_constr_param(code)
            return code

    def sub_constructor_decl (self, code):
        p = re.compile(r'@constructor@')
        return p.sub(self.get_host_class_constr_decl(), code)

    def suppress_output_code_decl (self, code):
        p = re.compile(r'@if_output@.*?@end_if_output@', re.DOTALL)
        return p.sub('', code)

    def remove_if_output_decl (self, code):
        p = re.compile(r'@if_output@(.*?)@end_if_output@', re.DOTALL)
        return p.sub(r'\1', code)

    def sub_output_type_decl (self, code):
        p = re.compile(r'@output_type@')
        return p.sub(f'{get_everparse_type_c_name(self.output)}', code)

    def sub_param_member_decl (self, code):
        p = re.compile(r'@param@')
        return p.sub(f'{self.get_host_param_member_decl()}', code)

    def gen_host_decl (self):
        """
        Return a string C declaration of the class representing the function
        """
        tmp_file = get_template_dir() / 'statefn.h.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.sub_name(code)
            code = self.sub_constructor_decl(code)
            code = self.sub_param_member_decl(code)
            if self.has_output():
                code = self.sub_output_type_decl(code)
                code = self.remove_if_output_decl(code)
            else:
                code = self.suppress_output_code_decl(code)
            return code

    def gen_host_def (self):
        return 'TBD'

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

    def sub_name (self, code):
        p = re.compile('@app@')
        return p.sub(self.name, code)

    def get_statefn_host_decl (self):
        code = ''
        for fn in self.fn_defs:
            code += '\n\n'
            code += fn.gen_host_decl()
        return code

    def sub_host_statefn_decl (self, code):
        p = re.compile('@app_statefn@')
        return p.sub(self.get_statefn_host_decl(), code)

    def write_host_decl (self, file_path):
        tmp_file = get_template_dir() / 'app.h.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.sub_name(code)
            code = self.sub_host_statefn_decl(code)
            with open(file_path, 'w') as out_file:
                out_file.write(code)

    def get_statefn_host_def (self):
        code = ''
        for fn in self.fn_defs:
            code += '\n\n'
            code += fn.gen_host_def()
        return code

    def sub_statefn_host_def (self, code):
        p = re.compile('@app_statefn@')
        return p.sub(self.get_statefn_host_def(), code)

    def write_host_def (self, file_path):
        tmp_file= get_template_dir() / 'app.cpp.tmp'
        with open (tmp_file) as tf:
            code = tf.read()
            code = self.sub_name(code)
            code = self.sub_statefn_host_def(code)
            with open(file_path, 'w') as out_file:
                out_file.write(code)

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
