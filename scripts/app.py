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


class Param:
    def __init__ (self, tname, vname):
        self.tname = tname
        self.vname = vname

        if tname == 'app_record':
            self.tname_or_slot = 'slot'
            self.vname_or_slot = f's_{vname}'
            self.host_tname = 'Record'
        else:
            self.tname_or_slot = tname
            self.vname_or_slot = vname
            self.host_tname = get_everparse_type_c_name(tname)
        self.record_idx = None

    def set_record_idx (self, idx):
        self.record_idx = idx

    def is_record (self):
        return self.tname == 'app_record'

class StateFn:
    """
    A state transition function of the Zeta state machine.

    Attributes:
        name: name of the function
        params: non-record input parameters
    """
    def __init__ (self, id, name, params, output, body):
        self.id = id
        self.name = name
        self.params = params
        self.body = body
        self.output = output
        self.everparse_param_name = f'{name}_param'
        self.verifier_body = self.translate_function_body()
        self.name_title = name.title()
        self.has_output = (output != 'void')
        self.has_output_str = str(self.has_output).lower()
        self.has_output_indicator = f"_HAS_OUTPUT_{self.name_title}"
        if self.has_output:
            self.indicate_has_output = self.has_output_indicator
        else:
            self.indicate_has_output = f"_HAS_NO_OUTPUT_{self.name_title}"
        self.c_output_type = get_everparse_type_c_name(output)
        self.record_params = [p for p in self.params if p.is_record()]
        self.non_record_params = [ p for p in self.params if not p.is_record()]
        self.arity = len (self.record_params)
        self.everparse_param_c_name = get_everparse_type_c_name(self.everparse_param_name)

        for i,p in enumerate(self.record_params):
            p.set_record_idx(i)

    def c_param_list (self):
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

    def c_param_member_decl (self):
        code = ''
        for t,n in self.params:
            if t == 'app_record':
                code += f'''
        Record {n}_;'''
            else:
                code += f'''
        {get_everparse_type_c_name(t)} {n}_;'''
        return code

    def c_param_member_init (self):
        code = ''
        for t,n in self.params:
            code += f'''
    , {n}_ {{ *{n} }}'''
        return code

    def map_idx_record (self):
        code = ''
        rec_params = [ (t,n) for t,n in self.params if t == 'app_record' ]
        for i,(_,n) in enumerate(rec_params):
            code += f'''
    if (idx == {i}) return {n}_;
'''
        return code

    def get_function_header (self):
        return f'''verify_runapp_result {self.name}
(
    uint8_t *_base, uint32_t _len,
    uint8_t *_out, uint32_t _out_len, uint32_t _out_offset,
    vthread_state_t *_t
)'''


    def get_param_type (self):
        return get_everparse_type_c_name(self.everparse_param_name)

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

        s += f'}} {self.everparse_param_name};\n'

        return s

    def sub_id (self, code):
        p = re.compile(r'@id@')
        return p.sub(str(self.id), code)

    def sub_arity (self, code):
        p = re.compile(r'@arity@')
        return p.sub(str(self.arity()), code)

    def sub_has_output (self, code):
        p = re.compile(r'@has_output@')
        return p.sub(str(self.has_output()).lower(), code)

    def sub_name_title (self, code):
        p = re.compile(r'@name_title@')
        return p.sub(self.name_title(), code)

    def sub_indicate_has_output (self, code):
        p = re.compile(r'@indicate_has_output@')
        return p.sub(self.indicate_has_output(), code)

    def sub_has_output_indicator (self, code):
        p = re.compile(r'@has_output_indicator@')
        return p.sub(self.has_output_indicator(), code)

    def sub_c_param_list(self, code):
        p = re.compile('@c_param_list@')
        return p.sub(self.c_param_list(), code)

    def sub_c_output_type (self, code):
        p = re.compile(r'@c_output_type@')
        return p.sub(f'{self.c_output_type()}', code)

    def sub_c_param_member_decl (self, code):
        p = re.compile(r'@c_param_member_decl@')
        return p.sub(f'{self.c_param_member_decl()}', code)

    def sub_c_param_member_init (self, code):
        p = re.compile(r'@c_param_member_init@')
        return p.sub(f'{self.c_param_member_init()}', code)

    def sub_map_idx_record (self, code):
        p = re.compile(r'@map_idx_record@')
        return p.sub(f'{self.map_idx_record()}', code)

    def gen_host_decl (self):
        """
        Return a string C declaration of the class representing the function
        """
        tmp_file = get_template_dir() / 'statefn.h.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.sub_name_title(code)
            code = self.sub_has_output_indicator(code)
            code = self.sub_indicate_has_output(code)
            code = self.sub_c_param_list(code)
            code = self.sub_c_param_member_decl(code)
            code = self.sub_c_output_type (code)
            return code

    def gen_host_def (self):
        tmp_file = get_template_dir() / 'statefn.cpp.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.sub_id(code)
            code = self.sub_arity(code)
            code = self.sub_has_output(code)
            code = self.sub_name_title(code)
            code = self.sub_c_output_type (code)
            code = self.sub_c_param_member_init(code)
            code = self.sub_c_param_list(code)
            code = self.sub_map_idx_record(code)
            code = self.sub_has_output_indicator(code)
            code = self.sub_indicate_has_output(code)
        return code

class App:
    """
    A zeta application
    """
    def __init__ (self, name, type_defs, fn_defs):
        self.name = name
        self.type_defs = type_defs
        self.fn_defs = fn_defs
        self.everparse_headers = None
        self.everparse_key_typedef = None
        self.everparse_val_typedef = None
        self.fncount = len(fn_defs);
        self.max_arity = max ([ fn.arity for fn in fn_defs ])

    def set_everparse_headers (self, formats_dir):
        self.everparse_headers = formats_dir.glob('*.h')

    def set_everparse_key_typedef (self, formats_dir):
        app_key_h = formats_dir / 'App_key.h'
        p = re.compile(r'typedef.*App_key_app_key;', re.DOTALL)
        code = app_key_h.read_text()
        m = p.search(code)
        if m == None:
            raise ValueError(f'App_key typedef not found in {app_key_h}')
        self.everparse_key_typedef = m.group()

    def set_everparse_val_typedef (self, formats_dir):
        app_val_h = formats_dir / 'App_val.h'
        p = re.compile(r'typedef.*App_val_app_val;', re.DOTALL)
        code = app_val_h.read_text()
        m = p.search(code)
        if m == None:
            raise ValueError(f'App_val typedef not found in {app_val_h}')
        self.everparse_val_typedef = m.group()

    def write_verifier_code (self, file_path):
        with open(file_path, 'a') as f:
            for fn in self.fn_defs:
                f.write('\n\n')
                f.write(fn.gen_verifier_code())

    def statefn_host_decl (self):
        code = ''
        for fn in self.fn_defs:
            code += '\n\n'
            code += fn.gen_host_decl()
        return code

    def statefn_host_def (self):
        code = ''
        for fn in self.fn_defs:
            code += '\n\n'
            code += fn.gen_host_def()
        return code

    def get_fncount (self):
        return len(self.fn_defs)

    def get_max_arity(self):
        return max ([ fn.arity() for fn in self.fn_defs ])

    def sub_name (self, code):
        p = re.compile('@name@')
        return p.sub(self.name, code)

    def sub_statefn_host_decl (self, code):
        p = re.compile('@statefn_host_decl@')
        return p.sub(self.statefn_host_decl(), code)

    def sub_statefn_host_def (self, code):
        p = re.compile('@statefn_host_def@')
        return p.sub(self.statefn_host_def(), code)

    def sub_fncount (self, code):
        p = re.compile('@fncount@')
        return p.sub(str(self.get_fncount()), code)

    def sub_max_arity (self, code):
        p = re.compile(r'@max_arity@')
        return p.sub(str(self.get_max_arity()), code)

    def transform_text (self, text):
        text = self.sub_name(text)
        text = self.sub_statefn_host_def(text)
        text = self.sub_statefn_host_decl(text)
        text = self.sub_fncount(text)
        text = self.sub_max_arity(text)
        return text

    def write_host_decl (self, file_path):
        tmp_file = get_template_dir() / 'app.h.tmp'
        with open(tmp_file) as tf:
            code = tf.read()
            code = self.transform_text(code)
            with open(file_path, 'w') as out_file:
                out_file.write(code)

    def write_host_def (self, file_path):
        tmp_file= get_template_dir() / 'app.cpp.tmp'
        with open (tmp_file) as tf:
            code = tf.read()
            code = self.transform_text(code)
            with open(file_path, 'w') as out_file:
                out_file.write(code)
