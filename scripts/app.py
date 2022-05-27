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

    def translate_function_body(self):
        b = translate_check_statements(self.body)
        b = translate_key_calls(b)
        b = translate_val_calls(b)
        b = translate_set_val_calls(b)
        b = translate_is_null_calls(b)
        b = translate_output(b)
        return b

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
