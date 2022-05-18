""" Parse an app specification """

import app
import re

def get_types_begin(spec_lines):
    try:
        return spec_lines.index('@begin_types')
    except ValueError:
        raise SyntaxError("@begin_types not found")

def get_types_end(spec_lines):
    try:
        return spec_lines.index('@end_types')
    except ValueError:
        raise SyntaxError("@end_types not found")

def get_type_defs(spec_lines):

    # identify text containing type definitions.
    types_begin_idx = get_types_begin(spec_lines)
    types_end_idx = get_types_end(spec_lines)

    if types_begin_idx > types_end_idx:
        raise SyntaxError("@begin_types after @end_types")

    return '\n'.join(spec_lines[types_begin_idx : types_end_idx])

def get_func_intervals(spec_lines):
    i = 0
    while i < len(spec_lines):

        if spec_lines[i] == '@begin_function':
            j = spec_lines.index('@end_function', i+1)
            yield (i,j)
            i = j+1
        else:
            i = i+1

def get_func_specs(spec_lines):
    for b,e in get_func_intervals(spec_lines):
        yield '\n'.join(spec_lines[b,e])

def parse_func_param (spec):
    tokens = spec.split()

    if len(tokens) != 2:
        raise SyntaxError("invalid function parameter: " + spec)

    return tokens[0], tokens[1]

def parse_func_params (params_spec):
    return [ parse_func_param(x) for x in params_spec.split(',')]

def parse_func(func_spec):
    fn_regex_pat = r'\s*(\w+)\s+(\w+)\s*\(([^)]*)\)\s*\{(.*)\}'
    fn_regex = re.compile(fn_regex_pat, re.DOTALL)
    m = fn_regex.match(func_spec)

    if m == None:
        raise SyntaxError("syntax error in function: " + func_spec)

    try:
        # Output type of the function
        out_t = m.group(1)

        # Name of the function
        name = m.group(2)

        # params list
        params = parse_func_params(m.group(3))

        # body of the function
        body = m.group(4)

        return app.StateFn(name, params, out_t, body)

    except IndexError:
        raise SyntaxError("syntax error in function: " + func_spec)

def parse_app (name, spec):

    spec_lines = spec.split('\n')

    # remove trailing whitespace
    spec_lines = [ l.rstrip() for l in spec_lines ]

    type_defs = get_type_defs(spec_lines)
    fn_defs = list(parse_func(fspec) for fspec in get_func_specs (spec_lines))
    return app.App(name, type_defs, fn_defs)
