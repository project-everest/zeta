""" Parse an app specification """

import app

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

def get_type_spec(spec_lines):

    # identify text containing type definitions.
    types_begin_idx = get_types_begin(spec_lines)
    types_end_idx = get_types_end(spec_lines)

    if types_begin_idx > types_end_idx:
        raise SyntaxError("@begin_types after @end_types")

    return spec_lines[types_begin_idx : types_end_idx]

def get_func_intervals(spec_lines):
    i = 0
    while i < len(spec_lines):

        if spec_lines[i] == '@begin_func':
            j = spec_lines.index('@end_func', i+1)
            yield (i,j)
            i = j+1
        else:
            i = i+1

def get_func_specs(spec_lines):
    for b,e in get_func_intervals(spec_lines):
        '\n'.join(spec_lines[b,e])

def parse_func(func_spec):
    pass
