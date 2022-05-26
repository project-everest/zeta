""" Parse an app specification """

import app
import re

def is_separator(line):
    """
    is line a separator (begins with //---)
    """
    line = line.lstrip()
    return line[:5] == '//---'

# enumerate indexes of separators
def separator_indexes(spec_lines):
    i = 0
    while i < len(spec_lines):
        if is_separator(spec_lines[i]):
            yield i
        i += 1

# index of the first separator
def first_separator_index(spec_lines):
    return next(separator_indexes(spec_lines))

def get_type_defs(spec_lines):
    """
    return the text containing the type definitions
    """
    return '\n'.join(spec_lines[ : first_separator_index(spec_lines)])

def get_func_intervals(spec_lines):
    sep_idxs = list(separator_indexes(spec_lines))
    prev = 0

    for i in sep_idxs:
        if prev > 0:
            yield (prev+1, i)
        prev = i
    yield (prev+1, len(spec_lines))

def get_func_specs(spec_lines):
    for b,e in get_func_intervals(spec_lines):
        yield '\n'.join(spec_lines[b:e])

# int *k; int * k; int* k
def parse_func_param (spec):
    param_pat = r'''
      \s*
      (?P<type>\w+)             # int
      (?P<sp1>\s*)
      (\*)?                     # *
      (?P<sp2>\s*)
      (?P<var>\w+)              # k
    '''
    param_regex = re.compile(param_pat, re.DOTALL | re.VERBOSE)
    m = param_regex.match(spec)
    if m == None:
        raise SyntaxError("invalid function parameter: " + spec)

    if m.group('sp1') == '' and m.group('sp2') == '':
        raise SyntaxError("invalid function parameter: " + spec)

    return m.group('type'), m.group('var')

def parse_func_params (params_spec):
    return [ parse_func_param(x) for x in params_spec.split(',')]

def parse_func(id, func_spec):
    fn_regex_pat = r'''
      \s*
      (?P<comment>/\*            # /*
        .*                       # comment body
      \*/)?                      # /*
      \s*
      (?P<out>\w+)               # void
      \s+
      (?P<name>\w+)              # foo
      \s*
      \(                         # (
      (?P<param>[^)]*)           # int x, int y, ...
      \)                         # )
      \s*
      \{                         # {
      (?P<body>.*)               # printf ("Hello World\n");
      \}                         # }
      '''
    fn_regex = re.compile(fn_regex_pat, re.DOTALL | re.VERBOSE)
    m = fn_regex.match(func_spec)

    if m == None:
        raise SyntaxError("syntax error in function: " + func_spec)

    try:
        # Output type of the function
        out_t = m.group('out')

        # Name of the function
        name = m.group('name')

        # params list
        params = parse_func_params(m.group('param'))

        # body of the function
        body = m.group('body')

        return app.StateFn(id, name, params, out_t, body)

    except IndexError:
        raise SyntaxError("syntax error in function: " + func_spec)

def parse_app (name, spec_lines):
    # remove trailing whitespace
    spec_lines = [ l.rstrip() for l in spec_lines ]

    type_defs = get_type_defs(spec_lines)
    fn_defs = list(parse_func(id, fspec) for id, fspec in enumerate(get_func_specs (spec_lines)))
    return app.App(name, type_defs, fn_defs)
