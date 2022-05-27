#!/usr/bin/python3
""" Script to generate zeta files for an application  """

import argparse
import os
import shutil
from pathlib import Path
import subprocess
import re
import app
import app_parse
from paths import *
import sys

def get_argparser():
    parser = argparse.ArgumentParser(description =
                                    'Generate zeta host and verifier files for an application')
    parser.add_argument('-i', '--input',
                        required=True,
                        help='input file containing the app specification')
    parser.add_argument('-o', '--out_dir',
                        help='output directory (default: the current directory)')
    parser.add_argument('-n', '--name', help='name of the application (default: filename)')
    parser.add_argument('-f', '--force', action='store_true', help='force delete output directory if exists')
    return parser

def get_name_from_input(inp_file):
    name = os.path.basename(inp_file)
    return name.split('.')[0]

def parse_app(args):
    # if name not specified, get the name from the file name
    name = args.name
    if name == None:
        name = get_name_from_input(args.input)

    with open(args.input) as inp_file:
        app_spec = inp_file.readlines()
        app = app_parse.parse_app(name, app_spec)
        return app

def get_out_dir(args):
    if args.out_dir == None:
        return Path(os.getcwd())
    else:
        return Path(args.out_dir)

def get_app_dir(parent_dir, app):
    return parent_dir / app.name

def get_formats_temp_dir (app_dir):
    return app_dir / '_formats'

def get_formats_dir (app_dir):
    return app_dir / 'formats'

def get_verifier_dir (app_dir):
    return app_dir / 'verifier'

def get_hostgen_dir (app_dir):
    return app_dir / 'hostgen'

def get_hostapp_dir (app_dir):
    return app_dir / 'hostapp'

def build_formats (app_dir,_):
    # Check FSTAR_HOME and EVERPARSE_HOME environment vars are set
    if 'FSTAR_HOME' not in os.environ:
        raise ValueError('FSTAR_HOME not set')
    if 'EVERPARSE_HOME' not in os.environ:
        raise ValueError('EVERPARSE_HOME not set')
    print('checked FSTAR_HOME and EVERPARSE_HOME set')
    with subprocess.Popen(['make', '-j', '2'],
                          stdout = subprocess.PIPE,
                          stderr = subprocess.PIPE,
                          cwd = get_formats_temp_dir(app_dir)) as bp:
        line_count = 0
        total_exp = 150
        for line in iter(bp.stdout.readline, ''):
            line = line.decode('utf-8')
            line = line.strip()
            if 'Verified module:' in line:
                print(f'[{int(line_count*100/total_exp)}%] Build formats: {line}')
                line_count += 1
            if 'KreMLin: wrote out' in line:
                print(f'[{line_count}] Build formats: {line}')
                break
        bp.wait()
        print(f'Return code: {bp.returncode}')
        if bp.returncode != 0:
            raise ValueError(f'Everparse make fail (return code = {bp.returncode})')

def set_everparse_headers (app_dir, app):
    formats_dir = app_dir / 'formats'
    app.set_everparse_headers (formats_dir)

def copy_verifier_cmake(app_dir, a):
    src = get_template_dir() / 'verifier_cmake.txt'
    dest = app_dir / 'verifier' / 'CMakeLists.txt'
    translate_cmake_file(src, dest, a)

def get_app_key_typedef (app_dir):
    app_key_h = get_formats_dir(app_dir) / 'App_key.h'
    p = re.compile(r'typedef.*App_key_app_key;', re.DOTALL)
    with open (app_key_h) as inp_file:
        code = inp_file.read()
        m = p.search(code)
        if m == None:
            raise ValueError('App_key typedef not found')
        return m.group()

def get_app_val_typedef (app_dir):
    app_key_h = get_formats_dir(app_dir) / 'App_val.h'
    p = re.compile(r'typedef.*App_val_app_val;', re.DOTALL)
    with open (app_key_h) as inp_file:
        code = inp_file.read()
        m = p.search(code)
        if m == None:
            raise ValueError('App_key typedef not found')
        return m.group()

def gen_zeta_app_types_h (app_dir, app):
    src = get_template_dir() / 'ZetaFormatsApplicationTypes.h'
    dest = get_verifier_dir(app_dir) / 'ZetaFormatsApplicationTypes.h'

    key_typedef = get_app_key_typedef(app_dir)
    val_typedef = get_app_val_typedef(app_dir)
    app_typedefs = f'{key_typedef}\n{val_typedef}'
    p = re.compile(r'@app_types@')

    with open(dest, 'w') as out_file:
        with open(src) as inp_file:
            code = inp_file.read()
            code = p.sub(app_typedefs, code)
            out_file.write(code)

def get_format_includes(app_dir):
    format_include_files = get_formats_dir(app_dir).glob('*.h')
    r = ''
    for f in format_include_files:
        n = f.name
        r += f'#include <{n}>\n'
    return r

def gen_app_c (app_dir, app):
    verifier_dir = get_verifier_dir(app_dir)
    app_c_template = get_template_dir() / 'app.c'
    app_c = verifier_dir / 'app.c'
    format_includes = get_format_includes(app_dir)
    p = re.compile(r'@format-includes@')

    with open (app_c_template) as inp:
        code = inp.read()
        code = p.sub(format_includes, code)
        with open (app_c, 'w') as out:
            out.write(code)
    app.write_verifier_code(app_c)

def gen_verifier_dir(app_dir, app):
    verifier_dir = get_verifier_dir(app_dir)
    print(f'Copying directory {get_verifier_template_dir()} -> {verifier_dir}')
    shutil.copytree(get_verifier_template_dir(), verifier_dir);
    gen_app_c(app_dir, app)
    copy_verifier_cmake(app_dir, app)
    gen_zeta_app_types_h (app_dir, app)

def gen_hostgen_cmake (app_dir, app):
    hostgen_cmake = get_hostgen_dir(app_dir) / 'CMakeLists.txt'
    os.remove(hostgen_cmake)

    hostgen_cmake_tmp = get_template_dir() / 'hostgen_cmake.txt.tmp'
    with open (hostgen_cmake_tmp) as tf:
        text = tf.read()
        text = app.transform_text(text)
        with open (hostgen_cmake, 'w') as f:
            f.write(text)

def gen_hostapp_cmake (app_dir, app):
    hostapp_cmake = get_hostapp_dir(app_dir) / 'CMakeLists.txt'
    hostapp_cmake_tmp = get_template_dir() / 'hostapp_cmake.txt.tmp'

    with open (hostapp_cmake_tmp) as tf:
        text = tf.read()
        text = app.transform_text(text)
        with open (hostapp_cmake, 'w') as f:
            f.write(text)

def gen_host_dir(app_dir, app):
    hostgen_src = get_zeta_root() / 'apps' / 'host'
    hostgen_dest = get_hostgen_dir(app_dir)
    print(f'Copying directory {hostgen_src} -> {hostgen_dest}')
    shutil.copytree(hostgen_src, hostgen_dest)
    gen_hostgen_cmake(app_dir, app)

    hostapp_dir = get_hostapp_dir(app_dir)
    hostapp_tmp_dir = get_hostapp_template_dir()
    print(f'Copying directory {hostapp_tmp_dir} -> {hostapp_dir}')
    shutil.copytree(hostapp_tmp_dir, hostapp_dir)

    app_h_file = hostapp_dir / 'app.h'
    app.write_host_decl(app_h_file)

    app_cpp_file = hostapp_dir / 'app.cpp'
    app.write_host_def (app_cpp_file)
    gen_hostapp_cmake(app_dir, app)

def copy_config_file (app_dir):
    config_file = 'zeta_config.h.in'
    src = get_zeta_root() / config_file
    dest = app_dir / config_file
    shutil.copy(src, dest)

def expand_env_var (src):
    p = re.compile(r'\$\((?P<ev>.*?)\)')
    return p.sub(lambda x: os.environ[x.group('ev')], src)

def expand_path (app_dir, p):
    p = p.replace('@app_dir@', str(app_dir))
    p = expand_env_var(p)

    if os.path.isabs(p):
        return Path(p).resolve()
    else:
        p = get_script_dir() / p
        return p.resolve()

def get_attribute (obj, attr):
    print(f'get_attr {obj} {attr}')
    if attr == '_':
        return str(obj)
    else:
        return str(getattr(obj, attr))

def iter_interpolate (obj, attr, template, sep):
    sep = sep.replace('n', '\n')
    if template[0:5] == 'file:':
        template_file = get_template_dir() / template[5:]
        template = template_file.read_text()

    return sep.join([interpolate(o, template) for o in getattr(obj, attr)])

pat_iter_interp = re.compile(r'''
@@
(?P<attr>[^|]*)
\|
(?P<file>[^|]*)
\|
(?P<sep>[^|]*)
@@
''', re.VERBOSE)

pat_interp = re.compile(r'@(?P<attr>.*?)@')

def interpolate (obj, template):
    text = pat_iter_interp.sub (lambda m: iter_interpolate (obj,
                                                            m.group('attr'),
                                                            m.group('file'),
                                                            m.group('sep')),
                                template)
    text = pat_interp.sub (lambda m: get_attribute (obj, m.group('attr')), text)
    return text

def process_config_file (app_dir, app):
    with open(get_config_file()) as f:
        for l in f.readlines():

            l = l.strip()

            if len(l) == 0:
                continue

            # ignore commented lines
            if l[0] == '#':
                continue

            p = l.split()

            # a single token implies a command
            if len(p) == 1:
                globals()[p[0]](app_dir, app)
                continue

            if len(p) != 2:
                raise SyntaxError(f'Invalid config file line: {l}')

            src = expand_path(app_dir, p[0])
            dest = (app_dir/p[1]).resolve()

            if src.is_dir():
                print(f'Copying directory {src} -> {dest}')
                shutil.copytree(src, dest)
            elif src.suffix != '.tmp':
                raise SyntaxError(f'file {src} is nota template file with suffix .tmp')
            else:
                print(f'transforming file {src} -> {dest}')
                with open (src) as src_file:
                    src_text = src_file.read()
                    dest_text = interpolate(app, src_text)
                    with open(dest, 'w') as dest_file:
                        dest_file.write(dest_text)

def main():
    try:
        argparser = get_argparser()
        args = argparser.parse_args()
        app = parse_app(args)
        app_dir = get_app_dir(get_out_dir(args), app)

        # check if app_dir exists
        if app_dir.exists():
            if args.force:
                shutil.rmtree(app_dir)
            else:
                sys.exit(f'directory {app_dir} exists')

        # create app_dir
        print(f'Creating directory {app_dir}')
        os.makedirs(app_dir)

        process_config_file(app_dir, app)
        # gen_verifier_dir(app_dir, app)
        # gen_host_dir(app_dir, app)
        # copy_config_file (app_dir)

    except ValueError as e:
        print(e)

if __name__ == '__main__':
    main()
