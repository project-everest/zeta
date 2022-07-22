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

def set_app_keyval_typedefs (app_dir, app):
    formats_dir = app_dir / 'formats'
    app.set_everparse_key_typedef (formats_dir)
    app.set_everparse_val_typedef (formats_dir)

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
(?P<attr>[^|]*?)
\|
(?P<file>[^|]*?)
\|
(?P<sep>[^|]*?)
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
                raise SyntaxError(f'file {src} is not a template file with suffix .tmp')
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
        copy_config_file (app_dir)

    except ValueError as e:
        print(e)

if __name__ == '__main__':
    main()
