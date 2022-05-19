#!/usr/bin/python3
""" Script to generate zeta files for an application  """

import argparse
import os
import shutil
from pathlib import Path
import app
import app_parse

def get_argparser():
    parser = argparse.ArgumentParser(description =
                                    'Generate zeta host and verifier files for an application')
    parser.add_argument('-i', '--input',
                        required=True,
                        help='input file containing the app specification')
    parser.add_argument('-o', '--out_dir',
                        help='output directory (default: the current directory)')
    parser.add_argument('-n', '--name', help='name of the application (default: filename)')
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
        return os.getcwd()
    else:
        return args.out_dir

def get_app_dir(parent_dir, app):
    return os.path.join(parent_dir, app.name)

def create_app_dir(parent_dir, app):
    app_dir = get_app_dir (parent_dir, app)
    if os.path.exists (app_dir):
        raise ValueError("directory " + app_dir + " exists")
    print(f'Creating directory {app_dir}')
    os.makedirs(app_dir)
    return app_dir

def get_script_dir():
    script_file = Path(__file__)
    script_dir = script_file.parent.absolute()
    return str(script_dir)

def get_zeta_root():
    script_dir = Path(get_script_dir())
    zeta_dir = script_dir.parent
    return str(zeta_dir)

def get_template_dir():
    templates_dir = Path(get_script_dir()) / 'templates'
    return str(templates_dir)

def get_formats_template_dir():
    return str (Path(get_template_dir()) / '_formats')

def get_dist_dir():
    zeta_dir = Path(get_zeta_root())
    dist_dir = zeta_dir / 'steel' / 'dist'
    dist_dir = dist_dir.resolve()
    return str(dist_dir)

def copy_dist_dir(app_dir):
    dist_dir_src = get_dist_dir();
    dist_dir_dest = Path(app_dir) / 'dist'
    dist_dir_dest = str(dist_dir_dest)
    print(f'Copying directory {dist_dir_src} -> {dist_dir_dest}')
    shutil.copytree(dist_dir_src, dist_dir_dest)

def gen_app_rfc (app_dir, a):
    formats_temp_dir = Path(app_dir) / '_formats'
    app_rfc_file = formats_temp_dir / 'App.rfc'

    with open(app_rfc_file, mode = 'w') as app_rfc_file:
        app_rfc_file.write(app.gen_everparse_types(a))
    return app_rfc_file

def build_formats (app_dir, a):
    # Check FSTAR_HOME and EVERPARSE_HOME environment vars are set
    if 'FSTAR_HOME' not in os.environ:
        raise ValueError('FSTAR_HOME not set')
    if 'EVERPARSE_HOME' not in os.environ:
        raise ValueError('EVERPARSE_HOME not set')
    print('FSTAR_HOME and EVERPARSE_HOME set')


def gen_formats_dir(app_dir, a):
    print(f'Copying directory {get_formats_template_dir()} -> {app_dir}')
    shutil.copytree(get_template_dir(), app_dir, dirs_exist_ok = True)
    gen_app_rfc (app_dir, a)

def main():
    try:
        argparser = get_argparser()
        args = argparser.parse_args()
        app = parse_app(args)
        app_dir = create_app_dir(get_out_dir(args), app)
        copy_dist_dir(app_dir)
        gen_formats_dir(app_dir, app)
    except ValueError as e:
        print(e)

if __name__ == '__main__':
    main()
