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
        return Path(os.getcwd())
    else:
        return Path(args.out_dir)

def get_app_dir(parent_dir, app):
    return parent_dir / app.name

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
    return script_dir

def get_zeta_root():
    script_dir = get_script_dir()
    zeta_dir = script_dir.parent
    return zeta_dir

def get_template_dir():
    templates_dir = get_script_dir() / 'templates'
    return templates_dir

def get_formats_template_dir():
    return Path(get_template_dir()) / '_formats'

def get_dist_dir():
    zeta_dir = get_zeta_root()
    dist_dir = zeta_dir / 'steel' / 'dist'
    dist_dir = dist_dir.resolve()
    return dist_dir

def get_formats_temp_dir (app_dir):
    return app_dir / '_formats'

def get_formats_dir (app_dir):
    return app_dir / 'formats'

def get_verifier_dir (app_dir):
    return app_dir / 'verifier'

def copy_dist_dir(app_dir):
    dist_dir_src = get_dist_dir();
    dist_dir_dest = app_dir / 'dist'
    print(f'Copying directory {dist_dir_src} -> {dist_dir_dest}')
    shutil.copytree(dist_dir_src, dist_dir_dest)

def copy_everparse_includes (app_dir):
    everparse_home = Path(os.environ['EVERPARSE_HOME']) / 'include'
    print(f'Everparse Home: {everparse_home}')
    dest = app_dir / 'everparse'
    print(f'Copying directory {everparse_home} -> {dest}')
    shutil.copytree(everparse_home, dest)

def gen_app_rfc (app_dir, a):
    formats_temp_dir = get_formats_temp_dir (app_dir)
    app_rfc_file = formats_temp_dir / 'App.rfc'

    with open(app_rfc_file, mode = 'w') as app_rfc_file:
        app_rfc_file.write(app.gen_everparse_types(a))
    return app_rfc_file

def build_formats (app_dir):
    # Check FSTAR_HOME and EVERPARSE_HOME environment vars are set
    if 'FSTAR_HOME' not in os.environ:
        raise ValueError('FSTAR_HOME not set')
    if 'EVERPARSE_HOME' not in os.environ:
        raise ValueError('EVERPARSE_HOME not set')
    print('checked FSTAR_HOME and EVERPARSE_HOME set')
    with subprocess.Popen(['make'],
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

def copy_formats_output (app_dir):
    src_dir = get_formats_temp_dir(app_dir) / 'out'
    dest_dir = get_formats_dir (app_dir)
    shutil.copytree(src_dir, dest_dir)

def copy_formats_cmake(app_dir, a):
    src = get_template_dir() / 'formats_cmake.txt'
    dest = app_dir / 'formats' / 'CMakeLists.txt'
    p = re.compile(r'@app@')
    with open(src) as inp_file:
        with open(dest, 'w') as out_file:
            for l in inp_file.readlines():
                l = p.sub(a.name, l)
                out_file.write(l)

def gen_formats_dir(app_dir, a):
    print(f'Copying directory {get_formats_template_dir()} -> {get_formats_temp_dir(app_dir)}')
    shutil.copytree(get_formats_template_dir(), get_formats_temp_dir(app_dir))
    gen_app_rfc (app_dir, a)
    build_formats(app_dir)
    copy_formats_output(app_dir)
    copy_formats_cmake(app_dir, app)

def gen_verifier_dir(app_dir, app):
    verifier_dir = get_verifier_dir(app_dir)
    print(f'Creating directory {verifier_dir}')
    os.makedirs(verifier_dir)

    app_c_template = get_template_dir() / 'app.c'
    app_c = verifier_dir / 'app.c'
    shutil.copy(app_c_template, app_c)
    app.write_verifier_code(app_c)

def copy_global_cmake(app_dir):
    src = get_template_dir() / 'global_cmake.txt'
    dest = app_dir / 'CMakeLists.txt'
    print(f'Copying {dest}')
    shutil.copyfile(src = src, dst = dest)

def main():
    try:
        argparser = get_argparser()
        args = argparser.parse_args()
        app = parse_app(args)
        app_dir = create_app_dir(get_out_dir(args), app)
        copy_dist_dir(app_dir)
        copy_everparse_includes(app_dir)
        copy_global_cmake(app_dir)
        # gen_formats_dir(app_dir, app)
        gen_verifier_dir(app_dir, app)


    except ValueError as e:
        print(e)

if __name__ == '__main__':
    main()
