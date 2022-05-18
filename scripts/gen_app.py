#!/usr/bin/python3
""" Script to generate zeta files for an application  """

import argparse

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

argparser = get_argparser()
args = argparser.parse_args()
