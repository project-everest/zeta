from pathlib import Path

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
    return get_template_dir() / '_formats'

def get_verifier_template_dir():
    return get_template_dir() / 'verifier'

def get_dist_dir():
    zeta_dir = get_zeta_root()
    dist_dir = zeta_dir / 'steel' / 'dist'
    dist_dir = dist_dir.resolve()
    return dist_dir

def get_hostapp_template_dir():
    return get_template_dir() / 'hostapp'

def get_config_file(use_enclave):
    if use_enclave:
        config_file_name = 'config_enclave.txt'
    else:
        config_file_name = 'config.txt'
    return get_script_dir() / config_file_name
