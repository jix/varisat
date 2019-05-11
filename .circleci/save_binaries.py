from subprocess import check_output
import json
import os
from shutil import copy2

cmd = 'cargo build --all-targets --message-format=json'.split()

output = check_output(cmd, universal_newlines=True)

for line in output.split('\n'):
    if not line:
        continue
    line = json.loads(line)
    if line['reason'] != 'compiler-artifact':
        continue
    executable = line.get('executable')
    if executable is None:
        continue
    if 'proc-macro' in line['target'].get('kind', []):
        continue
    package_name = line['package_id'].split()[0]
    executable_name = line['target']['name']
    if line['profile']['test']:
        subdir = 'tests'
    else:
        subdir = 'bins'

    target_dir = '/tmp/workspace/{subdir}/{package_name}'.format(
        subdir=subdir,
        package_name=package_name,
    )

    os.makedirs(target_dir, exist_ok=True)
    copy2(executable, '{target_dir}/{executable_name}'.format(
        target_dir=target_dir,
        executable_name=executable_name,
    ))
