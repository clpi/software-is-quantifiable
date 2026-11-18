#!/usr/bin/env python3
"""Recorded clean build, complete theorem axiom audit, and damaged controls."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain-bin', type=Path, required=True,
                    help='Directory containing the pinned Lean 4.15.0 lean and lake executables')
parser.add_argument('--output', type=Path, required=True,
                    help='Separate directory for the replay record and logs')
args = parser.parse_args()
BIN = args.toolchain_bin.resolve()
OUT = args.output.resolve()
if OUT == HERE or HERE in OUT.parents:
    parser.error('Keep replay outputs separate from the committed evidence directory')
OUT.mkdir(parents=True, exist_ok=True)
REFERENCE = json.loads((HERE / 'record.json').read_text())
record = {'started_at': datetime.now(timezone.utc).isoformat(),
          'base': 'a1d84c603906edfbf34dd117e5bd5de986db3940', 'commands': []}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(name, args, expected=0):
    result = subprocess.run([str(a) for a in args], cwd=REPO, capture_output=True)
    stdout, stderr = OUT / (name+'.stdout'), OUT / (name+'.stderr')
    stdout.write_bytes(result.stdout)
    stderr.write_bytes(result.stderr)
    item = {'name': name, 'argv': [str(a) for a in args], 'exit_code': result.returncode,
            'expected_exit': expected, 'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr)}
    record['commands'].append(item)
    print(name, result.returncode, flush=True)
    assert result.returncode == expected, result.stdout.decode() + result.stderr.decode()
    return result.stdout.decode() + result.stderr.decode()

try:
    record['lean_version'] = run('lean-version', [BIN/'lean', '--version']).strip()
    record['lean_sha256'] = digest(BIN/'lean')
    sources = sorted(REPO.glob('SoftwareIsQuantifiable/*.lean')) + [REPO/'SoftwareIsQuantifiable.lean', REPO/'lakefile.lean', REPO/'verification/ParetoControls.lean']
    record['sources'] = {str(p.relative_to(REPO)): digest(p) for p in sources}
    assert record['sources'] == REFERENCE['sources'], 'Source differs from the committed verification subject'
    assert record['lean_version'] == REFERENCE['lean_version'], 'Use the recorded Lean 4.15.0 toolchain version'
    record['reference_record_sha256'] = digest(HERE / 'record.json')
    run('clean', [BIN/'lake', 'clean'])
    build = run('build', [BIN/'lake', '--wfail', 'build'])
    assert 'Build completed successfully.' in build
    assert 'sorry' not in build.lower() and 'warning:' not in build.lower()
    run('upstream-pareto-controls', [BIN/'lake', 'env', BIN/'lean', '-DwarningAsError=true', 'verification/ParetoControls.lean'])

    theorem_names = []
    for path in sources:
        if path.parent.name != 'SoftwareIsQuantifiable':
            continue
        # These modules use the named two-level namespace throughout;
        # Fold's pre-namespace helper is the sole exception.
        for name in re.findall(r'^theorem\s+(\w+)', path.read_text(), re.M):
            prefix = 'SoftwareIsQuantifiable.'
            if name != 'decide_false_of_not':
                prefix += path.stem + '.'
            theorem_names.append(prefix + name)
    audit = OUT / 'Axioms.lean'
    audit.write_text('import SoftwareIsQuantifiable\n' + ''.join('#print axioms '+n+'\n' for n in theorem_names))
    axout = run('axioms', [BIN/'lake', 'env', BIN/'lean', '-DwarningAsError=true', audit])
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    entries = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", axout)
    assert {name for name, _ in entries} == set(theorem_names)
    for name, axioms in entries:
        actual = set(a.strip() for a in axioms.split(',') if a.strip())
        assert actual <= allowed, (name, actual)
    record['theorem_count'] = len(theorem_names)
    record['theorem_names'] = theorem_names
    record['allowed_axioms'] = sorted(allowed)
    record['unexpected_axioms'] = []

    controls = [
        ('unrecorded-witness', 'Coverage.lean',
         'ledger.any (fun w => valid w && decide (w.exec = e.id))',
         'decide (e.id = e.id) || ledger.any (fun w => valid w && decide (w.exec = e.id))'),
        ('missing-validator', 'Coverage.lean',
         'ledger.any (fun w => valid w && decide (w.exec = e.id))',
         'ledger.any (fun w => decide (w.exec = e.id))'),
        ('missing-compute-gate', 'Pareto.lean',
         'accepts qualified candidate && decide (noWorse out inc)',
         'accepts qualified candidate && decide (out.1 ≤ inc.1)'),
        ('missing-behavior-gate', 'Pareto.lean',
         'accepts qualified candidate && decide (noWorse out inc)',
         'true && decide (noWorse out inc)'),
    ]
    record['controls'] = []
    for name, file, before, after in controls:
        source = (REPO/'SoftwareIsQuantifiable'/file).read_text()
        assert source.count(before) == 1
        mutant = OUT / (name+'.lean')
        mutant.write_text(source.replace(before, after))
        output = run(name, [BIN/'lake', 'env', BIN/'lean', mutant], expected=1)
        assert 'error:' in output, output
        record['controls'].append({'name': name, 'mutant_sha256': digest(mutant), 'result': 'rejected'})
    record['status'] = 'passed'
except BaseException as exc:
    record['status'] = 'failed'
    record['error'] = str(exc)
    raise
finally:
    record['finished_at'] = datetime.now(timezone.utc).isoformat()
    (OUT/'record.json').write_text(json.dumps(record, indent=2)+'\n')
