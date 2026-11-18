#!/usr/bin/env python3
"""Check the current package, theorem dependencies, and semantic refusals."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain-bin', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
BIN = args.toolchain_bin.resolve()
OUT = args.output.resolve()
if OUT == REPO or REPO in OUT.parents or OUT in REPO.parents:
    parser.error('Use an output directory outside the repository')
OUT.mkdir(parents=True, exist_ok=True)
record = {'started_at': datetime.now(timezone.utc).isoformat(), 'commands': []}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, command, expected=0, env=None):
    result = subprocess.run([str(a) for a in command], cwd=REPO,
                            capture_output=True, env=env, timeout=300)
    log = OUT / (name + '.log')
    log.write_bytes(result.stdout + result.stderr)
    record['commands'].append({'name': name, 'argv': [str(a) for a in command],
                               'exit_code': result.returncode,
                               'expected_exit': expected,
                               'log_sha256': digest(log)})
    print(name, result.returncode, flush=True)
    if result.returncode != expected:
        raise RuntimeError(log.read_text())
    return log.read_text()


try:
    version = run('version', [BIN / 'lean', '--version']).strip()
    pin = (REPO / 'lean-toolchain').read_text().strip().split(':')[-1].lstrip('v')
    if f'version {pin},' not in version:
        raise RuntimeError('Toolchain version does not match lean-toolchain')
    record['lean_version'] = version
    record['lean_sha256'] = digest(BIN / 'lean')
    sources = sorted(REPO.glob('SoftwareIsQuantifiable/*.lean'))
    subject = sources + [REPO / 'SoftwareIsQuantifiable.lean', REPO / 'lakefile.lean',
                         REPO / 'lean-toolchain', REPO / 'lake-manifest.json',
                         REPO / 'verification/ParetoControls.lean',
                         HERE / 'Controls.lean', HERE / 'check.py']
    subject += sorted(p for p in (REPO / 'examples').rglob('*') if p.is_file())
    record['sources'] = {str(p.relative_to(REPO)): digest(p) for p in subject}
    run('clean', [BIN / 'lake', 'clean'])
    run('build', [BIN / 'lake', '--wfail', 'build'])
    lean = [BIN / 'lake', 'env', BIN / 'lean', '-DwarningAsError=true']
    run('upstream-controls', lean + ['verification/ParetoControls.lean'])
    run('occurrence-controls', lean + ['verification/occurrences/Controls.lean'])
    example_env = dict(os.environ, LEAN=str(BIN / 'lean'))
    run('examples', ['sh', 'examples/check.sh'], env=example_env)

    names = []
    for path in sources:
        for name in re.findall(r'^theorem\s+(\w+)', path.read_text(), re.M):
            prefix = 'SoftwareIsQuantifiable.'
            if name != 'decide_false_of_not':
                prefix += path.stem + '.'
            names.append(prefix + name)
    audit = OUT / 'Axioms.lean'
    audit.write_text('import SoftwareIsQuantifiable\n' +
                     ''.join('#print axioms ' + name + '\n' for name in names))
    axout = run('axioms', lean + [audit])
    entries = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", axout)
    if {name for name, _ in entries} != set(names):
        raise RuntimeError('Theorem audit inventory is incomplete')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in entries:
        actual = {a.strip() for a in axioms.split(',') if a.strip()}
        if not actual <= allowed:
            raise RuntimeError((name, actual))
    record['theorems'] = names
    record['allowed_axioms'] = sorted(allowed)

    false_claims = {
        'substituted-multiplicity':
            '[(0,0),(1,0),(1,0)] ∈ Finiteness.orderings (⟨[0,0,1],[0]⟩ : Finiteness.Qualification Nat Nat)',
        'wrong-scope':
            'Coverage.recorded (fun _ => true) (Coverage.inScope 1 [(2,⟨7,1⟩)]) ⟨7⟩ = true',
        'invalid-witness':
            'Coverage.recorded (fun w => decide (0 < w.events)) (Coverage.inScope 2 [(2,⟨7,0⟩)]) ⟨7⟩ = true',
        'empty-manifest-is-coverage':
            'Coverage.recorded (fun _ => true) [] ⟨7⟩ = true',
        'overlap-is-nonregression': 'Pareto.noWorse (18,0) (10,0)',
        'dropped-behavior':
            'Pareto.acceptsReplacement "same" "same" ({ qualified := [1,2] } : Pareto.PriorQualification Nat) { offered := [1] } ⟨0,0,by decide⟩ ⟨0,0,by decide⟩ ⟨0,0,by decide⟩ ⟨0,0,by decide⟩ = true',
        'equal-cost-is-strict':
            'Pareto.dominates (0,0) (0,0)',
    }
    record['refusals'] = []
    for name, claim in false_claims.items():
        path = OUT / (name + '.lean')
        path.write_text('import SoftwareIsQuantifiable\nopen SoftwareIsQuantifiable\n' +
                        'example : ' + claim + ' := by decide\n')
        output = run(name, lean + [path], expected=1)
        if "tactic 'decide' proved that the proposition" not in output or 'is false' not in output:
            raise RuntimeError('Expected semantic false-proposition rejection: ' + output)
        record['refusals'].append({'name': name, 'source_sha256': digest(path)})
    after = {str(p.relative_to(REPO)): digest(p) for p in subject}
    if after != record['sources']:
        raise RuntimeError('Verification subject changed during execution')
    record['unchanged_after_execution'] = True
    record['status'] = 'passed'
except BaseException as exc:
    record['status'] = 'failed'
    record['error'] = str(exc)
    raise
finally:
    record['finished_at'] = datetime.now(timezone.utc).isoformat()
    (OUT / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
