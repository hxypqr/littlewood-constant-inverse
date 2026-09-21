"""Check the complete Lean dependency output against the audited source inventory."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
V = ROOT / 'verification'
inventory = json.loads((V / 'declarations.json').read_text(encoding='utf-8'))
source = json.loads((V / 'source_audit.json').read_text(encoding='utf-8'))
allowed = {'propext', 'Classical.choice', 'Quot.sound'} | {
    x['name'] for x in inventory['external_axioms']
}
expected = {x['name'] for x in inventory['theorems'] if not x.get('private', False)}
log = (V / 'all_axioms.log').read_text(encoding='utf-8-sig')
dependencies = {}
for name, body in re.findall(r"^'([^\r\n]+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M):
    dependencies[name] = sorted({x.strip() for x in body.split(',') if x.strip()})
for name in re.findall(r"^'([^\r\n]+)' does not depend on any axioms", log, re.M):
    dependencies[name] = []
unexpected = {name: [a for a in deps if a not in allowed]
              for name, deps in dependencies.items() if set(deps) - allowed}
missing = sorted(expected - dependencies.keys())
extra = sorted(dependencies.keys() - expected)
errors = re.findall(r'^.*(?:error:|unknown constant|unsolved goals).*$', log, re.M)
build = (V / 'build.log').read_text(encoding='utf-8-sig')
build_ok = 'Build completed successfully' in build and not re.search(r'error:|build failed', build)
assert not source['forbidden_tokens'], source['forbidden_tokens']
assert not source['unapproved_axioms'], source['unapproved_axioms']
assert not source['orphan_modules'], source['orphan_modules']
assert build_ok, 'Whole-project build failed or has no successful completion record'
assert not missing, missing
assert not extra, extra
assert not errors, errors
assert not unexpected, unexpected
manifest = {
    'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'module_count': source['module_count'],
    'source_theorem_count_including_private': source['theorem_count'],
    'public_theorems_dependency_checked': len(dependencies),
    'external_axioms': sorted(allowed - {'propext', 'Classical.choice', 'Quot.sound'}),
    'forbidden_tokens': [], 'unapproved_axioms': [], 'orphan_modules': [],
    'whole_project_build_passed': True,
    'all_public_dependency_reports_passed': True,
    'proof_source_sha256': {
        p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for module in inventory['modules']
        for p in [ROOT / (module.replace('.', '/') + '.lean')]
    },
    'manuscript_sha256': {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted((ROOT / 'manuscript').iterdir()) if p.suffix in {'.pdf', '.tex'}
    },
}
(V / 'validation_summary.json').write_text(
    json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in manifest.items() if not k.endswith('sha256')}, ensure_ascii=False))
