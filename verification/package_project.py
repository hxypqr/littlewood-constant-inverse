"""Create a source-only, audited delivery archive, without the local cache junction."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT.parent / 'output'
OUT.mkdir(exist_ok=True)
summary = json.loads((ROOT / 'verification/validation_summary.json').read_text(encoding='utf-8'))
assert summary['whole_project_build_passed'] and summary['all_public_dependency_reports_passed']
inventory = json.loads((ROOT / 'verification/declarations.json').read_text(encoding='utf-8'))
paths = {ROOT / (m.replace('.', '/') + '.lean') for m in inventory['modules']}
paths.update(ROOT / name for name in [
    'README.md', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
    '.gitignore', 'Audit.lean', 'AuditAll.lean',
])
paths.update(p for p in (ROOT / 'manuscript').iterdir() if p.suffix in {'.pdf', '.tex'})
paths.add(ROOT / 'manuscript/VERSION.txt')
paths.update(p for p in (ROOT / 'verification').iterdir()
             if p.suffix in {'.md', '.py', '.json', '.lean'})
paths.update(ROOT / 'verification' / name for name in [
    'build.log', 'all_axioms.log', 'axioms.log', 'main_theorems_axioms.log',
    'appendix_b_axioms.log', 'quantitative_axioms.log', 'supplemental_checks.log',
])
for rel, expected in summary['proof_source_sha256'].items():
    assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == expected, rel
assert all(p.is_file() for p in paths)
assert all('.lake' not in p.relative_to(ROOT).parts for p in paths)
entries = {f'LittlewoodInverse/{p.relative_to(ROOT).as_posix()}': p.read_bytes()
           for p in sorted(paths)}
checksums = {name: hashlib.sha256(data).hexdigest() for name, data in entries.items()}
entries['LittlewoodInverse/DELIVERY_MANIFEST.json'] = (
    json.dumps(checksums, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
archive = OUT / 'LittlewoodInverse_Lean4_20260917.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for name, data in entries.items():
        z.writestr(name, data)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert set(z.namelist()) == set(entries)
    for name, expected in checksums.items():
        assert hashlib.sha256(z.read(name)).hexdigest() == expected, name
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix('.zip.sha256').write_text(digest + '  ' + archive.name + '\n', encoding='ascii')
print(json.dumps({'archive': str(archive), 'files': len(entries),
                  'bytes': archive.stat().st_size, 'sha256': digest}, ensure_ascii=False))
