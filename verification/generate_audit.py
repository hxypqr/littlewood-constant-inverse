"""Generate declaration and forbidden-placeholder audits for the root import closure."""
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {
    'LittlewoodInverse.External.mps_weighted',
    'LittlewoodInverse.External.polynomial_bsg',
    'LittlewoodInverse.HardyExternal.schwarz_integral_boundary',
    'LittlewoodInverse.HardyExternal.bounded_holomorphic_radial_boundary',
    'LittlewoodInverse.BackgroundExternal.green_sanders',
    'LittlewoodInverse.BackgroundExternal.bloom_green_inverse',
    'LittlewoodInverse.BackgroundExternal.bloom_green_constant',
}
EXCLUDED_MODULES = {'LittlewoodInverse.MomentCertificateTest'}
DECLARATION = re.compile(
    r'^\s*(?:@\[.*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*'
    r'(theorem|lemma|axiom|constant)\s+([^\s(:{]+)')

def code_only(text):
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2
            elif pair == '-/':
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\' and i+1 < len(text):
                out.extend('  '); i += 2
            else:
                string = text[i] != '"'
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end-i)); i = end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)

modules = {}
def visit(module):
    if module in modules: return
    path = ROOT / (module.replace('.', '/') + '.lean')
    source = code_only(path.read_text(encoding='utf-8-sig'))
    modules[module] = (path, source)
    for line in source.splitlines():
        if line.lstrip().startswith('import '):
            for child in line.split()[1:]:
                if child.startswith('LittlewoodInverse.'):
                    visit(child)

def inspect_source(module, source):
    declarations, axioms, forbidden = [], [], []
    stack = []
    for line_no, line in enumerate(source.splitlines(), 1):
        if m := re.match(r'^\s*namespace\s+([^\s]+)', line):
            stack.append(('namespace', m[1]))
        elif m := re.match(r'^\s*section(?:\s+([^\s]+))?\s*$', line):
            stack.append(('section', m[1]))
        elif re.match(r'^\s*end(?:\s+[^\s]+)?\s*$', line):
            if stack: stack.pop()
        else:
            m = DECLARATION.match(line)
            if m:
                name = '.'.join([v for k, v in stack if k == 'namespace'] + [m[2]])
                name = name.removeprefix('_root_.')
                item = {'name': name, 'module': module, 'line': line_no,
                        'private': bool(re.search(r'\bprivate\b', line[:m.end(1)]))}
                (axioms if m[1] in ('axiom', 'constant') else declarations).append(item)
        if re.search(r'\b(sorry|admit|native_decide|sorryAx)\b', line):
            forbidden.append({'module': module, 'line': line_no, 'code': line.strip()})
    return declarations, axioms, forbidden

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--strict', action='store_true',
                    help='Fail for orphan modules, forbidden proof tokens, or unapproved axioms.')
args = parser.parse_args()

# Regression checks for the source scanner itself: comments/strings do not
# count as declarations, whereas indented/internal axioms must be reported.
test_source = code_only('''namespace AuditTest
/- axiom hidden : False /- sorry -/ -/
def text := "axiom hidden : False; sorry"
  axiom internal : False
protected theorem actual : True := by trivial
end AuditTest
''')
test_decls, test_axioms, test_forbidden = inspect_source('AuditTest', test_source)
assert [x['name'] for x in test_decls] == ['AuditTest.actual']
assert [x['name'] for x in test_axioms] == ['AuditTest.internal']
assert not test_forbidden

visit('LittlewoodInverse')
all_sources = {}
for path in (ROOT / 'LittlewoodInverse').rglob('*.lean'):
    module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
    all_sources[module] = (path, code_only(path.read_text(encoding='utf-8-sig')))
orphans = sorted(set(all_sources) - set(modules) - EXCLUDED_MODULES)

declarations, axioms, forbidden = [], [], []
all_axioms = []
for module, (path, source) in sorted(all_sources.items()):
    ds, ax, bad = inspect_source(module, source)
    all_axioms.extend(ax)
    forbidden.extend(bad)
    if module in modules:
        declarations.extend(ds)
        axioms.extend(ax)
internal_axioms = [x for x in all_axioms if x['name'] not in ALLOWED_AXIOMS]

names = [item['name'] for item in declarations if not item['private']]
if len(names) != len(set(names)):
    raise RuntimeError('Duplicate fully qualified declaration names')
(ROOT / 'AuditAll.lean').write_text(
    'import LittlewoodInverse\n\n' + '\n'.join('#print axioms ' + n for n in names) + '\n',
    encoding='utf-8')
(ROOT / 'verification/declarations.json').write_text(
    json.dumps({'modules': list(sorted(modules)), 'theorems': declarations,
                'external_axioms': axioms}, ensure_ascii=False, indent=2), encoding='utf-8')
(ROOT / 'verification/source_audit.json').write_text(
    json.dumps({'module_count': len(modules), 'theorem_count': len(declarations),
                'public_theorems_for_kernel_audit': len(names),
                'external_axiom_count': len(axioms),
                'all_project_axiom_count': len(all_axioms),
                'forbidden_tokens': forbidden, 'unapproved_axioms': internal_axioms,
                'orphan_modules': orphans, 'excluded_modules': sorted(EXCLUDED_MODULES)},
               ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps({'modules':len(modules), 'theorems':len(declarations),
                  'external_axioms':len(axioms), 'all_project_axioms':len(all_axioms),
                  'forbidden':forbidden, 'unapproved_axioms':internal_axioms,
                  'orphan_modules':orphans}, ensure_ascii=False))
if args.strict and (forbidden or internal_axioms or orphans):
    raise SystemExit('Strict audit failed; see verification/source_audit.json.')
