"""Repository checks before Lean and the independent Comparator run (Python 3.11+)."""
from pathlib import Path
import json
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parent.parent
PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def lean_code(text):
    """Mask nested comments and strings so the lexical audit does not flag prose."""
    out, depth, string, escape, i = [], 0, False, False, 0
    while i < len(text):
        pair, ch = text[i:i+2], text[i]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if ch == '\n' else ' '); i += 1
        elif string:
            out.append('\n' if ch == '\n' else ' ')
            if escape: escape = False
            elif ch == '\\': escape = True
            elif ch == '"': string = False
            i += 1
        elif pair == '--':
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out.extend(' ' * (j-i)); i = j
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif ch == '"': string = True; out.append(' '); i += 1
        else: out.append(ch); i += 1
    require(not depth and not string, 'Unclosed Lean comment or string')
    return ''.join(out)

def main():
    challenge = (ROOT / 'Challenge.lean').read_text(encoding='utf-8')
    statement = (ROOT / 'Erdos1045/Statement.lean').read_text(encoding='utf-8')
    require(challenge.startswith(statement), 'Challenge definitions drifted from Statement.lean')
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100*1024,
            'Challenge exceeds the Palomar hard limit')
    code = lean_code(challenge)
    require(re.findall(r'^import\s+(\S+)', code, re.M) == ['Mathlib'],
            'Challenge must import only Mathlib')
    require(len(re.findall(r'\bsorry\b', code)) == 1, 'Expected exactly one Challenge theorem hole')
    statement_code = lean_code(statement)
    require(re.search(r'def evenThreshold\s*:\s*ℕ\s*:=\s*2\s*\^\s*\(10\s*\^\s*120\)',
                      statement_code), 'The submitted statement must expose the concrete even cutoff')
    require(re.search(r'def regularThreshold\s*:\s*ℕ\s*:=\s*2\s*\^\s*100000000',
                      statement_code), 'Missing concrete regular-polygon cutoff')
    require(re.search(r'def Claims\s*:\s*Prop\s*:=\s*DiameterCharacterization\s*∧\s*PerimeterCharacterization\s*∧\s*NormalizedLimits\s*∧\s*Algebraic.CertificateAboveThreshold\s*∧\s*KKT.UniquePositiveKKT',
                      statement_code), 'Expected the five canonical public conclusions')
    require(re.search(r'def UniquePositiveKKT\s*:\s*Prop\s*:=\s*∀ m : ℕ, evenThreshold ≤ 2 \* m', statement_code),
            'Positive KKT must use the same concrete even cutoff')
    require('def ExplicitEvenClaims' not in statement_code and 'def EventualDiameterCharacterization' not in statement_code,
            'Duplicated eventual and explicit public conclusions')
    require(re.search(r'def DiameterCharacterization\s*:\s*Prop\s*:=\s*∀ n : ℕ, diameterThreshold n ≤ n', statement_code),
            'Diameter statement must use the parity-dependent concrete cutoff')

    require(re.search(r'theorem main : Statement.Claims := by\s+sorry',
                      lean_code(challenge[len(statement):])), 'Unexpected Challenge theorem')
    config = json.loads((ROOT / 'comparator.json').read_text())
    require(config == {
        'challenge_module': 'Challenge', 'solution_module': 'Solution',
        'theorem_names': ['Erdos1045.main'],
        'definition_names': ['Erdos1045.Statement.evenThreshold', 'Erdos1045.Statement.regularThreshold', 'Erdos1045.Statement.diameterThreshold', 'Erdos1045.Statement.DiameterCharacterization', 'Erdos1045.Statement.PerimeterCharacterization', 'Erdos1045.Statement.Algebraic.CertificateAboveThreshold', 'Erdos1045.Statement.KKT.UniquePositiveKKT'],
        'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'enable_nanoda': True,
    }, 'Comparator configuration changed; review its claim and proof policy')
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    require(not (ROOT / 'lakefile.lean').exists(), 'Exactly one Lakefile is permitted')
    require(lake['require'][0]['rev'] == PIN, 'Unexpected Mathlib requirement')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = manifest['packages']
    require(next(p for p in packages if p['name'] == 'mathlib')['rev'] == PIN,
            'Unexpected Mathlib manifest revision')
    for p in packages:
        require(p['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', p['rev']) and
                re.fullmatch(r'https://github\.com/[\w.-]+/[\w.-]+', p['url']),
                'Dependency is not pinned to a public GitHub SHA: ' + p['name'])
    sources = [ROOT / 'Erdos1045.lean', ROOT / 'Solution.lean']
    sources += list((ROOT / 'Erdos1045').rglob('*.lean')) + list((ROOT / 'Internal').rglob('*.lean'))
    forbidden = re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC')
    for source in sources:
        require(not forbidden.search(lean_code(source.read_text(encoding='utf-8-sig'))),
                'Forbidden proof construction: ' + str(source.relative_to(ROOT)))
    print(f'Layout PASS: {len(sources)} solution sources; Challenge {len(challenge.splitlines())} '
          f'lines / {len(challenge.encode())} bytes; {len(packages)} pinned dependencies.')
    if (ROOT / '.git').exists():
        paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
        bad = [p for p in paths if p and (p.endswith(('.olean', '.ilean', '.olean.private',
               '.olean.server', '.ir', '.trace', '.o', '.obj', '.a', '.bc', '.so', '.dll', '.dylib'))
               or p.split('/')[0] in {'.lake', '.build', '.verification', '.dev', '.cache', 'tmp', 'output'})]
        require(not bad, 'Generated or local-only files tracked by Git: ' + ', '.join(bad[:10]))

if __name__ == '__main__':
    main()
