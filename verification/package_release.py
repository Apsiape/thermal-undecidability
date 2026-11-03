"""Regenerate the portable paper source archive, manifest, and public hashes.
Run after the strict paper build and replay audit. Python standard library only.
"""
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
import hashlib,json
ROOT=Path(__file__).resolve().parent.parent
PAPER=ROOT/'paper'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def public(p):
    rel=p.relative_to(ROOT)
    return p.is_file() and not any(x in {'.git','__pycache__','build','runs'} for x in rel.parts)
source=sorted(p for p in PAPER.rglob('*') if public(p) and p.suffix in {'.tex','.bib','.txt','.py'})
manifest={p.relative_to(PAPER).as_posix():{'sha256':digest(p),'bytes':p.stat().st_size} for p in source}
(PAPER/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
with ZipFile(PAPER/'source.zip','w',ZIP_DEFLATED) as z:
    for p in source+[PAPER/'source-manifest.json']:
        item=ZipInfo(p.relative_to(PAPER).as_posix(),date_time=(2026,11,3,0,0,0))
        item.compress_type=ZIP_DEFLATED;item.external_attr=0o644<<16
        z.writestr(item,p.read_bytes())
hashfile=ROOT/'verification/SHA256SUMS'
files=sorted(p for p in ROOT.rglob('*') if public(p) and p not in {hashfile,ROOT/'SHA256SUMS'})
lines=[digest(p)+'  '+__import__('os').path.relpath(p,hashfile.parent).replace('\\','/') for p in files]
hashfile.write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
root_hashfile=ROOT/'SHA256SUMS'
root_files=sorted(p for p in ROOT.rglob('*') if public(p) and p!=root_hashfile)
root_lines=[digest(p)+'  '+p.relative_to(ROOT).as_posix() for p in root_files]
root_hashfile.write_text('\n'.join(root_lines)+'\n',encoding='utf-8',newline='\n')
print('Packaged',len(source),'paper source files and manifest;',len(files),'public hashes.')
