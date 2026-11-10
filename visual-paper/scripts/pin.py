from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent.parent
files={}
for folder in ['source/paper','source/repository']:
 for path in sorted((root/folder).rglob('*')):
  if path.is_file() and path.suffix not in ['.log','.out','.toc','.synctex','.gz']:
   files[str(path.relative_to(root))]=hashlib.sha256(path.read_bytes()).hexdigest()
lock={'paper':{'arxiv':'2407.12372v2','source_url':'https://arxiv.org/src/2407.12372v2','retrieved':'2026-11-09','aux':'derived by pdflatex from pinned TeX'},'lean':{'repository':'https://github.com/svaiter/HardnessBilevelProgramming','commit':'d1032f4c70da9b037605c2f444ce2450900e5a76'},'anchor_offsets':'Unicode codepoints, start inclusive / end exclusive','files':files}
(root/'SOURCE.lock').write_text(json.dumps(lock,indent=2)+'\n')
