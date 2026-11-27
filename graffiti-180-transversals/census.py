from pathlib import Path
import subprocess, sys
folder=Path(__file__).resolve().parent
for n in sys.argv[2:]:
    gen=subprocess.Popen([sys.argv[1],'-cq',n],stdout=subprocess.PIPE)
    scan=subprocess.run([str(folder/'.build/search')],stdin=gen.stdout,capture_output=True,text=True)
    gen.stdout.close()
    status=gen.wait()
    print('n',n,scan.stdout.strip(),flush=True)
    if scan.returncode or status:raise SystemExit(1)
