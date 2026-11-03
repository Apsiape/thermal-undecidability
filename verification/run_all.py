"""Run every standalone review script and the independent exact checker.

Commands use this interpreter and paths relative to this directory. Results are
written to a new runs/run-* directory (or a fresh --output directory). Import-only common.py is not a script.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess, sys, time, json, platform, argparse, tempfile, os, hashlib

ROOT=Path(__file__).resolve().parent
JOBS=[
    "exact_checks.py",
    "uniqueness/check_constants.py",
    "uniqueness/check_lw.py",
    "uniqueness/check_q1681.py",
    "potts/collision_checks.py",
    "potts/fk_q9_checks.py",
    "potts/exact_q9_checks.py",
    "fk_route/claim2_identities.py",
    "fk_route/counterexample27.py",
    "fk_route/dobrushin_check.py",
    "fk_route/extra_checks.py",
    "fk_route/fkg_tests.py",
    "fk_route/surj_decide_1d.py",
    "magnetic/sec2_checks.py",
    "magnetic/sec3_checks.py",
    "magnetic/sec3_run2.py",
    "magnetic/sec3_torus33.py",
    "magnetic/sec4_boundary_layer.py",
    "magnetic/sec4_checks.py",
    "magnetic/sec44_criticality.py",
]


def run(name):
    t=time.monotonic()
    result=subprocess.run([sys.executable,"-u",str(ROOT/name)],cwd=ROOT,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                          encoding="utf-8",errors="replace")
    out=result.stdout.replace(str(ROOT),"verification").replace(str(ROOT).replace("\\","/"),"verification")
    (OUT/"logs"/(name.replace("/","__")+".log")).write_text(out,encoding="utf-8",newline="\n")
    row={"script":name,"exit_code":result.returncode,"seconds":round(time.monotonic()-t,3),
         "source_sha256":hashlib.sha256((ROOT/name).read_bytes()).hexdigest()}
    print(json.dumps(row),flush=True)
    return row


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,help="Fresh output directory; must not already exist")
    args=parser.parse_args()
    if args.output:
        OUT=args.output.resolve()
        OUT.mkdir(parents=True,exist_ok=False)
    else:
        (ROOT/"runs").mkdir(exist_ok=True)
        OUT=Path(tempfile.mkdtemp(prefix="run-",dir=ROOT/"runs"))
    (OUT/"logs").mkdir()
    os.environ["PYTHONDONTWRITEBYTECODE"]="1"
    print("Fresh replay output:",OUT,flush=True)
    versions={"python":platform.python_version()}
    for module in ["numpy","scipy","sympy","networkx","mpmath"]:
        m=__import__(module); versions[module]=m.__version__
    (OUT/"versions.json").write_text(json.dumps(versions,indent=2)+"\n",encoding="utf-8",newline="\n")
    with ThreadPoolExecutor(max_workers=2) as pool:
        rows=list(pool.map(run,JOBS))
    (OUT/"run-results.json").write_text(json.dumps(rows,indent=2)+"\n",encoding="utf-8",newline="\n")
    assert all(r["exit_code"]==0 for r in rows), "At least one script failed; inspect logs"
    print("All 20 standalone scripts completed with exit code zero.",flush=True)
