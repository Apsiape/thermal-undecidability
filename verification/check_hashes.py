"""Verify SHA256SUMS using the Python standard library."""
from pathlib import Path
import hashlib

root=Path(__file__).resolve().parent
count=0
for line in (root/"SHA256SUMS").read_text(encoding="utf-8").splitlines():
    expected,name=line.split("  ",1)
    actual=hashlib.sha256((root/name).read_bytes()).hexdigest()
    assert actual==expected, "Hash mismatch: "+name
    count+=1
print("Verified",count,"SHA-256 hashes.")
