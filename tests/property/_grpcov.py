import warnings, re, collections
warnings.filterwarnings("ignore")
from hypothesis import settings, HealthCheck, given
from strategies import programs_with_locals, source_with_locals
from oracle import dump_source
srcs=[]
@settings(max_examples=600, database=None, deadline=None, suppress_health_check=list(HealthCheck))
@given(programs_with_locals())
def collect(pl):
    prog,pro=pl; srcs.append(source_with_locals(dump_source(prog),pro))
collect()
blob="\n".join(srcs)

loc = collections.Counter()
for m in re.finditer(r"^\s+(u?int\d+) ([^;]+);", blob, re.M):
    loc[len(m.group(2).split(","))] += 1
gl = collections.Counter()
for m in re.finditer(r"^global (?:u?int\d+ )?([^;]+);", blob, re.M):
    gl[len(m.group(1).split(","))] += 1
fm = collections.Counter()
for m in re.finditer(r"^(?:void|u?int\d+) \w+\(([^)]*)\)", blob, re.M):
    a=m.group(1).strip(); fm[0 if not a else len(a.split(","))] += 1
ac = collections.Counter()
for m in re.finditer(r"(?<![\w])(?:\w+ := )?(?:f|g|helper)\(([^()]*)\)", blob):
    a=m.group(1).strip(); ac[0 if not a else len(a.split(","))] += 1

print("locals per decl group :", dict(sorted(loc.items())))
print("globals per decl      :", dict(sorted(gl.items())))
print("formals per proc      :", dict(sorted(fm.items())))
print("actuals per call      :", dict(sorted(ac.items())))
print("programs:", len(srcs))
