from z3 import *

x = [[Int("x[%d][%d]" % (i, j)) for j in range(3)] for i in range(3)]
y = Int("y")
s = Solver()
for i in range(3):
    for j in range(3):
        s.add(x[i][j] == 1)
s.add(y == Sum(tmp for tmp in x[0]))
r = s.check()
if r == sat:
    m = s.model()
    print(m[y].as_long())
else:
    print(r)
