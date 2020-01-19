from z3 import *

x = 1

y = Int("y")
z = Int("z")

s = Solver()

s.add(If(x == 1, y == 1, y ==0))
x = 0
s.add(If(x == 1, z == 1, z ==0))

s.check()
model = s.model()
print(model[y].as_long())
print(model[z].as_long())
