import re 

x = [[-1] * 3] * 4 
x = [[-1 for i in range(3)] for j in range(4)]

print(x)
for j in range(3):
    for i in range(4):
        print(x[i][j], end='')
    print()
print()

x[1][2] = 2
    
for j in range(3):
    for i in range(4):
        print(x[i][j], end='')
    print()
