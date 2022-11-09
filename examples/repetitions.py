def repetitions(lines):
    for i, line in enumerate(lines):
        for j in range(i):
            if line == lines[j]:
                print(i, j, line)
                break

with open('kiwi_2.txt', "r") as f:
    lines = f.readlines()
    repetitions(lines)