import os
import time
import pynauty

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)
solution_set_path = os.path.join(script_dir, "solution set.txt")

start_time = time.time()

certificates = []
order = 10

def get1DIndex(l, r, c, s):
    index = 4 * order * r 
    index += 4 * c 
    index += l + 1
    if s == 0:
        index = -index
    return index

def get4DIndex(v): 
    v = v - 1 
    r = v // (4 * order) 
    rem = v % (4 * order)
    c = rem // 4
    rem = rem % 4
    l = rem
    return l, r, c

def display_line(line):
    for i in range(len(line)):
        l, r, c = get4DIndex(line[i])
        print(f"{line[i]} = [{l}, {r}, {c}],", end=" ")
    print("")

def display_template(template):
    print("[",end="")
    for row in range(order):
        if row==4:
            print("\n", end='')
        if row == 0:
            print("[",end="")
        else:
            print(" [",end="")
        for x in range(order):
            if x==4:
                print(" ", end='')
            for l in range(2, 4):
                print(template[l][row][x], end='')
            if x == order - 1:
                if row == order - 1:
                    print("]]", end='')
                else:
                    print("],", end='')
            else:
                print(", ", end='')
        print(" ")

def create_template(line):
    template = []
    for l in range(4): # we only care about the 2 frequency classes (XX**)
        template.append([])
        for y in range(order):
            template[l].append([])
            for x in range(order):
                template[l][y].append(-1)
    for j in range(4 * order * order):
        i = j + 1
        l, r, c = get4DIndex(i)
        s = 0
        if (len(line) == 400 and line[i-1] > 0) or i in line:
            s = 1
        template[l][c][r] = s
    return template

def create_graph(template):
    vertex_count = order*order + order*2 + 4 + 4 # 100 points, 10 rows and 10 columns, 4 symbols, 4 "pivot" vertices [R,C,S1,S2]
    
    point_count = order * order - 1
    R = point_count + order*2 + 4 + 1
    C = point_count + order*2 + 4 + 2
    S1 = point_count + order*2 + 4 + 3
    S2 = point_count + order*2 + 4 + 4

    adjacency_dict = {}
    for i in range(vertex_count):
        adjacency_dict[i] = []
    
    def add_vertex(id_from, id_to):
        adjacency_dict[id_from].append(id_to)
        adjacency_dict[id_to].append(id_from)

    for r in range(order):
        for c in range(order):
            symbol1 = template[2][c][r]
            symbol2 = template[3][c][r]
            id = r * 10 + c # x_{r,c}                               #   0 -  99
            add_vertex(id, point_count + r + 1)                     # 100 - 109
            add_vertex(id, point_count + order + c + 1)             # 110 - 119
            add_vertex(id, point_count + order*2 + symbol1 + 1)     # 120 - 121
            add_vertex(id, point_count + order*2 + 2 + symbol2 + 1) # 122 - 123
        
        add_vertex(point_count + r + 1, R) # r_i to R
        add_vertex(point_count + order + r + 1, C) # c_i to C

    add_vertex(point_count + order*2 + 1, S1) # s1_{0} to S1
    add_vertex(point_count + order*2 + 2, S1) # s1_{1} to S1
    add_vertex(point_count + order*2 + 3, S2) # s2_{0} to S2
    add_vertex(point_count + order*2 + 4, S2) # s2_{1} to S2

    vertex_coloring = [
        set(range(order*order + order*2 + 4)), # GREY
        set([R, C]), # RED
        set([S1, S2])  # BLUE
    ]

    return pynauty.Graph(vertex_count, False, adjacency_dict, vertex_coloring)

with open(solution_set_path, "r") as f:
    cert_count = 0
    line_count = 0
    for line in f:
        line_count = line_count + 1
        line = line.strip()
        line = line[16:-1] # skip trailing zeros and starting statements
        line = [(int(x)) for x in line.split()] # Converts line into list of variables
        template = create_template(line)
        graph = create_graph(template)
        cert = pynauty.certificate(graph)
        if cert not in certificates:
            certificates.append(cert)
            cert_count = cert_count + 1
            if cert_count % 100 == 0:
                print(f"new certificate, #{cert_count}")
        if line_count % 10000 == 0:
            print(f"current line: {line_count}")
        if line_count == 50:
            print(graph)

print(len(certificates))

print("Total elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
