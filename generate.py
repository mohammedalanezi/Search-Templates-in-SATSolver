import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "input.cnf")
output_path = os.path.join(script_dir, "output.txt")

kissat_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat") # Before testing: Update this to your sat solver's location 

start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0

clauses = []

if len(sys.argv) < 4:
	print("Usage: python3 generate.py <order> <symbol_count> <symbol_frequencies> [frequency_squares] [seed]\n") 
	sys.exit(1)

variableCount = 0

order = int(sys.argv[1])
symbol_count = int(sys.argv[2])
frequencies = []
frequency_squares = 4
seed = 0
if len(sys.argv) > 2:
	for i in range(min(symbol_count, len(sys.argv) - 3)):
		frequencies.append(int(sys.argv[i+3]))
if len(sys.argv) > 3 + symbol_count:
	frequency_squares = int(sys.argv[3 + symbol_count])
if len(sys.argv) > 4 + symbol_count:
	seed = int(sys.argv[4 + symbol_count])

if len(frequencies) < symbol_count:
	print(f"Error: Not enough frequencies given; got {len(frequencies)} symbol frequencies but need {symbol_count} (#symbol_frequencies < symbol_count)\n") 
	sys.exit(1)

def addClause(variables):
	if len(variables) == 0:
		return False
	clause = ""
	for v in variables:
		clause += str(v) + " "
	clauses.append(clause + "0")
	return True

def addImplicationClause(antecedent, consequent): # conjunction(AND) of all antecedental variables implies the disjunction(OR) of consequental variables, e.g. "x1 and .. and xn" implies "y1 or ... or yn"
	if len(antecedent) == 0 or len(consequent) == 0:
		return False
	clause = "" # X implies Y is equivalent to -X OR Y
	for x in antecedent:
		clause += str(-x) + " "
	for y in consequent:
		clause += str(y) + " "
	clauses.append(clause + "0")
	return True

def addOrthogonalityClauses(square1, square2, frequencies1, frequencies2):
	global variableCount, clauses
	
	for s in range(len(frequencies1)):
		for t in range(len(frequencies2)):
			expected_orthogonality = frequencies1[s] * frequencies2[t]
			
			pair_vars = []
			for x in range(order):
				for y in range(order):
					pair_var = variableCount + 1
					variableCount += 1
					pair_vars.append(pair_var)
					
					addImplicationClause([pair_var], [get1DIndex(square1, x, y, s)])
					addImplicationClause([pair_var], [get1DIndex(square2, x, y, t)])
					
					addImplicationClause([get1DIndex(square1, x, y, s), get1DIndex(square2, x, y, t)], [pair_var])
			
			addCardinalityClauses(pair_vars, expected_orthogonality, expected_orthogonality)

def addCardinalityClauses(variables, mininum, maximum): # <= maximum variables and >= minimum values are true (latin squares would use minimum = maximum = 1 for each symbol)
	global variableCount
	
	n = len(variables) # rows
	k = maximum + 1	   # columns
	l = mininum
	
	s = [] # Boolean counter variables, s[i][j] says at least j of the variables x1, ..., xi are assigned to true
	for i in range(n + 1):
		row = []
		for j in range(k + 1):
			variableCount += 1
			row.append(variableCount)
		s.append(row)
	
	for i in range(n+1):
		addClause([s[i][0]]) # 0 variables are always true of variables [x1, ..., xi]
	for j in range(1, k+1):
		addClause([-s[0][j]]) # j>=1 of nothing is always false
	for j in range(1, l+1):
		addClause([s[n][j]]) # at least minimum of [x0, ..., xi-1] are true
	for i in range(1, n+1):
		addClause([-s[i][k]]) # at most maximum of [x0, ..., xi-1] are true
		
	for i in range(1, n+1): # for each variable xi, propagate counts across the table
		for j in range(1, k+1):
			addImplicationClause([s[i-1][j]], [s[i][j]]) # If at least j of the first i-1 variables are true, then at least j of the first i variables are true
			addImplicationClause([variables[i-1], s[i-1][j-1]], [s[i][j]]) # If xi is true and at least j-1 of the first i-1 variables are true, then at least j of the first i variables are true
			if j <= l:
				addImplicationClause([s[i][j]], [s[i-1][j], variables[i-1]]) # If at least j of the first i variables are true, then either xi is true or at least j of the first i-1 variables were already true
				addImplicationClause([s[i][j]], [s[i-1][j-1]]) # If at least j of the first i variables are true, then at least j-1 of the first i-1 variables must be true

def getCombinations(totalList, array, n, currentRemovals): # n >= 0, generate all possible combinations from n choices
	if n == 0:
		totalList.append(currentRemovals)
	else: 
		for i in range(len(array)):
			tmpList = array[i + 1 : len(array)]
			removals = currentRemovals.copy()
			removals.append(array[i])
			getCombinations(totalList, tmpList, n - 1, removals)

def addXORClauses(chain): # create XOR clauses for given chain, should add 2^(len(chain) - 1) clauses for XOR
	for notCount in range(1, len(chain) + 1, 2):
		total = []
		getCombinations(total, list(range(len(chain))), notCount, [])
		for i in range(len(total)):
			tmpChain = chain.copy()
			for j in range(len(total[i])):
				tmpChain[total[i][j]] = -tmpChain[total[i][j]]
			addClause(tmpChain)

if __name__ == "__main__": # test script, This is a copy of my first frequency square encoding but with sinz cardinality encoding above
	tryTemplate = True

	def get1DIndex(l, r, c, s): # latin square, row, col, symbol, l = 0 or 1, 0 <= r, s, c <= n - 1
		return l * order * order * symbol_count + r * order * symbol_count + c * symbol_count + s + 1 # 1 to n^3

	def get4DIndex(v): 
		v = v - 1  # Make it 0-based
		l = v // (order * order * symbol_count)
		rem = v % (order * order * symbol_count)
		r = rem // (order * symbol_count)
		rem = rem % (order * symbol_count)
		c = rem // symbol_count
		s = rem % symbol_count
		return l, r, c, s # l = 0 or 1, 0 <= r, c, s <= n - 1

	variableCount = get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1) 
	for l in range(frequency_squares):
		for x in range(order):
			for y in range(order):
				# Each cell (x,y) has exactly one symbol
				cell_vars = [get1DIndex(l, x, y, z) for z in range(symbol_count)]
				addCardinalityClauses(cell_vars, 1, 1)
		
		if l >= 2 or not tryTemplate:
			for x in range(order):
				for z in range(symbol_count):
					# Each symbol z appears "some amount of times" in row x
					row_vars = [get1DIndex(l, x, y, z) for y in range(order)]
					addCardinalityClauses(row_vars, frequencies[z], frequencies[z])
			
			for y in range(order):
				for z in range(symbol_count):
					# Each symbol z appears "some amount of times" in column y
					col_vars = [get1DIndex(l, x, y, z) for x in range(order)]
					addCardinalityClauses(col_vars, frequencies[z], frequencies[z])
	
	if tryTemplate:
		for x in range(order):
			for y in range(order):
				if x < 4: 
					addClause([get1DIndex(1, x, y, 1)])
				else:
					addClause([get1DIndex(1, x, y, 0)])

				if y < 4:
					addClause([get1DIndex(0, x, y, 1)])
				else:
					addClause([get1DIndex(0, x, y, 0)])

				if x == y and x < 4:
					addClause([get1DIndex(2, x, y, 1)])
					addClause([get1DIndex(3, x, y, 1)])
				elif x < 4 and y < 4:
					addClause([get1DIndex(2, x, y, 0)])
					addClause([get1DIndex(3, x, y, 0)])
			
		for i in range(2, frequency_squares):
			for j in range(i + 1, frequency_squares):
				addOrthogonalityClauses(i, j, frequencies, frequencies)

		for x in range(order):
			for y in range(order):
				bits = []
				for l in range(frequency_squares):
					bits.append(get1DIndex(l, x, y, 1))
				addXORClauses(bits)
				
	with open(input_path, "w") as f:
		f.write(f"p cnf {variableCount} {len(clauses)}\n")
		f.write("\n".join(clauses))
			
	dimacs_elapsed = round((time.time() - start_time) * 100)/100
	print("Wrote DIMACS CNF file to:", input_path)  

	kissat_time = time.time() # wall time
	with open(output_path, "w") as out_file:
		commands = [kissat_path, input_path, "--seed=" + str(seed)]
		subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	kissat_elapsed = round((time.time() - kissat_time) * 100)/100
	print("Wrote Kissat output to:", output_path)
			
	result = [] # the resulting frequency square
	with open(output_path, "r") as f:
		satisfiable = None
		for l in range(frequency_squares):
			result.append([])
			for y in range(order):
				result[l].append([])
				for x in range(order):
					result[l][y].append(-1) # easily tells us if logic error occured by the existance of -1 symbol
		for line in f:
			if line.startswith("s "):
				if "UNSATISFIABLE" in line:
					satisfiable = "UNSAT"
				elif "SATISFIABLE" in line:
					satisfiable = "SAT"
			elif line.startswith("v "):
				values = line[2:].strip().split()
				for val in values:
					if val == '0': # end of variables
						continue
					val = int(val)
					if val > 0 and val <= get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1):
						l, r, c, s = get4DIndex(val)
						result[l][r][c] = s

		print("Result:", satisfiable)
		if satisfiable == "SAT":
			print("[",end="")
			for row in range(order):
				if row == 0:
					print("[",end="")
				else:
					print(" [",end="")
				for x in range(order):
					for l in range(frequency_squares):
						print(result[l][row][x], end='')
					if x == order - 1:
						if row == order - 1:
							print("]]", end='')
						else:
							print("],", end='')
					else:
						print(", ", end='')
				print(" ")
	print("Total elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
	print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
	print("     Kissat elapsed time:", kissat_elapsed, "seconds")

# cd /mnt/g/Code/sat\ solver\ stuff/search\ templates
