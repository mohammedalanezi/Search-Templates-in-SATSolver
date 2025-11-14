import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "input.cnf")
output_path = os.path.join(script_dir, "output.txt")

kissat_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0

clauses = []

variableCount = 0

order = 10
symbol_count = 2
frequencies = [6, 4]
frequency_squares = 4
seed = 0

def addClause(variables):
	if len(variables) == 0:
		return False
	clause = ""
	for v in variables:
		clause += str(v) + " "
	clauses.append(clause + "0")
	return True

def addImplicationClause(antecedent, consequent): # conjunction(AND) of all antecedental variables implies the disjunction(OR) of consequental variables, e.g. "x1 and .. and xn" implies "y1 or ... or yn"
	clause = "" # X implies Y is equivalent to -X OR Y
	for x in antecedent:
		clause += str(-x) + " "
	for y in consequent:
		clause += str(y) + " "
	clauses.append(clause + "0")
	return True

def addOrthogonalityClauses(square1, square2, frequencies1, frequencies2):
	global variableCount, clauses

	freq_pairs = {} # [position] = (auxiliary, point)

	for s in range(len(frequencies1)):
		for t in range(len(frequencies2)):
			expected_orthogonality = frequencies1[s] * frequencies2[t]
			
			point = (s, t)
			point_pairs = []

			for x in range(order):
				for y in range(order):
					if not ((x,y) in freq_pairs):
						freq_pairs[(x, y)] = {}
					pair_var = variableCount + 1
					variableCount += 1
					point_pairs.append(pair_var)
					freq_pairs[(x, y)][point] = pair_var
					
					addImplicationClause([pair_var], [get1DIndex(square1, x, y, s)])
					addImplicationClause([pair_var], [get1DIndex(square2, x, y, t)])
					
					addImplicationClause([get1DIndex(square1, x, y, s), get1DIndex(square2, x, y, t)], [pair_var])
			addCardinalityClauses(point_pairs, expected_orthogonality, expected_orthogonality) # likely unneeded if tryTemplate is true
				
	if tryTemplate: # LEMMA 3.2 II and IV, TODO: merge these into fewer for loops
		for x in range(4):
			#if (s == 0 and t == 1) or (s == 1 and t == 0):
			for i in range(2):
				relation_ii_row = []
				for y in range(4,10):
					relation_ii_row.append(freq_pairs[(x, y)][(i, 1 - i)])
				addCardinalityClauses(relation_ii_row, 3, 3)
				
				relation_ii_col = []
				for y in range(4,10):
					relation_ii_col.append(freq_pairs[(y, x)][(i, 1 - i)])
				addCardinalityClauses(relation_ii_col, 3, 3)
		for x in range(4,10): 
			#if (s == 1 and t == 1):
			relation_iv_row = []
			for y in range(4,10):
				relation_iv_row.append(freq_pairs[(x, y)][(1, 1)])
			addCardinalityClauses(relation_iv_row, 2, 2)
			
			relation_iv_col = []
			for y in range(4,10):
				relation_iv_col.append(freq_pairs[(y, x)][(1, 1)])
			addCardinalityClauses(relation_iv_col, 2, 2)
			
			#elif (s == 0 and t == 0):
			relation_iv_row = []
			for y in range(4,10):
				relation_iv_row.append(freq_pairs[(x, y)][(0, 0)])
			addCardinalityClauses(relation_iv_row, 4, 4)
			
			relation_iv_col = []
			for y in range(4,10):
				relation_iv_col.append(freq_pairs[(y, x)][(0, 0)])
			addCardinalityClauses(relation_iv_col, 4, 4)
			
			#elif (s == 1 and t == 0) or (s == 0 and t == 1):
			for i in range(2):
				relation_iv_row = []
				for y in range(10):
					relation_iv_row.append(freq_pairs[(x, y)][(i, 1 - i)])
				addCardinalityClauses(relation_iv_row, 2, 2)
				
				relation_iv_col = []
				for y in range(10):
					relation_iv_col.append(freq_pairs[(y, x)][(i, 1 - i)])
				addCardinalityClauses(relation_iv_col, 2, 2)

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

def addLexicographicalOrder(a, b): # lexico ordering
			# for any 2 vectors in the same sections
			# a is vector 1 and b is vector 2 
			# a0 = 1 => b0 = 1, equiv to, b0 = 0 => a0 = 0 (contrapositive)
			# a0 = b0 => -a1 or b1 				(2 cases a0 and b0 = 0 and a0 and b0 = 1)
			# a0 = b0 and a1 = b1 => -a2 or b2 	(4 cases, a0 and b0 = 0, a0 and b0 = 1, a1 and b1 = 0, a1 and b1 = 1)
	addImplicationClause([a[0]], [b[0]])
	for i in range(2):
		parityA = i * 2 - 1
		addImplicationClause([parityA * a[0], parityA * b[0]], [-a[1], b[1]])
		for j in range(2):
			parityB = j * 2 - 1
			addImplicationClause([parityA * a[0], parityA * b[0], parityB * a[1], parityB * b[1]], [-a[2], b[2]])

if __name__ == "__main__": # test this with cadical exhauste, its open sourced on github
	tryTemplate = True

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

	variableCount = get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1) 
	for l in range(frequency_squares):
		if l >= 2 or not tryTemplate:
			for x in range(order):
				for z in range(symbol_count): # could reduce to just constraint one of the frequencies
					# Each symbol z appears "some amount of times" in row x
					row_vars = [get1DIndex(l, x, y, z) for y in range(order)]
					addCardinalityClauses(row_vars, frequencies[z], frequencies[z])
			
			for y in range(order):
				for z in range(symbol_count):
					# Each symbol z appears "some amount of times" in column y
					col_vars = [get1DIndex(l, x, y, z) for x in range(order)]
					addCardinalityClauses(col_vars, frequencies[z], frequencies[z])
	
	if tryTemplate:
		a = [get1DIndex(2, y+1, 5, 1) for y in range(3)]
		b = [get1DIndex(2, y+1, 6, 1) for y in range(3)]
		addLexicographicalOrder(a, b)
		
		a=[get1DIndex(2, y+1, 7, 1) for y in range(3)]
		b=[get1DIndex(2, y+1, 8, 1) for y in range(3)]
		c=[get1DIndex(2, y+1, 9, 1) for y in range(3)]
		addLexicographicalOrder(a, b)
		addLexicographicalOrder(b, c)
		#addLexicographicalOrder(a, c) # not needed

		for i in range(2):
			a=[get1DIndex(2, 4 + 3*i, x+1, 1) for x in range(3)]
			b=[get1DIndex(2, 5 + 3*i, x+1, 1) for x in range(3)]
			c=[get1DIndex(2, 6 + 3*i, x+1, 1) for x in range(3)]
			addLexicographicalOrder(a, b)
			addLexicographicalOrder(b, c)
			#addLexicographicalOrder(a, c) # not needed

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
				pass #addXORClauses(bits) # not needed
		
		for x in range(4,7):
			addClause([get1DIndex(3, 0, x, 1)])
			addClause([get1DIndex(3, x, 0, 1)])
			
		for x in range(7,10):
			addClause([get1DIndex(2, 0, x, 1)])
			addClause([get1DIndex(2, x, 0, 1)])
		addClause([get1DIndex(3, 1, 4, 1)])
		addClause([get1DIndex(2, 2, 4, 1)])
		addClause([get1DIndex(2, 3, 4, 1)])
		
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
	print("Wrote output to:", output_path)

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
					if abs(val) <= get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1):
						l, r, c = get4DIndex(abs(val))
						s = 0
						if val > 0:
							s = 1
						result[l][c][r] = s
		print("Result:", satisfiable)
		if satisfiable == "SAT":
			print("[",end="")
			for row in range(order):
				if tryTemplate and row==4:
					print("\n", end='')
				if row == 0:
					print("[",end="")
				else:
					print(" [",end="")
				for x in range(order):
					if tryTemplate and x==4:
						print(" ", end='')
					for l in range(0, frequency_squares):
						print(result[l][row][x], end='')
					if x == order - 1:
						if row == order - 1:
							print("]]", end='')
						else:
							print("],", end='')
					else:
						print(", ", end='')
				print(" ")

# cd /mnt/g/Code/sat\ solver\ stuff/search\ templates