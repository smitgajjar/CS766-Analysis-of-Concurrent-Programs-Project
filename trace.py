import sys
import subprocess
import os
from pathlib import Path

def findAllPossibleOrders(adj, visited, n, indegree, n_globals):
	for u in range(n):
		if not visited[u] and indegree[u] == 0:
			visited[u] = True
			order.append(u)
			for v in adj[u]:
				indegree[v] -= 1

			findAllPossibleOrders(adj, visited, n, indegree, n_globals)
			visited[u] = False
			order.pop()
			for v in adj[u]:
				indegree[v] += 1

	if len(order) == n:
		l = [inverted_idx[order[i]] for i in range(n_globals, len(order))]
		prev_set_len = len(rf_ws_str_set)
		rf, ws = get_relations(l)
		rf_ws_str_set.add(''.join([a for l in rf for a in l])+''.join([a for l in ws for a in l]))
		if prev_set_len != len(rf_ws_str_set):
			trace_rf_ws.append([l, rf, ws])

def GenerateAllPossibleOrders(adj, n, n_globals):
	visited = [False] * n
	indegree = [0] * n

	for src in range(len(adj)):
		for dest in adj[src]:
			indegree[dest] += 1

	findAllPossibleOrders(adj, visited, n, indegree, n_globals)




def is_read(instr_str):
	return ('r' in instr_str)

def is_x_read(instr_str):
	return (is_read(instr_str) and instr_str[-1]=='x')

def is_y_read(instr_str):
	return (is_read(instr_str) and instr_str[-1]=='y')

def is_z_read(instr_str):
	return (is_read(instr_str) and instr_str[-1]=='z')

def is_x_write(instr_str):
	return (not is_read(instr_str) and 'x' in instr_str)

def is_y_write(instr_str):
	return (not is_read(instr_str) and 'y' in instr_str)

def is_z_write(instr_str):
	return (not is_read(instr_str) and 'z' in instr_str)

def is_in_different_process(instr_str1, instr_str2):
	if is_read(instr_str2):
		return instr_str1[0]!=instr_str2[0]
	return instr_str1[0]!='g' and instr_str1[0]!=instr_str2[0]


def get_relations(trace):
	prev_write_instr={'x':'gvx=0', 'y':'gvy=0', 'z':'gvz=0'}
	rf=[]
	ws=[]
	for i in range(len(trace)):
		if is_read(trace[i]):
			if is_x_read(trace[i]):
				rf.append([prev_write_instr['x'], trace[i]])
			elif is_y_read(trace[i]):
				rf.append([prev_write_instr['y'], trace[i]])
			elif is_z_read(trace[i]):
				rf.append([prev_write_instr['z'], trace[i]])
		else:
			if is_x_write(trace[i]):
				if is_in_different_process(prev_write_instr['x'], trace[i]):
					ws.append([prev_write_instr['x'], trace[i]])
				prev_write_instr['x'] = trace[i]
			elif is_y_write(trace[i]):
				if is_in_different_process(prev_write_instr['y'], trace[i]):
					ws.append([prev_write_instr['y'], trace[i]])
				prev_write_instr['y'] = trace[i]
			elif is_z_write(trace[i]):
				if is_in_different_process(prev_write_instr['z'], trace[i]):
					ws.append([prev_write_instr['z'], trace[i]])
				prev_write_instr['z'] = trace[i]

	rf.sort()
	ws.sort()
	return rf, ws




def check_condition(l, assert_stmt_str):
	trace1, rf1, ws1 = l 
	assert_conditions_true = are_assert_conditions_true(assert_stmt_str, trace1)
	if not assert_conditions_true:
		print("Error: Assertion Violation")
		print("Violating Trace: [",end='')
		
		for i in range(len(trace1)-1):
			print(trace1[i][2:],end=', ')
		print(trace1[-1][2:], end='')
		print(']', end=' ')

		if rf1:
			print('rf relation:[', end='')
			for i in range(len(rf1)-1):
				print('[{}, {}]'.format(rf1[i][0][2:], rf1[i][1][2:]), end=', ')
			print('[{}, {}]]'.format(rf1[-1][0][2:], rf1[-1][1][2:]), end=' ')

		if ws1:
			print('co relation:[', end='')
			for i in range(len(ws1)-1):
				print('[{}, {}]'.format(ws1[i][0][2:], ws1[i][1][2:]), end=', ')
			print('[{}, {}]]'.format(ws1[-1][0][2:], ws1[-1][1][2:]))
		return False
	return True
	


def are_assert_conditions_true(assert_stmt_str, trace1):
	f = open('temp.py', 'w')
	for instr_str in trace1:
		f.write('{}\n'.format(instr_str[2:]))
	f.write(assert_stmt_str)
	f.close()
	
	p = subprocess.Popen(['python3', 'temp.py'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
	return not p.communicate()[0]


def print_result(trace_rf_ws,A):
	if A==1:
		for l in trace_rf_ws:
			if not check_condition(l, assert_smt):
				if Path('temp.py').exists():
					os.remove('temp.py')
				return
	if Path('temp.py').exists():
		os.remove('temp.py')
	print('No of traces =', len(trace_rf_ws))
	counter=1
	for l in trace_rf_ws:
		trace1, rf1, ws1 = l
		print(counter,"-: Trace: [",end='')
		
		for i in range(len(trace1)-1):
			print(trace1[i][2:],end=', ')
		print(trace1[-1][2:], end='')
		print(']', end=' ')

		if rf1:
			print('rf relation:[', end='')
			for i in range(len(rf1)-1):
				print('[{}, {}]'.format(rf1[i][0][2:], rf1[i][1][2:]), end=', ')
			print('[{}, {}]]'.format(rf1[-1][0][2:], rf1[-1][1][2:]), end=' ')

		if ws1:
			print('co relation:[', end='')
			for i in range(len(ws1)-1):
				print('[{}, {}]'.format(ws1[i][0][2:], ws1[i][1][2:]), end=', ')
			print('[{}, {}]]'.format(ws1[-1][0][2:], ws1[-1][1][2:]))
			#print(ws1)
		counter += 1




def take_input():
	n = int(sys.stdin.readline())
	process = []
	for i in range(n):
		process.append((sys.stdin.readline().split(';'))[:-1])
		for j in range(len(process[i])):
			process[i][j] = str(i)+str(j)+process[i][j]
	assert_smt = ''
	A = int(sys.stdin.readline())
	if A==1:
		assert_smt = sys.stdin.readline()

	
	return process,assert_smt,A


def CreateGraph(process):
	has_x = False
	has_y = False
	has_z = False

	for i in range(len(process)):
		for j in range(len(process[i])):
			if 'x' in process[i][j]:
				has_x = True
			elif 'y' in process[i][j]:
				has_y = True
			elif 'z' in process[i][j]:
				has_z = True

	N = 0 # number of nodes in graph
	if has_x:
		idx['gvx=0'] = N
		N += 1

	if has_y:
		idx['gvy=0'] = N
		N += 1

	if has_z:
		idx['gvz=0'] = N
		N += 1

	n_globals = N
	for i in range(len(process)):
		for j in range(len(process[i])):
			idx[process[i][j]] = N
			N += 1

	for k in idx.keys():
		inverted_idx[idx[k]] = k


	adj = []
	for i in range(N):
		adj.append(list())

	for i in range(len(process)):
		for j in range(n_globals):
			adj[j].append(idx[process[i][0]])

	for i in range(len(process)):
		for j in range(1, len(process[i])):
			adj[idx[process[i][j-1]]].append(idx[process[i][j]])
	
	return adj, N, n_globals
		

trace_rf_ws = []
order = []
rf_ws_str_set=set()
idx={}
inverted_idx={}

if __name__=="__main__":

	process, assert_smt,A = take_input()
	adj,N,n_globals = CreateGraph(process)
	GenerateAllPossibleOrders(adj,N,n_globals)
	print_result(trace_rf_ws,A)
