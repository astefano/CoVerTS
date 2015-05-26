from z3 import *

def getII(F):
	 blockAnd = []
	 s = Solver()
	 s.add(F)
	 while True:
		 if s.check() == sat:
			 m = s.model()
			 # Create a new constraint the blocks the current model
			 block = []
			 blockOr = []
			 for d in m:
				 c = d()
				 block.append(c != m[d])
				 if m[d].sexpr() == 'true': 
					 blockOr.append(c)
				 # d is a declaration
				 # create a constant from declaration
			 if block != []:		
			 	s.add(Or(block))
			 if len(blockOr) > 1: 
			 	blockAnd.append(Or(blockOr))
			 elif len(blockOr) == 1:	
			 	blockAnd.append(blockOr[0])
		 else:
			 return And(blockAnd)

def getAllModels(F, lim):
	 result = []
	 s = Solver()
	 s.add(F)
	 i = 0
	 while i < lim:
		 i = i + 1
		 if s.check() == sat:
			 m = s.model()
			 result.append(m)
			 #printModel(m)	
			 block = []
			 for d in m:
				 c = d()
				 block.append(c != m[d])
				 #if block != []:		
			 s.add(Or(block))
		 else:
			 return result

def printModel(M):
	print "["
	for d in M: 
		if M[d].sexpr() != 'false':
			print "%s = %s" % (d.name(), M[d])
	print "]"

def printModels(models):
	for m in models:
		printModel(m)

#given a formula F and a model M, return F[M]
def subst(F, M):
	r = F
	for d in M: 
		if M[d].sort().sexpr() == 'Bool':
			r = substitute(r,((Bool(d.name()), BoolVal(str(M[d])))))
		elif M[d].sort().sexpr() == 'Int':
			r = substitute(r, ((Int(d.name()), IntVal(str(M[d])))))
	return r

def getUppaalQueryFromTempControlII(models):
	cn = 'Controller'
	tn = 'Train'
	gn = 'Gate'
	query = ''
	for m in models:
		qA = ''
		for d in m:
			if m[d].sexpr() == 'true':
				s = d.name() 						
				if s.startswith('C'):
					qA = qA + cn + '.' + s  + ' and '
				elif s in set(['is_down', 'is_up', 'coming_down', 'going_up']):
					qA = qA + gn + '.' + s  + ' and '
				else:		
					iS = s[-1]
					qA = qA + tn + '(' + iS + ').' + s[:-2] + ' and '
		query = query + ' or \n (' + qA[:-5] + ')'
	return 'A[] ( not(' + cn + '.C0) imply (' + query[4:] + ')'

def getUppaalQueryFromCEXWithHistory(model):
	cn = 'Controller'
	tn = 'Train'
	gn = 'Gate'
	qA = ''
	for d in model:
		s = d.name() 						
		#if a loc
		if model[d].sexpr() == 'true':
			if s.startswith('C'):
				qA = qA + cn + '.' + s  + ' and '
			elif s in set(['is_down', 'is_up', 'coming_down', 'going_up']):
				qA = qA + gn + '.' + s  + ' and '
			else:		
				iS = s[-1]
				qA = qA + tn + '(' + iS + ').' + s[:-2] + ' and '
		#if a clock
		elif model[d].sort().sexpr() == 'Int':
			if s.startswith('x'):
				index = s[-1]
				qA = qA + tn + '(' + index + ').x == ' + str(model[d]) + ' and '
			elif s == 'y':
				qA = qA + gn + '.y == ' + str(model[d]) + ' and '
			elif s == 'z': 
				qA = qA + cn + '.z == ' + str(model[d]) + ' and '
			#else it's a history clock	
			else:
				index = s[-1]
				if index == 'c':
					qA = qA + cn + '.' + s + ' == ' + str(model[d]) + ' and '
				elif index == 'g':
					qA = qA + gn + '.' + s + ' == ' + str(model[d]) + ' and '
				else:
					qA = qA + tn + '(' + index + ').' + s[:-1] + ' == ' + str(model[d]) + ' and '
	return 'A[] ( not(' + qA[:-5] + '))'

def getCEX(F):
    toSolve = Solver()
    toSolve.add(F)
    if toSolve.check() == sat:
        m = toSolve.model()
        printModel(m)
        print getUppaalQueryFromCEXWithHistory(m)
    else:
        print "no solution"

