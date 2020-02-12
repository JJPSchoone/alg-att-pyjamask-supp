from brial import *

declare_ring([Block('x',192),Block('k',288)],globals())
[Variable(i,r) for i in range(r.ngens())]
myM = [[0,1,3,8,13,18,19,24,25,26,30],[1,6,13,14,15,17,23,25,26,30,31],[8,10,13,14,15,16,19,20,22,25,28,30,31]]
constSet = BooleSet([Monomial(r)])
emptySet = constSet.subset1(0)

#apply Linear Layer and output in an other list
def applyL(mylist):
    newlist = []
    for i in range(3):
        for j in range(32):
            mypoly = r(0)
            for l in myM[i]:
                mypoly = mypoly + mylist[((l+j)%32)+i*32]
            newlist.append(mypoly)
    return newlist

#Apply Sbox Layer in place
def applyS(mylist):
    for i in range(32):
        X0 = mylist[i]
        X1 = mylist[i+32]
        X2 = mylist[i+64]
        mylist[i] = (X0 * X2) + X1
        mylist[i+32] = (X0 * X1) + X0 + X1 + X2 
        mylist[i+64] = (X1 * X2) + X0 + X1

#initiate with trick depicted in Section 6
def initiateState():
    l = []
    for i in range(32):
        mypoly = k(i)*x(64+i)+k(64+i)*x(i)
        l.append(mypoly)
    for i in range(32):
        mypoly = k(i)*x(32+i)+k(32+i)*x(i)
        l.append(mypoly)
    for i in range(32):
        mypoly = k(32+i)*x(64+i)+k(64+i)*x(32+i)
        l.append(mypoly)
    l = applyL(l)
    for i in range(96):
        mypoly = x(96+i)
        l[i] = x(96+i)  + l[i]
    return l

#Help to verify correctness
def initiateVerify():
	l = []
	for i in range(96):
		mypoly = x(i)
		l.append(mypoly)
	return l

#deletes monomials in key variables only
def deleteAlonePrivate(mySet):
	S = mySet
	for i in range(192):
		print(i)
		S = S.subset0(i)
	return mySet.diff(S)

#gives number of monomials needed to evaluate
def quotientPrivate(mySet):
	result = mySet
	for i in range(288):
		print(i)
		result = (result.subset1(i+192)).union(result.subset0(i+192))
	return result.diff(constSet)

#gives number of monomials after evaluation
def quotientPublic(mySet):
	result = mySet
	for i in range(192):
		print(i)
		result = (result.subset1(i)).union(result.subset0(i))
	return result.diff(constSet)

#Output bit with the less number of monomials (TODO again for full Pyj)
def outputBestOne(State):
	j = 0
	tmp = State[j].size_double()
	for i in range(1,96):
		S = State[i]
		size1 = S.size_double()
		if size1<tmp :
			tmp = size1
			j = i
	return j

#Construct the list of guess to choose in order to reduce the complexity
def constructList(State):
	S = State
	L = []
	while S.size_double()>448:
		j = 192
		newS = ((S.subset0(192)).union(S.subset1(192))).diff(constSet)
		tmp = newS.size_double()
		for i in range(1,288):
			myS = ((S.subset0(192+i)).union(S.subset1(192+i))).diff(constSet)
			size = myS.size_double()
			if tmp>size:
				tmp = size
				j = i+192
		S = ((S.subset0(j)).union(S.subset1(j))).diff(constSet)
		L.append(j-192)
	print (S.size_double())
	return L

#output all variables that effectivily appear
def list_variables(State):
	L = []
	for i in range(480):
		tmp = State.subset1(i)
		if not (tmp.empty()):
			L.append(i)
	return L

#in order to do partial sums
def moyenne_reevaluation(state,mylist):
	r = 0.
	#firt 96 bits always guessed for 2.5 rounds
	for i in range(96):
		tmp = (state.subset1(i+192)).size_double()
		r += tmp
	for i in mylist:
		tmp = (state.subset1(i+192)).size_double()
		r += tmp
	return r

State = initiateState()
#add k1
for i in range(96):
	p = k(96+i)
	State[i] = State[i] + p

for i in range(96):
	print(State[i])

applyS(State)

def transforminset(s):
	l = []
	for i in range(96):
		l.append(s[i].set())
	return l

Statesets = transforminset(State)
#Here it's 1.5 rounds
j = outputBestOne(Statesets)
S = Statesets[j]
print("min number of monomials for 1.5 rounds:",S.size_double(),"at bit",j)
S = deleteAlonePrivate(S)
print("delete alone key monomials:",S.size_double())
Eval = quotientPrivate(S)
print("Cost of Evaluation:",Eval.size_double())
System = quotientPublic(S)
print("Cost of Solving:",System.size_double())
myL = list_variables(System)
print(myL)
print(len(myL))
L = constructList(System)
print(L)
print(len(L))

def secondtrick():
	mixedState = initiateVerify()
	tmp = initiateState()
	for i in range(32):
		s0 = k(96+i)
		s1 = k(96+32+i)
		s2 = k(96+64+i)
		mixedState[i] = (s0 * tmp[64+i]) + (s2 * tmp[i])
		mixedState[32+i] = (s0 * tmp[32+i]) + (s1 * tmp[i])
		mixedState[64+i] = (s2 * tmp[32+i]) + (s1 * tmp[64+i])
	applyS(tmp)
	for i in range(96):
		tmp[i] = tmp[i] + mixedState[i]
	return applyL(tmp)

#second trick
State = secondtrick()

#Add k_2
for j in range(96):
	mypoly = k(j+192)
	State[j] = State[j] + mypoly

#Expression of bit 32 (bestOne)
Poly = (State[0]*State[32]) + State[0] + State[32] + State[64]
FinalState = Poly.set()
print("min number of monomials for 2.5 rounds:",FinalState.size_double(),"at bit 32")
FinalState = deleteAlonePrivate(FinalState)
print("delete alone key monomials:",FinalState.size_double())
Eval25 = quotientPrivate(FinalState)
print("Cost of Evaluation:",Eval25.size_double())
System25 = quotientPublic(FinalState)
print("Cost of Solving:",System25.size_double())

#print list of variables that appear
print(len(list_variables(System25)))

System25bis = System25
#guess all first 96 bits
for i in range(96):
	print(i)
	System25bis = (System25bis.subset1(i+192)).union(System25bis.subset0(i+192))

#print remaining variables that appear
print(list_variables(System25bis))

lastL = constructList(System25bis)
evalGuess = moyenne_reevaluation(System25,lastL)

print(evalGuess)

