# Information:
# 	Accompying paper has more information on usage and includes references.
# 	Some of the variable and function names don't make sense as I have been building ontop of the same code for a long time as my research progressed.
#   And I can't be bothered to go over all of it and change it again. CPU doesn't care about variable names.
#
# Author: Essbee Vanhoutte 
# License type: Whatever, don't care, we live in the information age, not the copyright age.
import sys
import time
import sympy
import multiprocessing
import random
from timeit import default_timer
import itertools
from sage import *
import time
import copy
from bisect import bisect_left
import traceback
import argparse


##See chapter V of paper for description
##Settings##
method="LLL" 
strat=1 
key=0
keysize=14
aidlen=4
cores=16
mode=1
custom_mode=10000 

##Algorithm parameters
#constraints
g_cmult=16
g_cmult_max=200
g_cmult_inc=8
g_climit=5
g_climit_max=30
g_climit_inc=4
g_constr_min=0 #Only used with g_use_aid_cols
g_constr_max=4 #Only used with g_use_aid_cols
#Deletion
g_maxdepth=20 #Increases speed a the cost of precision
g_deletion_amount=10 #Increases speed a the cost of precision
g_deletion_mode=1 #Set to 0 to increase speed at the cost of precision
#Lifting (code is unoptimized for heavy lifting)
g_liftlimit=3
g_lift_for_2=16
g_lift_for_3=2 
g_lift_for_others=2 
g_lift_threshold=3
g_use_aid_cols=0 
#Other 
g_include_unmerged_col=0 
g_mod_red_amount=6 
g_merged_aid_list=2 

##Debug settings##
show=0
debug=0
printcols=60

##Define custom factors (mainly for debugging)
g_enable_custom_factors=0
g_p=32587
g_q=31543

##Do not touch unless needed##
upperweight=1
scalar=10000000000 #Set to smaller value when using the show setting

##Key gen function##
def power(x, y, p):
    res = 1;
    x = x % p;
    while (y > 0):
        if (y & 1):
            res = (res * x) % p;
        y = y>>1; # y = y/2
        x = (x * x) % p;
    return res;

def miillerTest(d, n):
    a = 2 + random.randint(1, n - 4);
    x = power(a, d, n);
    if (x == 1 or x == n - 1):
        return True;
    while (d != n - 1):
        x = (x * x) % n;
        d *= 2;
        if (x == 1):
            return False;
        if (x == n - 1):
            return True;
    # Return composite
    return False;

def isPrime( n, k):
    if (n <= 1 or n == 4):
        return False;
    if (n <= 3):
        return True;
    d = n - 1;
    while (d % 2 == 0):
        d //= 2;
    for i in range(k):
        if (miillerTest(d, n) == False):
            return False;
    return True;

def generateLargePrime(keysize = 1024):
   while True:
      num = random.randrange(2**(keysize-1), 2**(keysize))
      if isPrime(num,4):
         return num

def findModInverse(a, m):
   if gcd(a, m) != 1:
      return None
   u1, u2, u3 = 1, 0, a
   v1, v2, v3 = 0, 1, m
   while v3 != 0:
      q = u3 // v3
      v1, v2, v3, u1, u2, u3 = (u1 - q * v1), (u2 - q * v2), (u3 - q * v3), v1, v2, v3
   return u1 % m

def generateKey(keySize):
   while True:
       p = generateLargePrime(keySize)
       print("[i]Prime p: "+str(p))
       q=p
       while q==p:
           q = generateLargePrime(keySize)
       print("[i]Prime q: "+str(q))
       n = p * q
       print("[i]Modulus (p*q): "+str(n))
       count=65537
       e =count
       if gcd(e, (p - 1) * (q - 1)) == 1:
           break

   phi=(p - 1) * (q - 1)
   d = findModInverse(e, (p - 1) * (q - 1))
   publicKey = (n, e)
   privateKey = (n, d)
   print('[i]Public key - modulus: '+str(publicKey[0])+' public exponent: '+str(publicKey[1]))
   print('[i]Private key - modulus: '+str(privateKey[0])+' private exponent: '+str(privateKey[1]))
   return (publicKey, privateKey,phi,p,q)
##END KEY GEN##

def formal_deriv(y,x):
	result=(2*x)+(y)
	return result

def find_r(mod,total):
	mo,i=mod,0
	while (total%mod)==0:
		mod=mod*mo
		i+=1
	return i

def find_all_solp(n,start,limit):
	##This code is shit, if lifting takes too long, blame this function.
	rlist=[]	
	if start == 2:
		rlist=[[0,1]]
	else:
		i=0
		while i<start:
			if squareRootExists(n,start,i):
				temp=find_solution_x(n,start,i)
				rlist.append(temp[0])
			i+=1
	newlist=[]
	mod=start**2
	g=0
	while g<limit-1:
		rlist2=[]
		for i in rlist:
			if i[1]== -1:
				rlist2.append([i[0],-1,i[2]])
				continue
			j=0
			while j<len(i)-1:
				j+=1
				x=i[j]
				y=i[0]
				while 1:
					xo=x	
					while 1:
						test,test2=equation(y,x,n,mod)
						if test == 0:
							b=0
							while b<len(rlist2):
								if rlist2[b][0] == y and rlist2[b][1] != -1:
									rlist2[b].append(x)
									b=-1
									break
								b+=1	
							if b!=-1:		
								rlist2.append([y,x])
						x+=mod//start
						if x>mod-1:
							break
					x=xo	
					y+=mod//start	
					if y>mod-1:
						break
			b=0
			while b<len(rlist2):
				if rlist2[b][1] != -1:
					x=rlist2[b][1]
					y=rlist2[b][0]
					re=formal_deriv(y,x)
					r=find_r(start,re)
					ceiling=(start*r)+1
					ceiling=start**ceiling
					if mod < ceiling:
						b+=1
						continue	
					rlist2[b]=[]
					rlist2[b].append(y)
					rlist2[b].append(-1)
					rlist2[b].append(ceiling)
				b+=1	
		rlist=rlist2.copy()	
		mod*=start
		g+=1
	fe=[]
	
	for i in rlist2:
		if i[0] not in fe:
			fe.append(i[0])
			if i[1]==-1:
				y=i[0]
				while 1:
					y+=i[2]
					if y<(mod//start):
						fe.append(y)
					else:
						break	
	newlist.append(mod//start)
	fe.sort()
	newlist.append(fe)	
	return newlist

def take_closest(myList,myNumber):
	pos=bisect_left(myList,myNumber)
	if pos==len(myList):
		return pos-1
	return pos

def equation(y,x,n,mod):
	rem=(x**2)+y*-x+n
	rem2=rem%mod
	return rem2,rem  

def legendre(a, p):
    return pow_mod(a,(p-1)//2,p) 

def squareRootExists(n,p,b):
	b=b%p
	c=n%p
	bdiv = (b*inverse(2,p))%p
	alpha = (pow_mod(bdiv,2,p)-c)%p
	if alpha == 0:
		return 1
	
	if legendre(alpha,p)==1:
		return 1
	return 0

def inverse(a, m):
   if gcd(a, m) != 1:
      return None
   u1,u2,u3 = 1,0,a
   v1,v2,v3 = 0,1,m
   while v3 != 0:
      q = u3//v3
      v1,v2,v3,u1,u2,u3=(u1-q*v1),(u2-q*v2),(u3-q*v3),v1,v2,v3
   return u1%m

def pow_mod(base, exponent, modulus):
    return pow(base,exponent,modulus)   
 
def get_primes(start,stop):
	return list(sympy.sieve.primerange(start,stop))

def find_sol_for_p(n,p):
	rlist=[]
	y=0
	while y<p:
			if squareRootExists(n,p,y):
				rlist.append(y)
			y+=1
	return rlist

def min_value(n,a):
	sr=round(n**0.5)
	sr=sr-a
	sr*=2
	return sr

def find_solution_x(n,mod,y):
	##to do: can use tonelli if this ends up taking too long
	rlist=[]
	x=0
	while x<mod:
		test,test2=equation(y,x,n,mod)
		if test == 0:
			rlist.append([y,x])		
		x+=1
	return rlist

def normalize_sols(n,sum1):
	if strat == 1:
		sum1=square_sols(sum1)
	sum1=rebase(sum1)	
	sum1,total=create_partial_results(sum1)
	return sum1,total

def init_matrix(size,upperweight,length):
	M = []
	for i in range(size):
		arr = [0 for _ in range(length)]
		arr[i]=upperweight
		if i == size - 1:
			arr = [1/2 for _ in range(length)]
		M.append(arr)
	return M

def total_list_length(list1):
	listlen=0
	for i in list1:
		listlen+=len(i)
	return listlen

def combine(list3,modulus,split,totalmod,invb):
	list1=copy.deepcopy(list3)
	list2=[]
	i=0
	while i < len(list1):
		j=0
		parity=1
		if split ==1:
			if i%2 == 1:
				parity = -1
		while j < len(list1[i]):
			if invb ==1:
				inv=inverse(modulus[(i+1)%2],modulus[i])
				temp=(list1[i][j]*inv*modulus[(i+1)%2])%totalmod
			else:
				temp=list1[i][j]
			list2.append(temp*parity)
			j+=1
		i+=1
	return list2

def addcolumn(M,list1,totalmod,target,offset,upperweight,ceiling,split):	
	i=0
	while i < len(M):
		if i == len(list1):
			if offset ==0:
				M[i].append(-(totalmod*scalar))
			else: 	
				M[i].append(0)
			if M[i+offset][i+offset] == upperweight or M[i+offset][i+offset] < upperweight/ceiling:
				M[i+offset][i+offset]=upperweight/ceiling

		elif i == len(M)-1:
			M[i].append(target*scalar)	
		elif i > len(list1)-1:
			M[i].append(0)
		else:
			if split ==1 :
				M[i].append((list1[i])*scalar)
			else:	
				M[i].append((list1[i]%totalmod)*scalar)
		i+=1
	
	if offset != 0:
		M[len(list1)+offset][-1]=-(totalmod*scalar)
	return M


def prep_matrix(sums,modulust,ceiling,n1,pq,indexlistt,indextarget,sols,constr,climit,cmult,indexes,lchance,aid):
	sr=round(n1**0.5)
	##check whats taking so long here..
	fsols=copy.deepcopy(sols[0])
	fsols.extend(copy.deepcopy(sols[1]))
	indexlist=copy.deepcopy(indexlistt)
	modulus=copy.deepcopy(modulust)
	nmask=[]
	nullstoadd=0
	totalsumslen=total_list_length(sums)
	plist=get_primes(2,10000)
	plist2=copy.copy(plist)
	i=0
	while i < len(fsols):
		j=0
		num=plist.pop(0)
		while j < len(fsols[i+1]):
			k=0
			temp_mask=[]
			m=num
			while k < len(fsols[i+1]):
				if k > 0:
					m=(m*(10**len(str(num))))
					if k != j:
						m+=num
				else:
					if k == j:
						m-=num			
				if k == j:
					temp_mask.append(0)
				else:
					temp_mask.append(num*2)
				k+=1
			j+=1
			if m == 0:
				m=num
			nmask.append(m*(10**nullstoadd))
		nullstoadd+=len(fsols[i+1])*len(str(num))
		i+=2	
	
	k=0
	i=0
	while i < len(fsols):
		j=0
		num=plist2.pop(0)
		while j < len(fsols[i+1]):
			l=k+j*(len(str(num))-1)
			nmask.append(-(num*(10**(l))))
			k+=1
			j+=1
		k+=j*(len(str(num))-1)	
		i+=2

	constraint2=(keysize)*cmult
	constraint3=(keysize)*cmult
	totalmod=modulus[0]*modulus[1]
	origmod0=modulus[0]
	origmod1=modulus[1]
	origtotalmod=totalmod
	am=1+climit
	if not g_use_aid_cols:
		relsize=am*4+totalsumslen*1
		aid=[]
	else:	
		relsize=am*6+totalsumslen*1+len(aid)
	size =0x2+totalsumslen+relsize
	combinedsums=combine(sums,modulus,0,totalmod,1)
	M=init_matrix(size,upperweight,size)
	combinedsumssplit=combine(sums,modulus,1,totalmod,0)
	nindexlist=[]
	nindexlist.extend(copy.deepcopy(indexlist))
	M=addcolumn(M,nindexlist,0,indextarget,0,upperweight,1,1)
	if len(indexes)>0:
		for ind in indexes:
			if lchance == 0:
				nmask[ind]=0
			else:
				nmask[ind]=13371337133713371337133713371337133713371337
	M=addcolumn(M,nmask,0,0,0,upperweight,1,1)	
	j=0
	while j < am:
		combinedsumssplitcpy=copy.deepcopy(combinedsumssplit)
		v=0
		while v < len(combinedsumssplitcpy):
			if combinedsumssplitcpy[v] > 0:
				combinedsumssplitcpy[v]=combinedsumssplitcpy[v]%modulus[0]
			if combinedsumssplitcpy[v] < 0:
				combinedsumssplitcpy[v]*=-1
				combinedsumssplitcpy[v]=combinedsumssplitcpy[v]%modulus[1]
				combinedsumssplitcpy[v]*=-1
			v+=1	
		offst=am*2
		if not g_use_aid_cols:
			offst=0
		M=addcolumn(M,combinedsumssplitcpy,modulus[0],0,len(combinedsums)+len(aid)+offst+j*4+0x1+0x1,upperweight,constraint2,1)
		M[len(combinedsums)*2+len(aid)+offst+j*4+0x1][-1]=(modulus[1])*scalar
		M[len(combinedsums)*2+len(aid)+offst+j*4+0x1][len(combinedsums)*2+len(aid)+offst+j*4+0x1]=upperweight/constraint2
		if (origtotalmod)%((modulus[0]*modulus[1])) !=0:
			M[len(combinedsums)*2+len(aid)+offst+0x3+j*4+0x1][-1]=-(origmod0%modulus[0])*scalar
			M[len(combinedsums)*2+len(aid)+offst+0x2+j*4+0x1][-1]=(origmod1%modulus[1])*scalar
			M[len(combinedsums)*2+len(aid)+offst+0x3+j*4+0x1][len(combinedsums)*2+len(aid)+offst+0x3+j*4+0x1]=(upperweight/constraint3)
			M[len(combinedsums)*2+len(aid)+offst+0x2+j*4+0x1][len(combinedsums)*2+len(aid)+offst+0x2+j*4+0x1]=(upperweight/constraint3)
		if g_use_aid_cols == 1:
			k=0
			while k < len(aid):
				v=0
				ad=0
				if j > 0:
					ad=1
				if j == 0 and g_include_unmerged_col == 1:
					lm=3
				else:
					lm=1	
				while v < lm:
					if v ==0:
						totalmod=modulus[0]*modulus[1]
					if v ==1:
						totalmod=modulus[0]
					if v ==2:	
						totalmod=modulus[1]
	
					target=(pq)%(aid[k])
					if strat == 1:
						target=((target-(n1*4))%aid[k])
					M=addcolumn(M,combinedsums,totalmod,target,len(combinedsums)+j*2+v+ad,upperweight,constraint2,0)
					M[len(combinedsums)*2+k+am*2+0x1][-1]=-(aid[k])*scalar
					if	M[len(combinedsums)*2+k+am*2+0x1][len(combinedsums)*2+k+am*2+0x1]==upperweight:
						M[len(combinedsums)*2+k+am*2+0x1][len(combinedsums)*2+k+am*2+0x1]=upperweight/constr

					if origtotalmod%totalmod !=0:
						M[len(combinedsums)*2+j*2+0x2][-1]=-(((origtotalmod)%totalmod)*scalar)
						M[len(combinedsums)*2+j*2+0x2][len(combinedsums)*2+j*2+0x2]=(upperweight/constraint3)
					v+=1	
				k+=1
		j+=1
		if j < am:
			if strat == 1:
				modulus[0]=n1+1
				modulus[1]=modulus[0]
			else:
				modulus[0]=sr*2+sr//2
				modulus[1]=modulus[0]
			if j > 0:
				if strat == 1:
					modulus[0]-=(2**(keysize-g_mod_red_amount))*j
					modulus[1]-=(2**(keysize-g_mod_red_amount))*j
					if modulus[0] < sr:
						if debug==1:
							print("[Debug]Modulus dropping below n^0.5. Perhaps lower g_mod_red_amount")
				else:	
					modulus[0]-=(2**(keysize//2-g_mod_red_amount))*j
					modulus[1]-=(2**(keysize//2-g_mod_red_amount))*j
					if modulus[0] < sr:
						if debug==1:
							print("[Debug]Modulus dropping below n^0.5. Perhaps lower g_mod_red_amount")
			totalmod=modulus[0]*modulus[1]	
	return M,size,combinedsums,origtotalmod

def calc_fac(sr,n,offset):
	sr+=(offset//2)
	r=sr
	sr=sr*sr
	if sr<n:
		return 0
	sr=sr-n
	sr=round(sr**0.5)
	factor=r-sr
	if factor != n and factor > 1:
		if n%factor==0:
			print("[i]factor1 is: ",factor)
			print("[i]factor2 is: ",n//factor)
			return 1
	return 0

def parse_list(padd,psub,modulus1):
	tadd,tsub=0,0
	for i in padd:
		tadd+=i
	for i in psub:	
		tsub+=i	
	total1=(tadd-tsub)%modulus1
	reverse=modulus1-total1
	return total1,reverse

def check_result(total1,n,sr):	
	if strat == 1:
		total1=total1+n*4
		total1=round(total1**0.5)	
	offset=total1-(sr*2)
	if calc_fac(sr,n,offset) == 1:
		return total1
	return 0

def print_matrix(M,length,length2):
	tempmatrix=[]
	i=0
	while i < length:
		j=length2
		printarray=[]
		printarray.append(i)
		while j > 0:
			printarray.append(M[i, -j])
			j-=1
		tempmatrix.append(printarray)	
		i+=1
	print(Matrix(tempmatrix))	


def add1(list1):
	ad=0
	for a in list1:
		if isinstance(a,list):
			ad+=a[0]
		else:
			ad+=a	
	return ad

def subtract1(list1):
	ad=0
	for a in list1:
		if isinstance(a,list):
			ad-=a[0]
		else:
			ad-=a	
	return ad	
def analyzeresult(debugarray,lengths,sols,sums,s1,s2):
	indexes,total,totals1,totals2=[],[],[],[]
	i,j=0,0
	while j < len(lengths):
		k=0
		add,adds1,adds2,sub,subs1,subs2=[],[],[],[],[],[]
		while k < lengths[j][1]:
			if debugarray[i] <0: 
				temp=debugarray[i]
				temp*=-1
				temp+=1/2
				add.append([sums[i]*(temp//1),i])
				adds1.append([s1[i]*(temp//1),i])
				adds2.append([s2[i]*(temp//1),i])
			elif debugarray[i] >1/2: 
				temp=debugarray[i]
				temp-=1/2
				sub.append([sums[i]*(temp//1),i])
				subs1.append([s1[i]*(temp//1),i])
				subs2.append([s2[i]*(temp//1),i])
			i+=1
			k+=1
		ad=add1(add)
		su=subtract1(sub)
		ads1=add1(adds1)
		ads2=add1(adds2)
		sus1=subtract1(subs1)
		sus2=subtract1(subs2)
		tot=ad-su
		tots1=ads1-sus1
		tots2=ads2-sus2
		if tot%sols[j*2] not in sols[j*2+1]:
			for s in sub:	
				indexes.append(s[1])
		total.append(tot)	
		totals1.append(tots2)
		totals2.append(tots2)			
		j+=1
	ftotal=add1(total)
	ftotals1=add1(totals1)
	ftotals2=add1(totals2)
	return indexes,ftotal,ftotals1,ftotals2

def runLLL(M,size,n,sums,modulus1,pq,s1,s2,mods,procnum,indexlist,lengths,sols):
	##To many if statements will make people think I'm a noob, but it all looks the same to the cpu.
	added =0
	results=[]
	length=len(M)
	length2=len(M[0])
	sr=round(n**0.5)
	M=Matrix(M)
	if show > 0:
		print_matrix(M,length,length2)
	if show < 0:
		print_matrix(M,length,printcols)	
	L=M.LLL()	
	if show == 2:
		print_matrix(L,length,length2)
	if show == -2:
		print_matrix(L,length,printcols)	
	indexall,indexall2=[],[]
	q=0
	while q < length:
		debugarray=[]
		total1,total2,total2,reverse1,reverse2,reverse3=0,0,0,0,0,0
		if L[q, -1] == 0:
			j=0
			skip=0
			while j < len(sums):
				if L[q][j] != 0 : 
					debugarray.append(L[q][j])	
				else:
					skip=1
					break
				j+=1
			if skip==1:
				q+=1
				continue	
			
			indexes,total1,total2,total3=analyzeresult(debugarray,lengths,sols,sums,s1,s2)
			if not total1 in ZZ:
				total1=1
			total1=total1%modulus1
			if not total2 in ZZ:
				total2=1
			total2=total2%mods[0]
			if not total3 in ZZ:	
				total3=1
			total3=total3%mods[1]	
			reverse=(modulus1-total1)%modulus1
			reverse2=(mods[0]-total2)%mods[0]
			reverse3=(mods[1]-total3)%mods[1]
			if added == 0 and total2 == total3 and total2 != 1:
				if len(indexall)==0 and len(indexes) > 0:
					i=0
					while i < len(indexes):
						if indexes[i] not in indexlist:
							indexall.extend([indexes[i]])
							if len(indexall)==g_deletion_amount:
								added=1
								break
						i+=1
			elif g_deletion_mode == 1 and added == 0:
				if len(indexall2)==0 and len(indexes) > 0:
					i=0
					while i < len(indexes):
						if indexes[i] not in indexlist:
							indexall.extend([indexes[i]])
							if len(indexall)==g_deletion_amount:
								added=1
								break
						i+=1
			total1=check_result(total1,n,sr)
			if total1 !=0:
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in total1!")
				return total1,indexall,0
			reverse=check_result(reverse,n,sr)	
			if reverse !=0:	
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in reverse1!")
				return reverse,indexall,0
			total2=check_result(total2,n,sr)	
			if total2 !=0:
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in total2!")
				return total2,indexall,0
			reverse2=check_result(reverse2,n,sr)	
			if reverse2 !=0:
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in reverse2!")
				return reverse2,indexall,0
			total3=check_result(total3,n,sr)	
			if total3 !=0:
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in total3!")
				return total3,indexall,0
			reverse3=check_result(reverse3,n,sr)	
			if reverse3 !=0:
				if debug == 1:
					print("[Debug]Result row: ",debugarray)
					print("[Debug]Found in reverse3!")
				return reverse3,indexall,0	
		q+=1  
		if len(indexall)>0:
			retindex=indexall  
		else:
			retindex=indexall2
	return 0,retindex,added

def singlelist(list1):
	list2=[]
	for lists in list1:
		i=1
		list2.append([])
		while i < len(lists):
			list2[-1].extend(lists[i])
			i+=2				
	return list2

def createindex(bigsums):
	indexlist=copy.deepcopy(bigsums)
	index=0
	i=0
	while i < len(indexlist):
		j=0
		while j < len(indexlist[i]):
			k=0
			index+=indexlist[i][j]
			while k<len(indexlist[i][j+1]):
				indexlist[i][j+1][k]=indexlist[i][j]
				k+=1
			j+=2
		i+=1	
	indexlist=singlelist(indexlist)
	new=[]
	for i in indexlist:
		new.extend(i)
	return new,index

def worker(procnum,return_dict,primetotal,n,pq,sols,aid):
	allsols,allbigsums,allsinglesums,alls1,alls2,allindexlist,alllengths,allflat=[],[],[],[],[],[],[],[]
	bigsums,bigmodulus,singleproducts,singlesums=[],[],[],[]
	i=0
	while i < len(sols):
		sums,modulus=normalize_sols(n,sols[i])	
		bigsums.append(sums)
		bigmodulus.append(modulus)
		i+=1

	for pqi in pq:	
		p=0
		solsc=copy.deepcopy(bigsums)
		while p < len(solsc):
			i=0
			while i < len(solsc[p]):
				for item in aid:
					if 0 == solsc[p][i]%item:
						j=0
						while j < len(solsc[p][i+1]):
							pqi=pqi%aid[0]
							c=solsc[p][i+1][j]	
							if c%item != pqi%item:
								solsc[p][i+1].pop(j)
								continue
							j+=1
				i+=2
			if strat == 1:
				solsc[p]=subtract_4n(solsc[p],bigmodulus[p],n)	
			p+=1	
		allsols.append(solsc)	
		p=0
		solslength=[]	
		flat=[]
		while p < len(solsc):
			i=0
			while i < len(solsc[p]):
				solslength.append([solsc[p][i],len(solsc[p][i+1])])
				flat.append(solsc[p][i])
				flat.append([])
				k=0
				while k < len(solsc[p][i+1]):
					flat[-1].append(solsc[p][i+1][k]%solsc[p][i])
					k+=1
				i+=2
			p+=1	
		allflat.append(flat)	
		alllengths.append(solslength)		
	for i in allsols:
		singlesums=singlelist(i)
		allsinglesums.append(singlesums)
		indexlist,indextarget=createindex(i)	
		allindexlist.append(indexlist)
		s1=copy.deepcopy(singlesums[0])
		s1.extend([0 for _ in range(len(singlesums[1]))])
		s2=[0 for _ in range(len(singlesums[0]))]
		s2.extend(copy.deepcopy(singlesums[1]))
		alls1.append(s1)
		alls2.append(s2)
	mods=copy.deepcopy(bigmodulus)
	try:
		results=0
		maxdepth=g_maxdepth
		cmult=g_cmult
		if g_use_aid_cols == 0:
			g_constr_max=g_constr_min
		while cmult<g_cmult_max:
			climit=g_climit
			while climit<g_climit_max:
				i=g_constr_min
				while results==0 and i < g_constr_max+1:
					constr=(2**((keysize)+i))
					if strat == 0:
						constr=(2**((keysize//2)+i))
					print("[i] constr: "+str(i)+" climit: "+str(climit)+" cmult: "+str(cmult)+" procnum: "+str(procnum))
					t=0
					while t < len(pq):
						indexes=[]
						indexe=[]
						hit = 1
						depth=0
						lchance=0
						while depth < maxdepth+1:
							added=0
							M,size,combinedsums,totalmod=prep_matrix(allsinglesums[t],bigmodulus,primetotal,n,pq[t],allindexlist[t],indextarget,allsols[t],constr,climit,cmult,indexes,lchance,aid)
							results,indexe,added=runLLL(M,size,n,combinedsums,totalmod,pq[t],alls1[t],alls2[t],mods,procnum,indexes,alllengths[t],allflat[t])
							hit = 0
							if results !=0:
								return_dict[procnum]=results
								if debug ==1: 
									print("[Debug]P+Q: "+str(results)+" found at depth: "+str(depth)+" procnum: "+str(procnum)+" aid: "+str(pq[t]))
									print("[Debug]Found at constraints: constr: "+str(i)+" climit "+str(climit)+" cmult "+str(cmult))
								return 1
							if len(indexe)>0:
								if added == 1:
									for z in indexe:
										indexes.append(z)
										hit=1
										lchance=0
							if hit ==0 and lchance==0:
								if len(indexes)==0:
									t+=1
									break
								lchance=1
							elif hit==0 and lchance==1:
								t+=1
								break		
							depth+=1
							if debug == 1 and depth == maxdepth:
								print("[Debug]Max depth reached for proc: "+str(procnum)+" aid: "+str(pq[t]))
						t+=1	
					i+=1
				climit+=g_climit_inc
			cmult+=g_cmult_inc
	except:
		traceback.print_exc(file=sys.stdout)				
	print("exiting: "+str(procnum))
	return 0

def find_sols_combinations(sols,total):
	temp,ret=[],[]
	i=0
	while i < len(sols):
		temp.append(sols[i+1])
		i+=2
	for l in itertools.product(*temp):
		tot=0
		for i in l:
			tot+=i
		ret.append(tot%total)		
	return ret

def create_sols(n,primelist,aid):
	test1=[]
	for prime1 in primelist:
		if prime1 <g_liftlimit+1:
			if prime1==2:
				lift=g_lift_for_2
			elif prime1==3:
				lift=g_lift_for_3
			else:
				lift=g_lift_for_others		
			mult1=[]
			mult1=find_all_solp(n,prime1,lift)
			while len(mult1[1]) > mult1[0]//g_lift_threshold:
					if lift <3 and prime1 != 2:
						mult1=[]
						mult1.append(prime1)
						mult1.append(find_sol_for_p(n,mult1[0]))
						break
					lift-=1	
					mult1=find_all_solp(n,prime1,lift)
			i=0
			while i < len(aid):
				if aid[i] == prime1:
					aid[i]=mult1[0]
				i+=1	

			test1.append(mult1[0])
			test1.append(mult1[1])
		else:	
			mult1=[]
			mult1.append(prime1)
			mult1.append(find_sol_for_p(n,mult1[0]))
			test1.append(mult1[0])
			test1.append(mult1[1])
	return test1,aid

def create_partial_results(sols):
	new=[]
	i=0
	while i < len(sols):
		j=0
		new.append(sols[i])
		new.append([])
		while j < len(sols[i+1]):
			k=0
			temp=sols[i+1][j]
			tot=sols[i]
			while k < len(sols):
				if sols[k] != sols[i]:
				##inverse
					inv=inverse(sols[k],sols[i])
					temp=temp*inv*sols[k]
					tot*=sols[k]
				k+=2
			new[-1].append(temp%tot)	
			j+=1
		i+=2	
	return new,tot	

def subtract_4n(sols,total,n):
	i=0
	while i < len(sols[-1]):
		sols[-1][i]=(sols[-1][i]-4*n)%total
		i+=1
	return sols

def rebase(sols):	
	new=[]
	i=0
	while i < len(sols):
		j=0
		new.append(sols[i])
		new.append([])
		while j < len(sols[i+1]):
			new[-1].append(sols[i+1][j]+2*sols[i])
			j+=1
		i+=2	
	return new

def square_sols(sols):
	new=[]
	i=0
	while i < len(sols):
		j=0
		new.append(sols[i])
		new.append([])
		while j < len(sols[i+1]):
			if (sols[i+1][j]**2)%sols[i] not in new[-1]:
				new[-1].append(sols[i+1][j]**2%sols[i])
			j+=1
		i+=2	
	return new

def find_next(n,sols,primetotal,aid):
	aidsols,aid=create_sols(n,aid,aid)
	if strat ==1:
		aidsols=square_sols(aidsols)
	if debug == 1:
		print("[Debug]Aid: ",aidsols)
	aidsols=rebase(aidsols)
	aidsols,newaid=create_partial_results(aidsols)
	pql=find_sols_combinations(aidsols,newaid)
	pql=[newaid,pql]
	if g_merged_aid_list == 1:
		aid=[newaid]
	elif g_merged_aid_list == 2:	
		aid.insert(0,newaid)
	#aid=[newaid]
	pqlen=len(pql[1])
	print("[i]Total precomputed combinations len: ",pqlen)
	pqlen=pqlen//cores
	temppq=[]
	
	i=0
	while i < cores:
		temppq.append([])
		i+=1

	i=0	
	while len(pql[1])>0:
		temppq[i].append(pql[1][0])
		pql[1].pop(0)
		i+=1
		if i == cores:
			i=0

	i=0
	while i < len(temppq):
		if len(temppq[i])==0:
			temppq.pop(i)
			continue
		i+=1	
	print("[i]Total cores utilized: ",len(temppq))
	print("[i]Max combinations per core: ",len(temppq[0]))
	
	manager=multiprocessing.Manager()
	return_dict=manager.dict()
	jobs=[]
	procnum=0
	print("[*]Launching attack")
	for pq in temppq:
		if len(pq)>0:
		#	print(pq)
			p=multiprocessing.Process(target=worker, args=(procnum,return_dict,primetotal,n,pq,sols,aid))
			jobs.append(p)
			p.start()
			procnum+=1
	
	for proc in jobs:
		proc.join(timeout=0)		
	
	while 1:
		if len(return_dict.values()) > 0:
			fres=copy.deepcopy(return_dict.values())
			for proc in jobs:
				proc.terminate()
			return 0	
		time.sleep(1)		
		
		z=0
		balive=0
		while z < len(jobs):
			if jobs[z].is_alive():
				balive=1
			z+=1
		if balive == 0:
			print("All procs exited")
			return 0	
	return 0

def build_sols_list(prime1,liftlimit,n,test1,mod1,limit,total1):
	found1=0
	mult1=[]
	if  prime1 > liftlimit:
		mult1.append(prime1)
		mult1.append(find_sol_for_p(n,mult1[0]))
		test1.append(mult1[0])
		test1.append(mult1[1])
		mod1*=prime1
	else:	
		if prime1 == 2:
			lift=g_lift_for_2
		elif prime1 == 3:
			lift=g_lift_for_3
		else:
			lift=g_lift_for_others
		mult1=find_all_solp(n,prime1,lift)
		while len(mult1[1]) > mult1[0]//g_lift_threshold or mod1*(mult1[0]//prime1) > limit:
			if lift <3 and prime1 != 2:
				mult1=[]
				mult1.append(prime1)
				mult1.append(find_sol_for_p(n,mult1[0]))
				break
			lift-=1
			mult1=find_all_solp(n,prime1,lift)
		test1.append(mult1[0])
		test1.append(mult1[1])
				
		mod1*=mult1[0]
	total1+=1
	if mod1>limit:
		found1=1
	return test1,found1,mod1	

def init(n,primeslist):	                     
	liftlimit=g_liftlimit
	biglist,bigtotal=[],[]
	total1,total2=0,0
	mod1,mod2=1,1
	test1,test2=[],[]
	limit=round(n**0.5)
	if mode == -1:
		limit=custom_mode
	elif mode == 2:
		limit=limit*2+limit//2
	elif mode == 1:
		limit=limit*round(limit*0.5)
	else:
		limit=n	
	if strat == 0 and mode != -1:
		limit=limit*2+limit//2 #no point in using the other ones here
	found1,found2=0,0
	aid=[]
	i=0
	while i < aidlen:
		aid.append(primeslist[i])
		i+=1
	while 1:
		mult2=[]
		if found1==0:
			prime1=primeslist[0]
			primeslist.pop(0)
			test1,found1,mod1=build_sols_list(prime1,liftlimit,n,test1,mod1,limit,total1)
		if found2==0:	
			prime2=primeslist[0]	
			primeslist.pop(0)
			test2,found2,mod2=build_sols_list(prime2,liftlimit,n,test2,mod2,limit,total2)
		if found1==1 and found2==1:
			break
	
	if mod1 < mod2:
		bigtotal.append(total1)
		bigtotal.append(total2)
		biglist.append(test1)
		biglist.append(test2)
	else:
		bigtotal.append(total2)
		bigtotal.append(total1)
		biglist.append(test2)
		biglist.append(test1)	
	find_next(n,biglist,bigtotal,aid)
	return 0

def find_sols_combinations_and_factor(sols,total,n):
	###Note this can be improved at the cost of space using dynamic programming so we don't iterate over combinations with the same results in mod m
	inc=0
	temp=[]
	i=0
	sr=round(n**0.5)
	#print("sols: "+str(sols)+" total: "+str(total))
	while i < len(sols):
		temp.append(sols[i+1])
		i+=2
	while inc*total < n:	
		for l in itertools.product(*temp):
			tot=0
			for i in l:
				tot+=i
			tot=tot%total
			tot+=inc*total	
			offset=tot-(sr*2)
			if offset > 0 and calc_fac(sr,n,offset) == 1:
				return tot	
		inc+=1		
	return 0

def worker_simple(procnum,return_dict,sum1,n,total):
	res=find_sols_combinations_and_factor(sum1,total,n)
	print("[i]Exiting proc: "+str(procnum))
	return_dict[procnum]=res
	return

def init_simple(n,primeslist):
	global strat
	strat=0
	liftlimit=g_liftlimit
	limit=round(n**0.5)
	if mode == -1:
		limit=custom_mode
	else:
		limit=limit*2+limit//2

	total1=0
	mod1=1
	sols=[]
	while 1:
		prime1=primeslist[0]
		primeslist.pop(0)
		sols,found1,mod1=build_sols_list(prime1,liftlimit,n,sols,mod1,limit,total1)
		if found1 == 1:
			break
	sum1,total=normalize_sols(n,sols)
	#print("test1: ",sum1)	
	#print("len ",len(sum1[1]))
	maxcores=len(sum1[1])//cores
	cpy=copy.deepcopy(sum1[1])
	temp=[]
	i=0
	while i < cores:
		temp.append([])
		i+=1

	i=0	
	while len(cpy)>0:
		temp[i].append(cpy[0])
		cpy.pop(0)
		i+=1
		if i == cores:
			i=0
	#print("temp: ",temp)		
	print("[i]Total cores utilized: ",len(temp))
	print("[i]Max combinations per core: ",len(temp[0]))
	manager=multiprocessing.Manager()
	return_dict=manager.dict()
	jobs=[]
	procnum=0
	print("[*]Launching attack")
	for sol in temp:
		if len(sol)>0:
			inp=copy.deepcopy(sum1)
			sum1[1]=sol
			p=multiprocessing.Process(target=worker_simple, args=(procnum,return_dict,sum1,n,total))
			jobs.append(p)
			p.start()
			procnum+=1
	
	for proc in jobs:
		proc.join(timeout=0)		
	
	while 1:
		if len(return_dict.values()) > 0:
			fres=copy.deepcopy(return_dict.values())
			for proc in jobs:
				proc.terminate()
			return 0	
		time.sleep(1)		
		
		z=0
		balive=0
		while z < len(jobs):
			if jobs[z].is_alive():
				balive=1
			z+=1
		if balive == 0:
			print("All procs exited")
			return 0	
	return

def bitlen(int_type):
	length=0
	while(int_type):
		int_type>>=1
		length+=1
	return length	

def main():
	global keysize
	if g_constr_min > g_constr_max:
		print("g_constr_min must be smaller than g_constr_max")
		return
	while 1:
		if key == 0:
			print("\n[*]Generating rsa key with a modulus of +/- size "+str(keysize)+" bits")
			publicKey, privateKey,phi,p,q = generateKey(keysize//2)
			if g_p !=0 and g_q !=0 and g_enable_custom_factors == 1:
				p=g_p
				q=g_q
			n=p*q
		else:
			n=key	
		print("[i]Modulus length: ",bitlen(n))
		keysize=bitlen(n)
		sr=round(n**0.5)
		primeslist=get_primes(2,10000)
		start2 = default_timer()
		if method == "LLL":
			init(n,primeslist)
		elif method == "Simple":
			print("n: ",n)
			init_simple(n,primeslist)	
		else:
			print("incorrect method")
			return	
		duration = default_timer() - start2
		print("[i]Factorization took: "+str(duration)+" (seconds)")
		return

def print_banner():
	print("Polar Bear was here       ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀ 						")
	print("⠀         ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀ ⣀⣀⣀⣤⣤⠶⠾⠟⠛⠛⠛⠛⠷⢶⣤⣄⣀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀ 	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⣤⣴⠶⠾⠛⠛⠛⠛⠉⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠙⠛⢻⣿⣟ ⠀⠀⠀⠀    	")
	print("⠀⠀⠀⠀⠀⠀⠀⢀⣤⣤⣶⠶⠶⠛⠋⠉⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠙⠳⣦⣄⠀⠀⠀⠀⠀	")
	print("⠀⠀⠀⠀⠀⣠⡾⠟⠉⢀⣀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠹⣿⡆⠀⠀⠀	")
	print("⠀⠀⠀⣠⣾⠟⠀⠀⠀⠈⢉⣿⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⢿⡀⠀⠀	")
	print("⢀⣠⡾⠋⠀⢾⣧⡀⠀⠀⠈⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣄⠈⣷⠀⠀   ")
	print("⢿⡟⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⠀⢹⡆⣿⡆⠀	")
	print("⠈⢿⣿⣛⣀⣀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠹⣆⣸⠇⣿⡇⠀	")
	print("⠀⠀⠉⠉⠙⠛⠛⠓⠶⠶⠿⠿⠿⣯⣄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⠟⠀⣿⡇⠀	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠻⣦⡀⠀⠀⠀⠀⠀⠀⠀⠠⣦⢠⡄⢸⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⡞⠁⠀⠀⣿⡇⠀	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⣿⣶⠄⠀⠀⠀⠀⠀⠀⢸⣿⡇⢸⡇⠀⠀⠀⠀⠀⠀⠀⠀⠀⣴⠇⣼⠋⠀⠀⠀⠀⣿⡇⠀	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢸⡿⣿⣦⠀⠀⠀⠀⠀⠀⠀⣿⣧⣤⣿⡄⠀⠀⠀⠀⠀⠀⠀⠀⣿⣾⠃⠀⠀⠀⠀⠀⣿⠛⠀	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣾⠀⠘⢿⣦⣀⠀⠀⠀⠀⠀⠸⣇⠀⠉⢻⡄⠀⠀⠀⠀⠀⠀⡘⣿⢿⣄⣠⠀⠀⠀⠀⠸⣧⡀	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⠀⠀⠀⠙⣿⣿⡄⠀⠀⠀⠀⠹⣆⠀⠀⣿⡀⠀⠀⠀⠀⠀⣿⣿⠀⠙⢿⣇⠀⠀⠀⠀⠘⣷	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣸⡏⠀⠀⢀⣿⡿⠻⢿⣷⣦⠀⠀⠀⠹⠷⣤⣾⡇⠀⠀⠀⠀⣤⣸⡏⠀⠀⠈⢻⣿⠀⠀⠀⠘⢿	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣴⠿⠁⠀⠀⢸⡿⠁⠀⠀⠙⢿⣧⠀⠀⠀⠀⠠⣿⠇⠀⠀⠀⠀⣸⣿⠁⠀⠀⢀⣾⠇⠀⠀⠀⠀⣼	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣠⡾⡁⠀⠀⠀⠀⣸⡇⠀⠀⠀⠀⠈⠿⣷⣤⣴⡶⠛⡋⠀⠀⠀⠀⢀⣿⡟⠀⠀⣴⠟⠁⠀⣀⣀⣀⣠⡿	")
	print("⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⣿⣿⣤⣾⣧⣤⡿⠁⠀⠀⠀⠀⠀⠀⠀⠈⣿⣀⣾⣁⣴⣏⣠⣴⠟⠉⠀⠀⠀⠻⠶⠛⠛⠛⠛⠋⠉⠀	")
	return

def parse_args():
	global mode,keysize,key,cores,debug,show,printcols,method,strat
	parser = argparse.ArgumentParser(description='Factor stuff')
	parser.add_argument('-key',type=int,help='Provide a key instead of generating one')	
	parser.add_argument('-keysize',type=int,help='Generate a key of input size')	
	parser.add_argument('-mode',type=int,help='Possible values:\n2: Very fast (smallest moduli)\n1: Fast (smaller moduli)\n0: Slow (biggest moduli)\n-1: Custom (see code)\nNote: small moduli work best when factors are close together')	
	parser.add_argument('-cores',type=int,help='# of cpu cores to use')
	parser.add_argument('-debug',type=int,help='1 to enable more verbose output')
	parser.add_argument('-show',type=int,help='1 to render input matrix. 2 to render input+ouput matrix. -1 to render input matrix truncated by --printcols. -2 to render input+output matrix truncated by --printcols')
	parser.add_argument('--printcols',type=int,help='Truncate matrix output if enabled')
	parser.add_argument('-method',type=str,help='Either "LLL" or "Simple" (fastest for small keys)')
	parser.add_argument('-strat',type=int,help='0 for unsquared solutions. 1 for squared solutions')
	args = parser.parse_args()
	if args.mode != None:
		mode = args.mode
	if args.keysize != None:	
		keysize = args.keysize
	if args.key != None:	
		key=args.key
	if args.cores != None:	
		cores=args.cores
	if args.debug != None:
		debug=args.debug	
	if args.show != None:
		show=args.show
		if show < 0 and args.printcols  != None:
			printcols=args.printcols	
	if args.method != None:
		method=args.method		
	if args.strat != None:
		strat=args.strat	
	return
if __name__ == "__main__":
	parse_args()
	print_banner()
	main()

