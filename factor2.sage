# Information:
#
#Key value must be an integer with exactly two prime factors of roughly equal bit size, as specified by the RSA encryption scheme. 
#For anything else you will need to make modifications yourself.
#Not tested on moduli less then 20 bit. 
#
#Example: sage factor2.sage -debug 1 -cores 16 -keysize 34
#
#note: With debug 1 enabled you can see if it found the correct result or accidently hit the correct result under "[Debug]Square root of result:..."
#When the result is an integer (i.e 115308.000000000) it found the correct results and LLL is working as intended. Else when it is a float (i.e 221824.708822079) it hit the factors accidentally due to rounding.
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
key=0                 #Define a custom modulus to factor
keysize=12            #Generate a random modulus of specified bit length
cores=16				#max amount of cores to use

##Algorithm parameters
g_multiplier=0.20           #Decrease to generate more columns, increase to generate less columns.
g_aid_mult=2.5					#Higher value generates less precomputed combinations, adjust accordinly to cores available
g_matched_del_amount=0.1             #Percentage of all weights to delete during weight reduction when we found a valid result
g_unmatched_del_amount=0.2           #Percentage of all weights to delete during weight reudction when we found no valid result
g_search_range_floor=0.5 	
g_weight_red_ceiling=0.6  #Determins depth of weight reduction.. check worker function
#Lifting (code is unoptimized for heavy lifting)
g_liftlimit=4
g_lift_for_2=7
g_lift_for_3=1
g_lift_for_others=2
##Debug settings##
show=0
debug=0
printcols=26

##Define custom factors (mainly for debugging)
g_enable_custom_factors=0
g_p=107
g_q=41


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
	sr=int(round(n**0.5))
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
	sum1=square_sols(sum1)
	sum1=rebase(sum1)	
	sum1,total=create_partial_results(sum1)
	return sum1,total

def init_matrix(size,length):
	M = []
	for i in range(size):
		arr = [0 for _ in range(length)]
		arr[i]=1
		if i == size - 1:
			arr = [1/2 for _ in range(length)]
		M.append(arr)
	return M

def total_list_length(list1):
	listlen=0
	for i in list1:
		listlen+=len(i)
	return listlen


def addcolumn(M,list1,totalmod,target,offset,ceiling,split,scalar):	
	i=0
	while i < len(M):
		if i == len(list1):
			M[i].append(0)
		elif i == len(M)-1:
			M[i].append(target*scalar)	
		elif i > len(list1)-1:
			M[i].append(0)
		else:
			M[i].append((list1[i])*scalar)
		i+=1
	return M


def prep_matrix(sums,modulus,n1,pq,indexlist,indextarget,sols,aid,constraint_adj_l,scalar):
	sums1=copy.deepcopy(sums)
	fsols=copy.deepcopy(sols[0])
	i=1
	while i < len(sols):
		fsols.extend(copy.deepcopy(sols[i]))
		i+=1
	nmask=[]
	nullstoadd=0
	plist=get_primes(2,1000)
	plist2=copy.copy(plist)
	i=0

	s2list=0
	while i < len(fsols):
		j=0
		num=plist.pop(0)
		while j < len(fsols[i+1]):
			if len(fsols[i+1])<3:
				nmask.append(0)
				j+=1
				continue
			k=0
			m=num
			while k < len(fsols[i+1]):
				if k > 0:
					m=(m*(10**len(str(num))))
					if k != j:
						m+=num
				else:
					if k == j:
						m-=num			
				k+=1	
			if m == 0:
				m=num
			
			nmask.append(m*(10**nullstoadd))	
			s2list+=1
			j+=1

		if len(fsols[i+1])>2:	
			
			nullstoadd+=len(fsols[i+1])*len(str(num))
		i+=2	

	k=0
	i=0
	target1=0
	while i < len(fsols):
		num=plist2.pop(0)
		if len(fsols[i+1])>2:
			j=0
			
			while j < len(fsols[i+1]):
				l=k+j*(len(str(num))-1)
				nmask.append(-(num*(10**(l))))
				k+=1
				j+=1
			k+=j*(len(str(num))-1)	
		i+=2

	i=0
	nullstoadd=0
	while i < len(sums1):
		if nullstoadd > 0:
			j=0
			while j < nullstoadd:
				sums1[i].insert(0,0)
				j+=1
		nullstoadd=len(sums1[i])		

		
		i+=1

	relsize=len(indexlist)*1+s2list+len(modulus)

	size =relsize+0x2
	M=init_matrix(size,size)
	j=0
	blen=bitlen(int(round(n1**constraint_adj_l)))
	blen=2**blen
	blen2=bitlen(int(round(n1)))
	while j < len(sums):
		target=((pq-(n1*4))%aid[0])	
		M=addcolumn(M,sums1[j],modulus[j],target,1,blen,1,scalar)
		M[len(indexlist)*1+s2list+j][-1]=(modulus[j])*scalar
		M[len(indexlist)*1+s2list+j][len(indexlist)*1+s2list+j]=1/blen
		M[-2][-1]=-(aid[0])*scalar
		if j == 0:
			M[-2][-3]=1/(2**blen2)
		j+=1


	M=addcolumn(M,indexlist,0,indextarget,0,1,1,scalar)			
	M=addcolumn(M,nmask,0,target1,0,1,1,scalar)	
	i=0
	while i <s2list:
		M[len(indexlist)+i][len(indexlist)+i]=4
		M[-1][len(indexlist)+i]=2
		i+=1
			
	return M,size,blen,s2list

def calc_fac(sr,n,offset):
	sr+=(offset//2)
	r=sr
	sr=sr*sr
	if sr<n:
		return 0
	sr=sr-n
	sr=int(round(sr**0.5))
	factor=r-sr
	if factor != n and factor > 1:
		if n%factor==0:
			print("[i]factor1 is: ",factor)
			print("[i]factor2 is: ",n//factor)
			return 1
	return 0



def check_result(total1,n,sr,aidmod):	
	if total1 < 1:
		if total1 == 0:
			return 0
		else:	
			total1*=-1

	total1=total1+n*4

	test=int(round(total1**0.5))
	offset=test-(sr*2)
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
		ad+=a	
	return ad

def add1_list(list1):
	ad=0
	for a in list1:
		ad+=a[0]
	return ad	

def subtract1(list1):
	ad=0
	for a in list1:
		ad-=a[0]
	return ad	

def analyzeresult(debugarray,sols,sums,tindex):
	indexes,total=[],[]
	i,j=0,0
	while j < len(sols):
		k=0
		add,sub=[],[]
		while k < len(sols[j+1]):
			if debugarray[i] <0: 
				temp=debugarray[i]
				temp*=-1
				temp+=1/2
				add.append([sums[i]*(temp//1),i])
			elif debugarray[i] >0: 
				temp=debugarray[i]
				temp-=1/2
				sub.append([sums[i]*(temp//1),i])
			i+=1
			k+=1
		ad=add1_list(add)
		su=subtract1(sub)
		tot=ad+su
		found=0
		for item in sols[j+1]:
			if item%sols[j]==tot%sols[j]:
				found=1
		if found == 0:
			for s in sub:	
				indexes.append(s[1]+tindex)			
			for s in add:	
				indexes.append(s[1]+tindex)			
		total.append(tot)			
		j+=2
	ftotal=add1(total)
	return indexes,ftotal

def calc_fraction(inf,outf):
	divisor=1/inf
	total=0
	if outf < 0:
		outf*=-1
		outf+=1/2
		total=outf//divisor
	elif outf >0 :
		outf-=1/2
		total=outf//divisor
		total*=-1

	return total

def rat_mod_int(a,k):
	return a.numerator() % (k*a.denominator()) / a.denominator()

def runLLL(M,size,n,sums,pq,s1,mods,procnum,indexlist,sols,indl,constr1,aidmod,slen,constraint_adj_l,search_range,g_deletion_amount,g_deletion_amount_unmatched):
	indexlistc=copy.deepcopy(indexlist)
	added1=0
	results=[]
	length=len(M)
	length2=len(M[0])
	sr=int(round(n**0.5))
	M=Matrix(M)
	prevind=[]
	adjusted=0
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
		a=1
		skip=0
		if L[q, -(len(sums)+3)] != 1/2:
			q+=1
			continue
		while a < (len(sums)+3):
			if 	L[q, -a] != 0:
				skip=1
				break
			a+=1	
		if skip == 1:
			q+=1
			continue	
		p=0
		j=0
		skip=0
		prev=0
		padded=0
		while p < len(sums):
			debugarray=[]
			total1,reverse1=0,0
			if skip==1:
				break
			jc=j
			while j < len(sums[p])+jc:
				if rat_mod_int(L[q][j],1) != 0 : 
					debugarray.append(L[q][j])	
				else:
					skip=1
					break
				j+=1
			if skip==1:
				break	
			modadjust=L[q][len(indl*1)+slen+p]
			total=calc_fraction(constr1,modadjust)
			indexes,total1=analyzeresult(debugarray,sols[p],sums[p],jc)
			total1=total1+(mods[p]*total)	
			back=total1
			if back==prev:
				total1=check_result(total1,n,sr,aidmod)
				indexall.extend(indexes)
				if padded==0:
					indexall.extend(prevind)
					padded=1
			else:
				if p !=0:
					break		
			if total1 !=0:
				if debug == 1 and back == prev:
					print("[Debug]Result row: ",L[q])
					print("[Debug]Found in total1! "+str(back)+" mod "+str(mods[p])+" aidmod: "+str(aidmod))
					print("[Debug]Square root of result: "+str(back**0.5)+" with +4n: "+str((back+4*n)**0.5)+"  test: "+str(back-n))
				if back == prev:
					return total1,indexall,0,0,constraint_adj_l		
			elif adjusted == 0:
				checktotal=back
				if back < 0:
					checktotal*=-1
				if checktotal > n**(search_range*2):
					constraint_adj_l-=0.1
					adjusted=1
				elif checktotal > n**(search_range*1.2):
					constraint_adj_l-=0.05
					adjusted=1	
				elif checktotal > n**search_range:
					constraint_adj_l-=0.001
					adjusted=1	
				elif checktotal < n**(search_range/2):
					constraint_adj_l+=0.001
					adjusted=1
			prev=back
			prevind=indexes		
	
			p+=1
		q+=1  
	i=0
	unmatched=0
	adj=0
	if len(indexlistc)==0:
		adj=1
	while i < g_deletion_amount and len(indexall) > 0:
		ind=random.randrange(0,len(indexall))
		if len(indexlistc)>0 and ind >0:
			ir=take_closest(indexlistc,indexall[ind])
			if indexall[ind]!=indexlistc[ir]:
				if indexall[ind]<indexlistc[ir]:
					indexlistc.insert(ir,indexall[ind])
				else:	
					indexlistc.insert(ir+1,indexall[ind])
				added1=1
				i+=1
		elif ind>0:	
			indexlistc.append(indexall[ind])
			added1=1
			i+=1
		indexall.pop(ind)	
	
	if added1 ==0:
		unmatched=1
		j=0
		maxtries=100
		k=0
		while j < g_deletion_amount_unmatched and k < maxtries:
			ind=random.randrange(0,len(indl))
			if len(indexlistc)>0 and ind>0:
				ir=take_closest(indexlistc,ind)

				if ind!=indexlistc[ir]:
					if ind<indexlistc[ir]:
						indexlistc.insert(ir,ind)
					else:	
						indexlistc.insert(ir+1,ind)
					added1=1
					j+=1

			elif ind >0:	
				indexlistc.append(ind)
				added1=1
				j+=1	
			k+=1		
	return 0,indexlistc,added1,unmatched,constraint_adj_l

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

def weightreduction(indexe,reduced_singlesums,reduced_indexlist,reduced_sols):
	indexes=copy.deepcopy(indexe)
	total=0
	off=0
	i=0
	while i < len(reduced_sols):
		j=0
		subtotal=0
		while j < len(reduced_sols[i]):
			k=0
			while k < len(reduced_sols[i][j+1]):
				if total == indexes[0] and len(reduced_sols[i][j+1]) == 1:
					indexes.pop(0)
					if len(indexes) == 0:
						return reduced_singlesums,reduced_indexlist,reduced_sols
				elif total == indexes[0] and len(reduced_sols[i][j+1]) > 1:
					reduced_sols[i][j+1].pop(k)
					reduced_indexlist.pop(total-off)
					reduced_singlesums[i].pop(subtotal)
					indexes.pop(0)
					off+=1
					if len(indexes) == 0:
						return reduced_singlesums,reduced_indexlist,reduced_sols

					total+=1
					continue
				subtotal+=1	
				total+=1
				k+=1
			j+=2
		i+=1
	return reduced_singlesums,reduced_indexlist,reduced_sols

def worker(procnum,return_dict,n,pq,sols,aid,search_range):
	bits=bitlen(n)
	scalar=10**bits
	allsols,allbigsums,allsinglesums,allindexlist=[],[],[],[]
	bigsums,bigmodulus,singlesums=[],[],[]
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

			solsc[p]=subtract_4n(solsc[p],bigmodulus[p],n)	
			p+=1	
		allsols.append(solsc)	
	for i in allsols:
		singlesums=singlelist(i)
		allsinglesums.append(singlesums)
		indexlist,indextarget=createindex(i)	
		allindexlist.append(indexlist)

	mods=copy.deepcopy(bigmodulus)
	constraint_adj_l=[]
	if len(constraint_adj_l)==0:
		for i in  pq:
			constraint_adj_l.append(1.0)
	g_deletion_amount=len(allindexlist[0])*g_matched_del_amount
	g_deletion_amount_unmatched=len(allindexlist[0])*g_unmatched_del_amount
	try:
		g=0
		while g < 200:
			t=0
			while t < len(pq):
				indexes=[]
				indexe=[]
				depth=0
				depth_unmatched=0
				while 1:
					added=0
					reduced_singlesums=copy.deepcopy(allsinglesums[t])
					reduced_indexlist=copy.deepcopy(allindexlist[t])
					reduced_sols=copy.deepcopy(allsols[t])
					if len(indexes)>0:
						reduced_singlesums,reduced_indexlist,reduced_sols=weightreduction(indexes,reduced_singlesums,reduced_indexlist,reduced_sols)
					M,size,constr1,slen=prep_matrix(reduced_singlesums,bigmodulus,n,pq[t],reduced_indexlist,indextarget,reduced_sols,aid,constraint_adj_l[t],scalar)
					results,indexe,added,unmatched,constraint_adj_l[t]=runLLL(M,size,n,reduced_singlesums,pq[t],reduced_sols,mods,procnum,indexes,reduced_sols,reduced_indexlist,constr1,aid[0],slen,constraint_adj_l[t],search_range,g_deletion_amount,g_deletion_amount_unmatched)
					#print("proc: "+str(procnum)+" matched: "+str(unmatched)+" "+str(indexe)+" const: "+str(constraint_adj_l[t]))
					if results !=0:
						return_dict[procnum]=results
						if debug ==1: 
							print("[Debug]constraint: ",constraint_adj_l[t])
							print("[Debug]P+Q: "+str(results)+" found at depth: "+str(depth)+" "+str(depth_unmatched)+" procnum: "+str(procnum)+" aid: "+str(pq[t])+" aidmod: "+str(aid[0]))
							print("[Debug]search_range: ",search_range)
						return 1
					elif added==1:
						indexes=indexe
						if len(indexes) > len(allindexlist[t])*g_weight_red_ceiling:
							break
					else:
						break
					if unmatched ==0:
						depth+=1
					else:
						depth_unmatched+=1
				t+=1	
			g+=1	
	except:
		traceback.print_exc(file=sys.stdout)	
	if debug == 1:				
		print("[Debug]Exiting: "+str(procnum))
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
		mult1=[]
		mult1.append(prime1)
		if prime1==2:
			mult1=[2,[1]]
		else:	
			mult1.append(find_sol_for_p(n,mult1[0]))
		lift=2
		liftlim=1
		if prime1==2:
			liftlim=g_lift_for_2
		elif prime1==3:
			liftlim=g_lift_for_3
		elif prime1 < g_liftlimit:
			liftlim=g_lift_for_others
		while 1:
			oldmult1=copy.deepcopy(mult1)
			mult1=find_all_solp(n,prime1,lift)
			if(len(mult1[1])-len(oldmult1[1])>prime1-1):
				if lift > liftlim:
					mult1=oldmult1
					break
			lift+=1	
		i=0
		while i < len(aid):
			if aid[i] == prime1:
				aid[i]=mult1[0]
			i+=1
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

def find_next(n,sols,aid,search_range):
	aidsols,aid=create_sols(n,aid,aid)

	aidsols=square_sols(aidsols)
	aidsols=rebase(aidsols)
	aidsols,newaid=create_partial_results(aidsols)
	pql=find_sols_combinations(aidsols,newaid)
	pql=[newaid,pql]

	aid=[newaid]
	if newaid**g_aid_mult < n:
		return -10
	if debug == 1:
		print("[Debug]Aid: ",aidsols)
		print("[Debug]Aid modulus: ",newaid)	
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
			p=multiprocessing.Process(target=worker, args=(procnum,return_dict,n,pq,sols,aid,search_range))
			jobs.append(p)
			p.start()
			procnum+=1
	
	for proc in jobs:
		proc.join(timeout=0)		
	
	while 1:
		time.sleep(1)
		if len(return_dict.values()) > 0:
			fres=copy.deepcopy(return_dict.values())
			for proc in jobs:
				proc.terminate()
			return 1			
		
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
	mult1=[]
	mult1.append(prime1)
	if prime1==2:
		mult1=[2,[1]]
	else:	
		mult1.append(find_sol_for_p(n,mult1[0]))
	lift=2
	liftlim=1
	if prime1==2:
		liftlim=g_lift_for_2
	elif prime1==3:
		liftlim=g_lift_for_3
	elif prime1 < g_liftlimit:
		liftlim=g_lift_for_others
	while 1:
		oldmult1=copy.deepcopy(mult1)
		mult1=find_all_solp(n,prime1,lift)
		if(len(mult1[1])-len(oldmult1[1])>prime1-1):
			if lift > liftlim:
				mult1=oldmult1
				break
		lift+=1	
	test1.append(mult1[0])
	test1.append(mult1[1])
				
	mod1*=mult1[0]
	total1+=1
	if mod1>limit:
		found1=1
	return test1,found1,mod1	

def init(n,primeslist,search_range,aidlen,lnumber,limit):	
	liftlimit=g_liftlimit
	biglist,bigtotal=[],[]
	total1,total2=0,0
	mod1,mod2=1,1
	test1,test2=[],[]
	found1,found2=0,0
	aid=[]
	i=0
	while i < aidlen:
		aid.append(primeslist[i])
		i+=1
	lists=[]
	mods=[]
	found=[]
	i=0
	totals=[]
	while i < lnumber:
		lists.append([])
		mods.append(1)
		found.append(0)
		totals.append(0)
		i+=1

	while 1:
		i=0
		hit=0
		while i < len(lists):
			if found[i]==0:
				hit=1
				prime1=primeslist[0]
				primeslist.pop(0)
				lists[i],found[i],mods[i]=build_sols_list(prime1,liftlimit,n,lists[i],mods[i],limit,totals[i])
			i+=1	
		if hit == 0:
			break	
	tmod=1
	for i in mods:
		tmod*=i	
	if tmod < n:
		return -1
	ret=find_next(n,lists,aid,search_range)
	return ret

def bitlen(int_type):
	length=0
	while(int_type):
		int_type>>=1
		length+=1
	return length	

def main():
	global key
	multip=g_multiplier
	search_range=1
	aidlen=1
	g_cols=1
	while 1:
		if g_p !=0 and g_q !=0 and g_enable_custom_factors == 1:
				p=g_p
				q=g_q
				key=p*q
		if key == 0:
			print("\n[*]Generating rsa key with a modulus of +/- size "+str(keysize)+" bits")
			publicKey, privateKey,phi,p,q = generateKey(keysize//2)
			n=p*q
			key=n
		else:
			print("[*]Attempting to break modulus: "+str(key)+" aidlen "+str(aidlen)+" cols: "+str(g_cols))
			n=key	
		limit=int(round(n**multip))
		bits=bitlen(n)
		print("[i]Modulus length: ",bitlen(n))
		sr=int(round(n**0.5))
		primeslist=get_primes(2,10000)
		start2 = default_timer()
		ret=init(n,primeslist,search_range,aidlen,g_cols,limit)
		if ret == 1:
			duration = default_timer() - start2
			print("[i]Factorization took: "+str(duration)+" (seconds)")
			return
		elif ret == -1:	
			if debug == 1:
				print("[Debug]Increasing g_cols: ",g_cols)

			g_cols+=1
		elif ret == -10:
			if debug == 1:
				print("[Debug]Increasing aidlen: ",aidlen)
			aidlen+=1
		else:	
			search_range-=0.1
			if search_range < g_search_range_floor:
				search_range=1

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
	global keysize,key,cores,debug,show,printcols
	parser = argparse.ArgumentParser(description='Factor stuff')
	parser.add_argument('-key',type=int,help='Provide a key instead of generating one')	
	parser.add_argument('-keysize',type=int,help='Generate a key of input size')	
	parser.add_argument('-cores',type=int,help='# of cpu cores to use')
	parser.add_argument('-debug',type=int,help='1 to enable more verbose output')
	parser.add_argument('-show',type=int,help='1 to render input matrix. 2 to render input+ouput matrix. -1 to render input matrix truncated by --printcols. -2 to render input+output matrix truncated by --printcols')
	parser.add_argument('--printcols',type=int,help='Truncate matrix output if enabled')

	args = parser.parse_args()
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
	return

if __name__ == "__main__":
	parse_args()
	print_banner()
	main()

