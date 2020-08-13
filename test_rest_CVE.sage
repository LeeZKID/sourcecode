#one round simulation    
reset();

import hashlib;
load('rest_CVE_utils.sage')

#scheme parameters
q = 31;
n = 163;
r = 59;
N=128;

#Preparations to execute the protocol
Fq=GF(q); #finite field with q elements
Fq_set = Set(Fq);
Fq_star = Fq_set.difference([0]); #multiplicative group of Fq
P = Permutations(range(0,n)); #set of permutations of {0, ... , n-1}

#Key generation
e, Htr_unsys, s = key_gen(Fq,n,r);

#Single round verification
print("Checking one single round...");
ok = one_round_sim(Fq,n,r,e,Htr_unsys,s);
if ok==1:
    print("ACCEPTED!");
else:
    print("REJECTED!");
    
print("----------------------------");


#Multiple rounds (with compression) verification    
print("Running N rounds with compression...");
ok = multiple_rounds_sim(Fq,n,r,e,Htr_unsys,s,N);
if ok==1:
    print("ACCEPTED!");
else:
    print("REJECTED!");
