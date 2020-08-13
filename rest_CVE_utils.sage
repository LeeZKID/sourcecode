#Key generation
def key_gen(Fq,n,r):
    Htr_unsys = random_matrix(Fq,n-r,r); #public matrix (only non-systematic portion)
    e = rnd_restricted_vector(Fq,n);
    
    #compute syndrome
    s = e[0,0:r] + e[0,r:n]*Htr_unsys;
    return e,Htr_unsys,s;    

##################################################################

#Generate a random vector made of +1 and -1
def rnd_restricted_vector(Fq,n):
    a = convert_restricted(Fq,random_matrix(GF(2),1,n),n);
    return a;

##################################################################

#Convert binary string to \pm 1 over Fq
def convert_restricted(Fq,a,n):
    b = a.change_ring(ZZ);
    b = 2*b-ones_matrix(ZZ,1,n);
    b = b.change_ring(Fq);
    return b;

##################################################################    

#Apply restricted monomial transformation
def apply_rest_monomial(Fq,tau_perm, tau_values, a, n):
    b = matrix(Fq,1,n);
    for i in range(0,n):
        p = tau_perm[i];
        b[0,i] = tau_values[0,p]*a[0,p];
    return b;

##################################################################

#Apply inverse of restricted monomial transformation
def apply_inv_rest_monomial(Fq,tau_perm, tau_values, a, n):
    b = matrix(Fq,1, n);
    for i in range(0, n):
        p = tau_perm[i];
        b[0,p] = tau_values[0,p]*a[0,i];
    return b;    

##################################################################

##Simulate one round of the protocol
def one_round_sim(Fq,n,r,e,Htr_unsys,s):
    
    ok=0;
    
    ##Generating committments
    u = random_matrix(Fq,1,n);
    tau_perm = P.random_element();
    tau_values  = rnd_restricted_vector(Fq,n);

    tau_e = apply_rest_monomial(Fq,tau_perm,tau_values,e,n);
    tau_u = apply_rest_monomial(Fq,tau_perm,tau_values,u,n);

    u_Htr = u[0,0:r]+u[0,r:n]*Htr_unsys;


    #Hashing and sending c0 and c1
    c0_before_hash = str(tau_perm)+str(tau_values)+str(u_Htr);
    c0 = hashlib.sha256();
    c0.update(c0_before_hash.encode('utf-8'));
    c0 = c0.hexdigest();

    c1_before_hash = str(tau_u)+str(tau_e);
    c1 = hashlib.sha256();
    c1.update(c1_before_hash.encode('utf-8'));
    c1 = c1.hexdigest();

    ##Verifier chooses z
    z = Fq_star.random_element();

    #Prover computes y
    y = tau_u + z*tau_e;

    ##Verifier chooses b
    b = GF(2).random_element();

    #Creating response
    if b==0:
        tau_inv_y = apply_inv_rest_monomial(Fq,tau_perm,tau_values,y,n);
        final_val = tau_inv_y[0,0:r]+tau_inv_y[0,r:n]*Htr_unsys-z*s;
        prover_c0_before_hash = str(tau_perm)+str(tau_values)+str(final_val);
        prover_c0 = hashlib.sha256();
        prover_c0.update(prover_c0_before_hash.encode('utf-8'));
        prover_c0 = prover_c0.hexdigest();
        if prover_c0 == c0:
            ok=1;
    else:
        final_val = y-z*tau_e;
        prover_c1_before_hash = str(final_val)+str(tau_e);
        prover_c1 = hashlib.sha256();
        prover_c1.update(prover_c1_before_hash.encode('utf-8'));
        prover_c1 = prover_c1.hexdigest();
        if prover_c1 == c1:
            ok=1;
    return ok;

########################################################################

def multiple_rounds_sim(Fq,n,r,e,Htr_unsys,s,N):


    ##Generating N committments
    big_c = []; #it is the overall commitment
    tau_u_matrix = matrix(Fq,N,n); #it contains the N vectors u, for all rounds
    tau_perm_matrix = matrix(ZZ,N,n); #it contains the N permutations, for all rounds
    tau_values_matrix = matrix(Fq,N,n); #it contains the N scaling vectors, for all rounds
    tau_e_matrix = matrix(Fq,N,n);

    comm_hashes=[];    
    #Proceeding with remaining rounds
    for i in range(0,N):

        #Generating a random u and a random restricted monomial
        u = random_matrix(Fq,1,n);
        tau_perm = P.random_element();
        tau_values = rnd_restricted_vector(Fq,n);

        #Apply monomial to tau_e and tau_u
        tau_e = apply_rest_monomial(Fq,tau_perm,tau_values,e,n);
        tau_u = apply_rest_monomial(Fq,tau_perm,tau_values,u,n);

        u_Htr = u[0,0:r]+u[0,r:n]*Htr_unsys;

        #Hashing, appending commitments to c and storing c0 and c1
        c0_before_hash = str(matrix(tau_perm))+str(tau_values)+str(u_Htr);
        c0 = hashlib.sha256();
        c0.update(c0_before_hash.encode('utf-8'));
        c0 = c0.hexdigest();

        c1_before_hash = str(tau_u)+str(tau_e);
        c1 = hashlib.sha256();
        c1.update(c1_before_hash.encode('utf-8'));
        c1 = c1.hexdigest();

        big_c+=c0+c1;
        comm_hashes.append(c0); 
        comm_hashes.append(c1);

        #Storing the random generated values
        tau_u_matrix[i,:] = tau_u;
        tau_e_matrix[i,:] = tau_e;
        tau_perm_matrix[i,:] = matrix(tau_perm);
        tau_values_matrix[i,:] = tau_values;


    #verification over N rounds starts    
    verifier_c=[]

    for j in range(0,N):

        ##Verifier chooses z
        z = Fq_star.random_element();

        #Prover computes y
        y = tau_u_matrix[j,:]+z*tau_e_matrix[j,:];

        ##Verifier chooses b
        b = GF(2).random_element();

        #Creating response: for each value of b, we also sen the opposite hash commitment
        if b==0:
            tau_inv_y = apply_inv_rest_monomial(Fq,vector(tau_perm_matrix[j,:]),tau_values_matrix[j,:],y,n);
            final_val = tau_inv_y[0,0:r]+tau_inv_y[0,r:n]*Htr_unsys-z*s;
            prover_c0_before_hash = str(tau_perm_matrix[j,:])+str(tau_values_matrix[j,:])+str(final_val);
            prover_c0 = hashlib.sha256();
            prover_c0.update(prover_c0_before_hash.encode('utf-8'));
            prover_c0 = prover_c0.hexdigest();
            verifier_c+=prover_c0+comm_hashes[2*j+1];
        else:
            final_val = y-z*tau_e_matrix[j,:];
            prover_c1_before_hash = str(final_val)+str(tau_e_matrix[j,:]);
            prover_c1 = hashlib.sha256();
            prover_c1.update(prover_c1_before_hash.encode('utf-8'));
            prover_c1 = prover_c1.hexdigest();
            verifier_c+=comm_hashes[2*j]+prover_c1;

    #Final test
    if big_c == verifier_c:
        ok = 1;
    else:
        ok = 0;
    return(ok);    