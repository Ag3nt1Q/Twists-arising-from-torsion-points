//Helping functions to calculate the function f such that div(f)=D -> program by F. Brunatala (https://perso.ens-lyon.fr/francois.brunault/parigp/divisors.gp) translated into MAGMA
// E is an elliptic curve
//divisor  D=\sum n_i(P_i) is implemented as a vector [<n_1,P_1>, ..., <n_r, P_r>]
function position(D,P)
    for i:=1 to #D do
        if D[i][2] eq P then
            return i;
        end if;
    end for;
return 0;
end function;

function simplifie(D)
    newD:=[];
    finalD:=[];
    for i:=1 to #D do
        i0:=position(newD,D[i][2]);
        if (i0 gt 0) then
            newD[i0][1]:=newD[i0][1]+D[i][1];
        else
            newD:=Append(newD, D[i]);
        end if;
    end for;
    for i:=1 to #newD do
        if (newD[i][1] ne 0) then
            finalD:=Append(finalD, newD[i]);
        end if;
    end for;
    return finalD;
end function;

// div(f_P)=2(P)-(2P)-(O)
function fP(E,P)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    p:=EE![x,y,1];
    PP:=EE!P;
    if (P eq E![0,1,0]) then
        return FE!1;
    end if;
    X:=1/((p-PP)[1]-PP[1]);
    return X;
end function;

// div(f_{P,Q})=(P)+(Q)-(P+Q)-(O)
function fPQ(E,P,Q)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    p:=EE![x,y,1];
    PP:=EE!P;
    QQ:=EE!Q;
    if (P eq E![0,1,0]) or (Q eq E![0,1,0]) then
        return FE!1 ;
    end if;
    if P eq Q then
        return fP(E,P);
    end if;
    if P[1] eq Q[1] then
        return p[1]-PP[1];
    end if;
    xPQ:=(PP+QQ)[1];
    X:= ((PP[1]-QQ[1])*(p[2]-PP[2])-(PP[2]-QQ[2])*(p[1]-PP[1]))/(p[1]-xPQ);
    return X;
end function;

// div(f_nP)=n(P)-(nP)-(n-1)(O)
function fPn(E,P,n)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    p:=EE![x,y,1];
    PP:=EE!P;
    if (n eq 1) or (P eq E![0,1,0]) then    
        return FE!1;
    end if;
    if n eq -1 then
        return 1/(p[1]-PP[1]);
    end if;
    if n eq 2 then
        return fP(E,P);
    end if;
    if n gt 0 then
        m:= n div 2;
        FP:=fP(E,P);
        FPn:=fPn(E,2*P,m);
        h:=FP^m*FPn;
        if (n mod 2) eq 0 then
            return h;
        end if;
        FPQ:=fPQ(E,P,(n-1)*P);
        h:=h*FPQ;
        return h;
    end if;
    FPn:=fPn(E,P,-n);
    FPQ:=fPQ(E,n*P,(-n)*P);
    h:=1/(FPn*FPQ);
    return h;
end function;

// div(f)=D
function fD(E,D)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    p:=EE![x,y,1];
    D0:=simplifie(D);
    if D0 eq [] then
        return FE!1;
    end if;
    h:=FE!1;
    newD:=[];
    for i:=1 to #D0 do
        FPn:=fPn(E,D0[i][2],D0[i][1]);
        h:=h*FPn;
        newD:=Append(newD,(D0[i][1])*(D0[i][2]));
    end for;
    R:=newD[1];
    for i:=2 to #newD do
        FPQ:=fPQ(E,R,newD[i]);
        h:=h*FPQ;
        R:=R+newD[i];
    end for;
    return h;
end function;

// Helping functions to calculate the twisted action of the cocycle
// Slight modifications of the program by F. Brunatala

// div(f_P)=2(P)-(2P)-(O)
function fP_t(E,P,S)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    SS:=EE!S;
    p:=EE![x,y,1]+SS;
    PP:=EE!P;
    if (P eq E![0,1,0]) then
        return FE!1;
    end if;
    X:=1/((p-PP)[1]-PP[1]);
    return X;
end function;

// div(f_{P,Q})=(P)+(Q)-(P+Q)-(O)
function fPQ_t(E,P,Q,S)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    SS:=EE!S;
    p:=EE![x,y,1]+SS;
    PP:=EE!P;
    QQ:=EE!Q;
    if (P eq E![0,1,0]) or (Q eq E![0,1,0]) then
        return FE!1 ;
    end if;
    if P eq Q then
        return fP_t(E,P,S);
    end if;
    if P[1] eq Q[1] then
        return p[1]-PP[1];
    end if;
    xPQ:=(PP+QQ)[1];
    X:= ((PP[1]-QQ[1])*(p[2]-PP[2])-(PP[2]-QQ[2])*(p[1]-PP[1]))/(p[1]-xPQ);
    return X;
end function;

// div(f_nP)=n(P)-(nP)-(n-1)(O)
function fPn_t(E,P,n,S)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    SS:=EE!S;
    p:=EE![x,y,1]+SS;
    PP:=EE!P;
    if (n eq 1) or (P eq E![0,1,0]) then    
        return FE!1;
    end if;
    if n eq -1 then
        return 1/(p[1]-PP[1]);
    end if;
    if n eq 2 then
        return fP_t(E,P,S);
    end if;
    if n gt 0 then
        m:= n div 2;
        FP:=fP_t(E,P,S);
        FPn:=fPn_t(E,2*P,m,S);
        h:=FP^m*FPn;
        if (n mod 2) eq 0 then
            return h;
        end if;
        FPQ:=fPQ_t(E,P,(n-1)*P,S);
        h:=h*FPQ;
        return h;
    end if;
    FPn:=fPn_t(E,P,-n,S);
    FPQ:=fPQ_t(E,n*P,(-n)*P,S);
    h:=1/(FPn*FPQ);
    return h;
end function;

// div(f)=D
function fD_t(E,D,S)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    SS:=EE!S;
    p:=EE![x,y,1]+SS;
    D0:=simplifie(D);
    if D0 eq [] then
        return FE!1;
    end if;
    h:=FE!1;
    newD:=[];
    for i:=1 to #D0 do
        FPn:=fPn_t(E,D0[i][2],D0[i][1],S);
        h:=h*FPn;
        newD:=Append(newD,(D0[i][1])*(D0[i][2]));
    end for;
    R:=newD[1];
    for i:=2 to #newD do
        FPQ:=fPQ_t(E,R,newD[i],S);
        h:=h*FPQ;
        R:=R+newD[i];
    end for;
    return h;
end function;

//MODEL FOR THE p-TWIST

//a=z^k, z=zeta_p; this function returns the exponent k
function exp(a,z)
    k:=0;
    while a ne 1 do
        a:=a/z;
        k:=k+1;
    end while;
    return k;
end function;

function polinom(koef,monomi)
    pol:=0;
    for i:=1 to (#(monomi)) do
        pol:=pol+koef[i]*monomi[i];
    end for;
    return pol;
end function;

//p is a prime, z=zeta_p, d is a p-power free integer (not in the argument of the function), E is an elliptic curve over the field K, <S,T>=E[p]<E(K)
function pTwist(p,z,E,K,S,T)
    FE<x,y>:=FunctionField(E);
    EE:=BaseChange(E,FE);
    O:=E![0,1,0];
    U:=2*T;
    Dz:=[<1,T>,<-1,O>];
    Dw:=[<1,U>,<-1,O>];
    for i:=1 to p-1 do
        Dz:=Append(Dz,<1,T+i*S>);
        Dz:=Append(Dz,<-1,i*S>);
        Dw:=Append(Dw,<1,U+i*S>);
        Dw:=Append(Dw,<-1,i*S>);
    end for;
    Z:=fD(E,Dz);
    W:=fD(E,Dw);
    Zt:=fD_t(E,Dz,S);
    Wt:=fD_t(E,Dw,S);
    ez:=exp(Zt/Z,z);
    ew:=exp(Wt/W,z);
    //Riemann-Rocha space
    n:=Floor((2*p-1+Sqrt(4*p^2-12*p+1))/2);
    Div:=DivisorGroup(E);
    D0:=[<Place(O),1>];
    for i:=1 to p do
        D0:=Append(D0,<Place(i*S),1>);
    end for;
    D:=Divisor(Div,D0);
    L_D, inv_map:=RiemannRochSpace(n*D);
    _map:=Inverse(inv_map);
    vekt:=[];
    for j:=0 to n do
        for i:=0 to n-j do
            vekt:=Append(vekt, _map(Z^i*W^j));
        end for;
    end for;
    //Relations for Z and W
    c:=Kernel(Matrix(vekt));
    R<u,v>:=PolynomialRing(K,2);
    monomi:=[];
    for j:=0 to n do
        for i:=0 to n-j do
            monomi:=Append(monomi, u^i*v^j);
        end for;
    end for;
    polynoms:=[];
    for i:=1 to (Dimension(c)) do
        polynoms:=Append(polynoms,polinom(c.i,monomi));
    end for;
    f:=GCD(polynoms); 
    //Scaling with the appropriate powers of d^(1/p)
    KK<d>:=FunctionField(K);
    RR:=PolynomialRing(KK,2);
    AssignNames(~RR,["z", "w"]);
    model_coef:=[];
    for j:=0 to n do
        for i:=0 to n-j do
            m:=u^i*v^j;
            e:=(ez*i+ew*j) div p;
            coeff:=d^e*MonomialCoefficient(f, m);
            model_coef:=Append(model_coef,coeff);
        end for;
    end for;
    monom:=[];
    for i:=1 to #monomi do
        monom:=Append(monom,RR!monomi[i]);
    end for;
    model:=polinom(model_coef,monom);
    return model;
end function;