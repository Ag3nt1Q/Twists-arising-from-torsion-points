function l(P1,P2,P); 
    lin:=(P1[1]-P2[1])*(P[2]-P1[2])-(P1[2]-P2[2])*(P[1]-P1[1]);
    return lin;
end function;

function polinom(koef,monomi)
    pol:=0;
    for i:=1 to (#(monomi)) do
        pol:=pol+koef[i]*monomi[i];
    end for;
    return pol;
end function;

F<zeta_3> := CyclotomicField(3);
K<a>:=FunctionField(F);
E:=EllipticCurve([(zeta_3+2)*a+(1-zeta_3),0,(zeta_3+1)*a^2-zeta_3*a,0,0]);
S:=E![0,0,1];
T:=E![-a,a,1];

FE<x,y>:=FunctionField(E);
EE:=BaseChange(E,FE);
O:=E![0,1,0];
P:=EE![x,y,1];
SS:=EE!S;
TT:=EE!T;
p:=EE![x,y,1]+SS;
    //PS:=P+SS;
//constructing functions Z i W for the model with the desired divisor structure
Z:=l(TT+SS,TT-SS,P)/(x-SS[1]);
W:=l(2*TT+SS,2*TT-SS,P)/(x-SS[1]);

//calculating the action of the cocycle on functions Z and W
Zt:=l(TT+SS,TT-SS,p)/(p[1]-SS[1]);
Wt:=l(2*TT+SS,2*TT-SS,p)/(p[1]-SS[1]);

Zt/Z; //Zt/Z=zeta_3 -> Z/d^(1/3) is the correct function that is in the function field of the twist
Wt/W; //Wt/W=(zeta_3)^2 -> W/d^(2/3) is the correct function that is in the function field of the twist

//Riemann-Rocha space
Div:=DivisorGroup(E);
D:=Divisor(Div, [<Place(S),1>, <Place(-S),1>, <Place(O),1>]);
L_3D, inv_map:=RiemannRochSpace(3*D);
_map:=Inverse(inv_map);
vekt:=[_map(1), _map(Z), _map(Z^2), _map(Z^3), _map(W), _map(Z*W), _map(Z^2*W), _map(W^2), _map(Z*W^2), _map(W^3) ];
c:=Kernel(Matrix(vekt));
R<z,w>:=PolynomialRing(K,2);
monomi:=[z^0,z,z^2,z^3,w,z*w,z^2*w,w^2,z*w^2,w^3];
polynoms:=[];
for i:=1 to (Dimension(c)) do
    polynoms:=Append(polynoms,polinom(c.i,monomi));
end for;
f:=GCD(polynoms);
f; //relation for the functions Z i W (here we need to scale Z by d^(1/3) and W by d^(2/3) in order to get the equation for the functions in the paper)

// define the curve C and maps varphi and phi
A<u,v> := AffineSpace(K,2);
C<U,V> := Curve(A, Evaluate(f,[u,v]));
varphi := map< E -> C | [Z,W] >;
test,phi := IsInvertible(varphi);

//checking that phi^\sigma \circ phi is the translation by S map
 phi(C(FE)![Zt,Wt]) eq E(FE)!p;