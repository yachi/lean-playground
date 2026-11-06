\\ PARI/GP script that produced the cofactors in LeanPlayground/PerfectCuboid/ThirdConjecture.lean.
\\ Run: gp -q -s 4G scripts/third-cuboid/certificates.gp
f = y^6 + (6*c^2-2*a^2-2*b^2)*y^5 + (c^4+b^4+a^4+4*a^2*c^2+4*b^2*c^2-12*b^2*a^2)*y^4 \
  + (6*a^4*c^2+6*c^2*b^4-8*a^2*b^2*c^2-2*c^4*a^2-2*c^4*b^2-2*a^4*b^2-2*b^4*a^2)*y^3 \
  + (4*c^2*b^4*a^2+4*a^4*c^2*b^2-12*c^4*a^2*b^2+c^4*a^4+c^4*b^4+a^4*b^4)*y^2 \
  + (6*a^4*c^2*b^4-2*c^4*a^4*b^2-2*c^4*a^2*b^4)*y + c^4*a^4*b^4;
NN = (y+c^2)*(y-b^2)*(y+a^2); DD = 2*(y+b^2)*(y^2-a^2*c^2);
U = 2*c*y*(DD^2+NN^2); V = 2*NN*DD*(y-c^2); W = (y-c^2)*(DD^2-NN^2);
Dp = 2*a*(c^2*NN^2+y*DD^2); Ep = b*((y+c^2)*(DD^2+NN^2)+2*NN*DD*(y-c^2));
G = (y+c^2)*(DD^2+NN^2);
\\ sextic_identity_one / _two: cofactors of f; sextic_identity_three: identity
q1 = divrem(U^2+y*V^2-Dp^2, f, y); print("identity one, remainder 0: ", q1[2] == 0);
q2 = divrem(U^2+y*W^2-Ep^2, f, y); print("identity two, remainder 0: ", q2[2] == 0);
print("identity three: ", U^2+y*(V^2+W^2)-y*G^2 == 0);
print("Q1 = ", q1[1]); print("Q2 = ", q2[1]);
\\ nn_sub_dd_ne_zero / nn_add_dd_ne_zero: resultant certificates A*f + B*(NN -+ DD) = R
\ (factor() hides the constant -2048, so divide by the product explicitly)
rm = polresultantext(f, NN-DD, y);
P1 = c^4*b^4*(b-c)^4*(b+c)^4*a^6*(a-b)^2*(a+b)^2*(a-c)^3*(a+c)^3*(c*a-b^2)*(c*a+b^2);
print("R(nn-dd) / P1 = ", rm[3]/P1);
rp = polresultantext(f, NN+DD, y);
P2 = c^4*b^4*(b-c)^3*(b+c)^3*a^4*(a-b)^2*(a+b)^2*(a-c)^3*(a+c)^3*(c*a-b^2)*(c*a+b^2)*(a^2-c*b)*(a^2+c*b);
print("R(nn+dd) / P2 = ", rp[3]/P2);
