// Verification: for good a (Q_a root-free), H=0 never occurs
// for any Type 3 direction (A,B,C) with ABC != 0.
// This confirms that the two cases in Step 3 of Part (d) of
// Theorem 2.8 are exhaustive under the root-free hypothesis.

for m in [3,5] do
    i := 1;
    q := 2^i;
    qq := 2^m;
    F := GF(qq);
    P<T> := PolynomialRing(F);
    
    printf "=== m=%o, i=%o, q=%o ===\n", m, i, q;
    
    good_a := [];
    bad_a  := [];
    for a_val in F do
        if a_val eq 0 then continue; end if;
        Qa := T^(q^2+q+1) + a_val*T + 1;
        if #Roots(Qa) eq 0 then
            Append(~good_a, a_val);
        else
            Append(~bad_a, a_val);
        end if;
    end for;
    printf "Good a (Q_a root-free): %o, Bad a (Q_a has root): %o\n",
           #good_a, #bad_a;
    
    // For good a: verify H != 0 for all Type 3 directions
    H_zero_found := false;
    for a_val in good_a do
        for A in F do
            if A eq 0 then continue; end if;
            for B in F do
                if B eq 0 then continue; end if;
                for C in F do
                    if C eq 0 then continue; end if;
                    
                    H_val :=
                        A^(q^2+q+1)
                        + A*B^(q^2+q)*a_val^q
                        + A*B^q*C^(q^2)
                        + A^(q^2+q)*C*a_val
                        + A^q*B^(q^2)*C
                        + A^(q^2)*B*C^q
                        + B^(q^2+q+1)
                        + B^(q^2+q)*C*a_val^(q+1)
                        + B^q*C^(q^2+1)*a_val
                        + B^(q^2)*C^(q+1)*a_val^q
                        + C^(q^2+q+1);
                    
                    if H_val eq 0 then
                        H_zero_found := true;
                        printf "  FAIL: H=0 for good a=%o, A=%o, B=%o, C=%o\n",
                               a_val, A, B, C;
                    end if;
                    
                end for;
            end for;
        end for;
    end for;
    if not H_zero_found then
        printf "CONFIRMED: H != 0 for all Type 3 directions with good a.\n";
    end if;
    
    // For bad a: verify that H=0 does occur (only meaningful when bad_a nonempty)
    if #bad_a eq 0 then
        printf "No bad a exists for m=%o (all parameters are good).\n\n", m;
    else
        H_zero_bad := 0;
        for a_val in bad_a do
            for A in F do
                if A eq 0 then continue; end if;
                for B in F do
                    if B eq 0 then continue; end if;
                    for C in F do
                        if C eq 0 then continue; end if;
                        
                        H_val :=
                            A^(q^2+q+1)
                            + A*B^(q^2+q)*a_val^q
                            + A*B^q*C^(q^2)
                            + A^(q^2+q)*C*a_val
                            + A^q*B^(q^2)*C
                            + A^(q^2)*B*C^q
                            + B^(q^2+q+1)
                            + B^(q^2+q)*C*a_val^(q+1)
                            + B^q*C^(q^2+1)*a_val
                            + B^(q^2)*C^(q+1)*a_val^q
                            + C^(q^2+q+1);
                        
                        if H_val eq 0 then
                            H_zero_bad +:= 1;
                        end if;
                        
                    end for;
                end for;
            end for;
        end for;
        printf "Sanity check: H=0 occurs %o times for bad a.\n\n", H_zero_bad;
    end if;

end for;
