with G;
with P;
--  This instantiation fails because the body of G contains
--  non-SPARK constructs.
package G2 is new G (P.T);
