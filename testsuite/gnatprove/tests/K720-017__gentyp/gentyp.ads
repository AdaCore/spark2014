with P;
pragma Elaborate_All(P);
package Gentyp is
   package NP is new P (T => Integer);

   U : NP.B;
   X : NP.A;
end Gentyp;
