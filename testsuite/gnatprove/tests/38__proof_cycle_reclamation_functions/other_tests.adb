with P3; use P3;

package body Other_Tests is

   V : T;

   --  CFG of P1 should show a proof dependency on Is_Null on the assignment.
   procedure P1 is
   begin
      V := Create;
   end P1;

   --  CFG of P2 should show a proof dependency on Is_Null on the out
   --  param of P, but shouldn't show a proof dependency on Is_Null on the in
   --  param of Q.
   procedure P2 is

      procedure P (Value : out T) with Global => null;

      procedure P (Value : out T) is
      begin
         Value := Create;
      end P;

      procedure Q (Value : in T) with Global => null;

      procedure Q (Value : in T) is
      begin
         null;
      end Q;

   begin
      P (V);
      Q (V);
   end P2;
end Other_Tests;
