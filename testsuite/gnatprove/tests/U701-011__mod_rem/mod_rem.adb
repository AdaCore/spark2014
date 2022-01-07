with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Mod_Rem (A, B : Integer) with
  Pre => B /= 0
is
   BigA : constant Big_Integer := To_Big_Integer (A);
   BigB : constant Big_Integer := To_Big_Integer (B);

   function Same_Sign (X, Y : Integer) return Boolean is
      ((X >= 0 and Y >= 0) or (X <= 0 and Y <= 0));

begin
   --  Defining relation for integer division and remainder (Ada RM 4.5.5(5))
   pragma Assert (BigA = (BigA / BigB) * BigB + To_Big_Integer (A rem B));
   --  (A rem B) has the sign of A
   pragma Assert (Same_Sign (A rem B, A));
   --  (A rem B) has an absolute value less than the absolute value of B
   pragma Assert (abs (To_Big_Integer (A rem B)) < abs (BigB));
   --  Identity satisfied by signed integer division
   pragma Assert (if A /= Integer'First then (-A)/B = -(A/B));
   pragma Assert (if A /= Integer'First and B /= Integer'First then -(A/B) = A/(-B));

   --  The signed integer modulus operator is defined such that the result of A
   --  mod B is either zero, or has the sign of B and an absolute value less
   --  than the absolute value of B.
   pragma Assert (Same_Sign (A mod B, B));
   pragma Assert (abs (To_Big_Integer (A mod B)) < abs (BigB));
   --  Identity satisfied by signed integer modulus
   pragma Assert (for some N in Integer =>
                    BigA = BigB * To_Big_Integer (N) +
                    To_Big_Integer (A mod B));
end;
