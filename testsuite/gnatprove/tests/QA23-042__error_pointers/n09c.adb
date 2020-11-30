-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal: the loan exceeds the lifetime of the borrowed reference

with Ada.Text_IO;
use Ada.Text_IO;

procedure N09c is
   package Data is
      type AI is access Integer;
      type ACAI is access AI;
      procedure Copy_Pointer (A : in ACAI; B: out AI) with
        Global => null,
        Depends => (B => A, A => A);
   end Data;
   package body Data is
      procedure Copy_Pointer (A : in ACAI; B: out AI) is --peek (A) move (B)
      begin
         B:= A.all; --move of (A.all.all) occurs here
         --ERROR cannot move (A.all.all): extension of peeked (A)
      end Copy_Pointer;


   end Data;
   use Data;
   X : AI := new Integer'(1);
   Y : ACAI := new AI'(X); --move of (X) occurs here
   Z : AI;
begin

   Copy_Pointer (Y, Z); --peek of (Y) and move of(Z) occurs here

end N09c;
