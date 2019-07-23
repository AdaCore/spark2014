-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal: the loan exceeds the lifetime of the borrowed reference

with Ada.Text_IO;
use Ada.Text_IO;

procedure N09b is
   package Data is
      type AI is access Integer;
      type AAI is access AI;
      procedure Copy_Pointer (A : in AAI; B: out AI)
        with
          Global => null,
          Depends => (B => (A));
          --ERROR: (B) cannot Depend on an `in' parameter (A)
   end Data;
   package body Data is
      procedure Copy_Pointer (A : in AAI; B: out AI) is --move (A) (B)
      begin
         B:= A.all; --move of (A.all.all) occurs here
      end Copy_Pointer;


   end Data;
   use Data;
   X : AI := new Integer'(1);
   Y : AAI := new AI'(X); --move of (X) occurs here
   Z : AI;
begin

   Copy_Pointer (Y, Z); --move of (Y) and (Z) occurs here

end N09b;
