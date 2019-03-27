-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal: the loan exceeds the lifetime of the borrowed reference

with Ada.Text_IO;
use Ada.Text_IO;

procedure N09 is
   package Data is
      type AI is access Integer;
      type AAI is access AI;
      function Copy_Pointer (A : in AAI) return AI;
   end Data;
   package body Data is
      function Copy_Pointer (A : in AAI) return AI is --peeking (A)
      begin
         return A.all; --the loan exceeds the lifetime of the borrow
                                  --move of (A.all.all) occurs here
         --ERROR cannot move (A.all.all): extension of peeked path (A)
      end Copy_Pointer;


   end Data;
   use Data;
   X : AI := new Integer'(1);
   Y : AAI := new AI'(X); --move of (X) occurs here
   Z : AI;
begin

   Z := Copy_Pointer (Y); --peek of (Y) occurs here

end N09;
