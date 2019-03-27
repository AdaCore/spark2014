-- Forbidden examples : we do not want this to happen in Spark.
-- should be illegal : we create an RO alias from a RW pointer at the same scope

-- TODO: if we allow moving for in parameters, then there will be problems in
-- the flow analysis (Depends section)

with Ada.Text_IO;
use Ada.Text_IO;

procedure N08b is
   package Data is
      type ACI is access Integer;
      type MyStruct is record
         A,B : ACI;
      end record;
      type AM is not null access MyStruct;
      procedure Inc_and_get (A : in AM; B: out ACI)
        with
          Global => null,
          Depends => (B => (A)) --want to add A=>(A)
          ;
          --ERROR: (B) cannot Depend on an `in' parameter (A)
   end Data;
   package body Data is
      procedure Inc_and_get (A : in AM; B: out ACI) is
      --move during call (A), move during call argument (B)
      begin
         A.all.A := A.all.A + 1; -- assignment to (A.all.A): OK

         B := A.all.A'Access; -- move of (A.all.A) occuring here
         --ERROR: cannot move (A.all.A): extension of restricted on move (A)

      end Inc_and_get;


   end Data;
   use Data;

   X : aliased MyStruct := MyStruct'(A => 10, B => 12);
   Y : AM := X'Access; --move of (X) occurs here
   Z : ACI;
begin
   Put_Line ("X.A =" & Integer'Image(X.A)
             & ", X.B =" & Integer'Image(X.B)
             & ", Y.all.A =" & Integer'Image(Y.all.A)
             & ", Y.all.B =" & Integer'Image(Y.all.B) ); --DEBUG


   Inc_and_get (Y, Z); --move during call of (Y) and (Z) occurs here

   --(Y) and (Z) are not moved anymore

   Put_Line ("X.A =" & Integer'Image(X.A)
             & ", X.B =" & Integer'Image(X.B)
             & ", Y.all.A =" & Integer'Image(Y.all.A)
             & ", Y.all.B =" & Integer'Image(Y.all.B)
             & ", Z.all =" & Integer'Image(Z.all) ); --DEBUG
end N08b;
