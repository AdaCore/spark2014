procedure Hello with SPARK_Mode is
   type T is record
      C : Boolean;
   end record;
   --  A record type to force pass-by-reference

   type T_Ptr is access all T;
   --  A generalized access type, to allow 'Access

   procedure Swap (X, Y : in out T) with Pre => True is
   begin
      null;
   end;
   --  A subprogram with dummy contract to prevent inlining-for-proof

   A : aliased T := (C => True);
begin
   Swap (A, T_Ptr'(A'Access).all); --  this looks like aliasing
end;
