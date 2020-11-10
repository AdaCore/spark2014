with P.Priv;

package body P
  with Refined_State => (State => (A, B, P.Priv.Instance_Gen.State_Gen_Pkg))
is
   B : Integer := 6;

   function F return Boolean is (B > 0);

   package body Nested_Generic_Package
     with Refined_State => (State_Gen_Pkg => C)
   is
      C : Integer := 0;

      procedure Nested_Proc (X : in out Integer)
      is
      begin
        if C = X and A = X then
           X := C;
        end if;
      end;
   begin
      Nested_Proc (C);
   end;
end;
