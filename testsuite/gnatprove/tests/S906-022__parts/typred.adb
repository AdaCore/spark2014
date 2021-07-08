package body Typred is

   procedure P (X : in out S) is
   begin
      X.A := not X.A;
   end P;
end Typred;
