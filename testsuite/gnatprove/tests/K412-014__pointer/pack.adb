package body Pack is

   package Ptr is
      procedure Set;
      function Get return Boolean;
   end Ptr;

   package body Ptr is
      pragma SPARK_Mode (Off);

      X : access Boolean := new Boolean;

      procedure Set is
      begin
         X.all := not X.all;
      end Set;

      function Get return Boolean is
      begin
         return X.all;
      end Get;
   end Ptr;

   use Ptr;

   procedure Test is
      A : Boolean := Get;
      B : Boolean;
   begin
      Set;
      B := Get;
      pragma Assert (A = B);
   end Test;

end;
