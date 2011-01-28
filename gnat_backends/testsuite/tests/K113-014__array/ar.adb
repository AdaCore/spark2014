package body Ar is

   function Get (X : A) return Integer
   is
   begin
      return X (1);
   end Get;

   procedure Set (X : in out A)
   is
   begin
      X (1) := 5;
   end Set;
end Ar;
