package body Ar is

   function Get (X : A) return Integer
   is
   begin
      return X (1);
   end Get;

   procedure Set (X : in out A; Y : Integer)
   is
   begin
      X (Y) := 5;
   end Set;
end Ar;
