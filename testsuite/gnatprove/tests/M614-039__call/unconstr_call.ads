package Unconstr_Call is

   type T is array (Natural range <>) of Integer;

   procedure P (X : T);

   procedure Havoc (X : in out T);
end Unconstr_Call;
