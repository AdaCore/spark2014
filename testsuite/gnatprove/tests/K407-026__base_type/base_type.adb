package body Base_Type is

   function Add1 (X, Y : T) return T is
   begin
      return (X + Y) - 1;  --  ok
   end;

   function Add2 (X, Y : T) return T is
   begin
      return (X + Y) + 1;  --  ok
   end;

   function Add3 (X, Y : D) return D is
   begin
      return (X + Y) - 1;  --  ok
   end;

   function Add4 (X, Y : D) return D is
   begin
      return (X + Y) + 1;  --  ok
   end;

   function Add5 (X, Y : U) return U is
   begin
      return ((X + Y) - 1) + 6;  --  ok
   end;

   function Add6 (X, Y : U) return U is
   begin
      return (X + Y) + 5;  --  ok
   end;

   function Add7 (X, Y : W) return W is
   begin
      return (X + Y) - 5;  --  ok
   end;

   function Add8 (X, Y : W) return W is
   begin
      return (X + Y) + 1;  --  ok
   end;
end;
