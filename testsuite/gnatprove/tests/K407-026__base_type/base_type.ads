package Base_Type is
   type T is range 1 .. 10;

   function Add1 (X, Y : T) return T
     with Pre => X <= 5 and Y <= 6;

   function Add2 (X, Y : T) return T
     with Pre => X <= 5 and Y <= 4;

   type D is range -3 .. 10;

   function Add3 (X, Y : D) return D
     with Pre => 1 <= X and X <= 5 and Y <= 6;

   function Add4 (X, Y : D) return D
     with Pre => X <= 5 and 0 <= Y and Y <= 4;

   type U is range -5 .. 10;

   function Add5 (X, Y : U) return U
     with Pre => X <= 4 and Y <= 1;

   function Add6 (X, Y : U) return U
     with Pre => X <= 5 and Y <= 0;

   type W is range -6 .. 10;

   function Add7 (X, Y : W) return W
     with Pre => X >= 5 and Y <= -3;

   function Add8 (X, Y : W) return W
     with Pre => Y = -1;
end;
