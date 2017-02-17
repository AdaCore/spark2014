procedure P is
   type Color is (Red, Blue, Green);

   type Volt is delta 0.125 range 0.0 .. 255.0;

   type Money is delta 0.01 digits 15;

   function Ident (N : Natural) return Natural with
     Pre => (N in 1 .. 10);

   function Ident (N : Natural) return Natural is
   begin
      return N;
   end Ident;

   function Ident (C : Color) return Color with
     Pre => (C in Red .. Blue);

   function Ident (C : Color) return Color is
   begin
      return C;
   end Ident;

   function Ident (V : Volt) return Volt with
     Pre => (V in 0.125 .. 1.125);

   function Ident (V : Volt) return Volt is
   begin
      return V;
   end Ident;

   function Ident (M : Money) return Money with
     Pre  => (M in 0.1 .. 10.1);

   function Ident (M : Money) return Money is
   begin
      return M;
   end Ident;

   function Ident (F : Float) return Float with
     Pre  => (F in -0.999 .. 0.999);

   function Ident (F : Float) return Float is
   begin
      return F;
   end Ident;

   N : Natural := Ident (5);
   C : Color   := Ident (Red);
   V : Volt    := Ident (0.725);
   M : Money   := Ident (1.2);
   F : Float   := Ident (-0.112);
begin
   null;
end P;
