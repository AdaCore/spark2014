procedure P is
   type Color is (Red, Blue, Green);

   type Volt is delta 0.125 range 0.0 .. 255.0;

   type Money is delta 0.01 digits 15;

   function Ident (N : Natural) return Natural with
     Pre  => (N /= Natural'Last),
     Post => (Ident'Result = N);

   function Ident (N : Natural) return Natural is
   begin
      return Natural'Pred (Natural'Succ (N));
   end Ident;

   function Ident (C : Color) return Color with
     Pre  => (C /= Color'Last),
     Post => (Ident'Result = C);

   function Ident (C : Color) return Color is
   begin
      return Color'Pred (Color'Succ (C));
   end Ident;

   function Ident (V : Volt) return Volt with
     Pre  => (V /= Volt'Last),
     Post => (Ident'Result = V);

   function Ident (V : Volt) return Volt is
   begin
      return Volt'Pred (Volt'Succ (V));
   end Ident;

   function Ident (M : Money) return Money with
     Pre  => (M /= Money'Last),
     Post => (Ident'Result = M);

   function Ident (M : Money) return Money is
   begin
      return Money'Pred (Money'Succ (M));
   end Ident;

   function Ident (F : Float) return Float with
     Pre  => (F /= Float'Last),
     Post => (Ident'Result = F);

   function Ident (F : Float) return Float is
   begin
      return Float'Pred (Float'Succ (F));
   end Ident;

begin
   null;
end P;
