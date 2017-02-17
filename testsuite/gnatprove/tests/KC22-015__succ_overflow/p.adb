procedure P is
   type Color is (Red, Blue, Green);

   type Volt is delta 0.125 range 0.0 .. 255.0;

   type Money is delta 0.01 digits 15;

   function Ident (N : Integer) return Integer with
     Pre => (N = Integer'Last);

   function Ident (N : Integer) return Integer is
   begin
      return Integer'Pred (Integer'Succ (N));
   end Ident;

   function Ident (C : Color) return Color with
     Pre  => (C = Color'Last);

   function Ident (C : Color) return Color is
   begin
      return Color'Pred (Color'Succ (C));
   end Ident;

   function Ident (V : Volt) return Volt with
     Pre  => (V = Volt'Last);

   function Ident (V : Volt) return Volt is
   begin
      return Volt'Pred (Volt'Succ (V));
   end Ident;

   function Ident (M : Money) return Money with
     Pre  => (M = Money'Last);

   function Ident (M : Money) return Money is
   begin
      return Money'Pred (Money'Succ (M));
   end Ident;

   function Ident (F : Float) return Float with
     Pre  => (F = Float'Last);

   function Ident (F : Float) return Float is
   begin
      return Float'Pred (Float'Succ (F));
   end Ident;

begin
   null;
end P;
