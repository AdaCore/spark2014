package Overloading
is

   type Complex is
      record
         Re, Im : Float;
      end record;

   I : constant Complex := (0.0, 1.0);

   function "+"(X,Y : Complex) return Complex;

   procedure Overload
     ( J, K : in Integer; I : out Integer;
      B, C  : in Complex; A : out Complex);

end Overloading;
