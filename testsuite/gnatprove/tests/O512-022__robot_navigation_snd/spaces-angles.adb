package body Spaces.Angles is

   function Create return Angle is
   begin
      return (Theta => 0.0);
   end Create;

   function Create (t : Float) return Angle is
   begin
      return (Theta => norm2Pi (t));
   end Create;

   function "+" (This, Other : Angle) return Angle is
   begin
      return (Theta => norm2Pi (This.Theta + Other.Theta));
   end "+";

   function "-" (This, Other : Angle) return Angle is
      myTheta : Float;
   begin
      if This.Theta >= Other.Theta then
         myTheta := This.Theta;
      else
         myTheta := This.Theta + 2.0 * Pi;
      end if;

      return (Theta => norm2Pi (myTheta - Other.Theta));
   end "-";

   function "*" (This : Angle; d : Float) return Angle is
   begin
      return (Theta => norm2Pi (This.Theta * d));
   end "*";

   function dCast (This : Angle) return Float is
   begin
      return This.Theta;
   end dCast;

   function dCastPi (This : Angle) return Float is
   begin
      return normPi (This.Theta);
   end dCastPi;

   function dCastDeg (This : Angle) return Float is
   begin
      return (This.Theta * 180.0 / Pi);
   end dCastDeg;

   function alDiff (This, Other : Angle) return Float is
   begin
      return normPi (Other.Theta - This.Theta);
   end alDiff;

   function ccwDiff (This, Other : Angle) return Float is
      otherTheta : Float;
   begin
      if This.Theta <= Other.Theta then
         otherTheta := Other.Theta;
      else
         otherTheta := Other.Theta + 2.0 * Pi;
      end if;

      return otherTheta - This.Theta;
   end ccwDiff;

   function cwDiff (This, Other : Angle) return Float is
      myTheta : Float;
   begin
      if This.Theta >= Other.Theta then
         myTheta := This.Theta;
      else
         myTheta := This.Theta + 2.0 * Pi;
      end if;

      return Other.Theta - myTheta;
   end cwDiff;

   function almostEqual (This, Other : Angle; toll : Float) return Boolean is
   begin
      return abs (alDiff (This, Other)) < toll;
   end almostEqual;

   function ccwMean (This, Other : Angle) return Angle is
   begin
      if Other.Theta = This.Theta then
         return Create (This.Theta + Pi);
      end if;

      declare
         otherTheta : Float;
      begin
         if This.Theta <= Other.Theta then
            otherTheta := Other.Theta;
         else
            otherTheta := Other.Theta + 2.0 * Pi;
         end if;

         return Create ((otherTheta + This.Theta) / 2.0);
      end;
   end ccwMean;

   function cwMean (This, Other : Angle) return Angle is
      myTheta : Float;
   begin
      if This.Theta >= Other.Theta then
         myTheta := This.Theta;
      else
         myTheta := This.Theta + 2.0 * Pi;
      end if;

      return Create ((Other.Theta + myTheta) / 2.0);
   end cwMean;

   function Print (This : Angle) return String is
   begin
      return Float'Image (This.Theta);
   end Print;

   M_PI : constant := Pi;
   M_2PI : constant := 2.0 * Pi;

   function norm2Pi
     (x : Float)
      return Float
   is
      a : Float := x;
   begin
      if a >= M_2PI or else a < 0.0 then
         a := Float'Remainder (a, M_2PI);        --  in [-2*M_PI,2*M_PI]
         if a < 0.0 then
            a := a + M_2PI; end if;  --  in [0,2*M_PI]
         if a > M_2PI then
            a := a - M_2PI; end if;
      end if;

      return a;
   end norm2Pi;

   function normPi
     (x : Float)
      return Float
   is
      a : Float := x;
   begin
      if a > M_PI or else a <= -M_PI then
         a := Float'Remainder (a, M_2PI);         --  in [-2*M_PI,2*M_PI]
         if a <= -M_PI then
            a := a + M_2PI; end if;
         if a > M_PI then
            a := a - M_2PI; end if;
      end if;

      return a;
   end normPi;

end Spaces.Angles;
