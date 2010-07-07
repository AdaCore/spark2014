package body Overloading
is

   procedure Swap (X, Y : in out Integer) is
      T:Integer;
   begin
      T := X; X:= Y; Y:= T;
   end Swap;

   procedure Swap (X, Y : in out Float) is
      T:Float;
   begin
      T := X; X:= Y; Y:= T;
   end Swap;


   procedure Echange (A, B : out Integer; C, D : out Float) is

      procedure Swap (X, Y : in out Long_Integer);

      procedure Swap (X, Y : in out Long_Integer) is
         T:Long_Integer;
      begin
         T := X; X:= Y; Y:= T;
      end Swap;
      E, F : Long_Integer;

   begin
      A := 10;
      B := 20;
      C := 10.0;
      D := 20.0;
      E := 100000;
      F := 200000;

      Swap (A,B);
      Swap (C,D);
      Swap (E,F);
   end Echange;

end Overloading;
