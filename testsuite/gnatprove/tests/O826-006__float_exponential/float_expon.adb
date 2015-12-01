procedure Float_Expon
  with SPARK_Mode
is
   subtype T is Float range 1.0..2.0;

   procedure Test1 (X : T; Y : in out Float) with
     Global => null
   is
   begin
      Y := 4.0*X**4 + 7.0*X**3-X**2+27.0*X-3.0;
   end Test1;

   procedure Test2 (X : T; Y : in out Float) with
     Global => null
   is
   begin
      Y:= 4.0*X*X*X*X + 7.0*X*X*X -X*X + 27.0*X - 3.0;
   end Test2;

   V : Float := 0.0;
begin
   Test1 (1.0, V);
   Test2 (1.0, V);
end Float_Expon;
