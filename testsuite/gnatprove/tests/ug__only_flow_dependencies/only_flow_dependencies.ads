package Only_Flow_Dependencies with
  SPARK_Mode
is
   V : Integer;

   procedure Add (X : Integer) with
     Depends => (V =>+ X);

   procedure Swap (X : in out Integer) with
     Depends => (V => X, X => V);

   procedure Call_Add (X, Y : Integer) with
     Global  => (In_Out => V),
     Depends => (V =>+ (X, Y));

   procedure Call_Swap (X, Y : in out Integer) with
     Global  => (In_Out => V),
     Depends => (X => Y, Y => X, V => V);

end Only_Flow_Dependencies;
