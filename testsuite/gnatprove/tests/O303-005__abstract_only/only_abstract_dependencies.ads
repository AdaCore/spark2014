package Only_Abstract_Dependencies with
  SPARK_Mode,
  Abstract_State => Value
is
   procedure Add (X : Integer) with
     Depends => (Value =>+ X);

   procedure Swap (X : in out Integer) with
     Depends => (Value => X, X => Value);

   procedure Call_Add (X, Y : Integer) with
     Global  => (In_Out => Value),
     Depends => (Value =>+ (X, Y));

   procedure Call_Swap (X, Y : in out Integer) with
     Global  => (In_Out => Value),
     Depends => (X => Y, Y => X, Value => Value);

end Only_Abstract_Dependencies;
