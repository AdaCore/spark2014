package body Only_Abstract_Dependencies with
  SPARK_Mode,
  Refined_State => (Value => V)
is
   V : Integer;

   procedure Add (X : Integer) is
   begin
      V := V + X;
   end Add;

   procedure Swap (X : in out Integer) is
      Tmp : constant Integer := V;
   begin
      V := X;
      X := Tmp;
   end Swap;

   procedure Call_Add (X, Y : Integer) is
   begin
      Add (X);
      Add (Y);
   end Call_Add;

   procedure Call_Swap (X, Y : in out Integer) is
   begin
      Swap (X);
      Swap (Y);
      Swap (X);
   end Call_Swap;

end Only_Abstract_Dependencies;
