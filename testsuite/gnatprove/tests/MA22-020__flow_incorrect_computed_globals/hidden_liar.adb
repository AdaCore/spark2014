package body Hidden_Liar
  with SPARK_Mode => Off
is
   Secret_Var : constant Integer := 1;

   procedure Add (X, Y : in     Integer;
                  Z    :    out Integer)
   is
   begin
      Z := X + Y + Secret_Var;
   end Add;
end Hidden_Liar;
