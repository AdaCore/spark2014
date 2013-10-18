package body Update_Legal_2
  with SPARK_Mode
is
   Z : Integer;

   type Record_T is record
      X, Y : Integer;
   end record;

   type Re_Record_T is record
      X2, Y2 : Record_T;
   end record;


   procedure P (R : in out Record_T)
     with Global => (Output => Z)
   is
   begin
      if R'Update (Y => Z).X = 10 then  --  Z is Uninitialized
         R.X := R.Y;
         R.Y := R.Y + 1;
      else
         Z := 10;
      end if;
   end P;


   procedure P2 (Nest_Rec : in out Re_Record_T)
   is
   begin
      Nest_Rec := Nest_Rec'Update(X2 => Nest_Rec.X2'Update (X => Nest_Rec.X2.Y,
                                                            Y => Nest_Rec.X2.X),
                                  Y2 => Nest_Rec.Y2'Update (X => Nest_Rec.Y2.Y,
                                                            Y => Nest_Rec.Y2.X));
   end P2;
end Update_Legal_2;
