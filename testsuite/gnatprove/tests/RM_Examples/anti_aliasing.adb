procedure Anti_Aliasing is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   type Arr is array (1 .. 10) of Integer;

   Local_1, Local_2 : Integer := 0;

   Rec_1 : Rec := (0, 0);

   Arr_1 : Arr := (others => 0);

   procedure One_In_One_Out (X : in Integer; Y : in out Integer)
   is
   begin
      Y := X + Y;
   end One_In_One_Out;

   procedure Two_In_Out (X, Y : in out Integer) with Global => null
   is
      Temp : Integer;
   begin
      Temp := Y;
      Y := X + Y;
      X := Temp;
   end Two_In_Out;

   procedure With_In_Global (I : in out Integer)
     with Global => Local_1
   is
   begin
      I := I + Local_1;
   end With_In_Global;

begin
   -- This is ok because parameters are by copy and there
   -- is only one out parameter
   One_In_One_Out (Local_1, Local_1);

   -- This is ok the variables do not overlap even though
   -- they are part of the same record.
   Two_In_Out (Rec_1.X, Rec_1.Y);

   -- This is ok the variables do not overlap they
   -- can statically determined to be distinct elements
   Two_In_Out (Arr_1 (1), Arr_1 (2));

   -- This is not ok because Global and formal in out parameter overlap
   With_In_Global (Local_1);

end Anti_Aliasing;
