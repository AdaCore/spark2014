procedure Anti_Aliasing is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   type Arr is array (1 .. 10) of Integer;

   type Arr_With_Rec is array (1 .. 10) of Rec;

   Local_1, Local_2 : Integer := 0;

   Rec_1 : Rec := (0, 0);

   Arr_1 : arr := (others => 0);

   Arr_Rec : Arr_With_Rec := (others => (0, 0));

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

   procedure With_In_Out_Global (I : in Integer)
     with Global => (In_Out => Local_1)
   is
   begin
      Local_1 := I + Local_1;
   end With_In_Out_Global;

   procedure With_Composite_In_Out_Global (I : in Integer)
     with Global => (In_Out => Rec_1)
   is
   begin
      Rec_1.X := I + Rec_1.X;
   end With_Composite_In_Out_Global;

begin
   -- This is ok because parameters are by copy and there
   -- is only one out parameter
   One_In_One_Out (Local_1, Local_1);

   -- This is erroneous both parameters are in out and
   -- the actual parameters overlap
   Two_In_Out (Local_1, Local_1);

   -- This is ok the variables do not overlap even though
   -- they are part of the same record.
   Two_In_Out (Rec_1.X, Rec_1.Y);

   -- This is ok the variables do not overlap they
   -- can statically determined to be distinct elements
   Two_In_Out (Arr_1 (1), Arr_1 (2));

   -- This is erroneous because it cannot be determined statically
   -- whether the elements overlap
   Two_In_Out (Arr_1 (Local_1), Arr_1 (Local_2));

   -- This is ok the variables do not overlap they
   -- can statically determined to be distinct components
   Two_In_Out (Arr_Rec (Local_1).X , Arr_Rec (Local_2).Y);

   -- This erroneous Global and formal in out parameter overlap.
   With_In_Global (Local_1);

   -- This erroneous Global In_Out and formal parameter overlap.
   With_In_Out_Global (Local_1);

   -- This erroneous Global In_Out and formal parameter overlap.
   With_Composite_In_Out_Global (Rec_1.Y);

end Anti_Aliasing;
