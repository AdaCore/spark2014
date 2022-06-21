procedure Main with SPARK_Mode is
   type My_Arr is array (Positive range <>) of Natural;
   type Arr_Acc is access My_Arr;

   type Arr_Holder (First : Positive; Last : Natural) is record
      Content : Arr_Acc (First .. Last);
   end record;

   procedure Test (X : Arr_Holder) with
     Global => null
   is
   begin
      pragma Assert
        (X.Content = null or else
           (X.Content'First = X.First and X.Content'Last = X.Last));
      pragma Assert (False); -- @ASSERT:FAIL
   end Test;

   type My_Rec (First : Positive; Last : Natural) is record
      Content : My_Arr (First .. Last);
   end record;

   type Rec_Acc is access My_Rec;

   type Rec_Holder (First : Positive; Last : Natural) is record
      Content : Rec_Acc (First, Last);
   end record;

   procedure Test (X : Rec_Holder) with
     Global => null
   is
   begin
      pragma Assert
        (X.Content = null or else
           (X.Content.First = X.First and X.Content.Last = X.Last
            and X.Content.Content'First = X.First
            and X.Content.Content'Last = X.Last));
      pragma Assert (False); -- @ASSERT:FAIL
   end Test;
begin
   null;
end Main;
