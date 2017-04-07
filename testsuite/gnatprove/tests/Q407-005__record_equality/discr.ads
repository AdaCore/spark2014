package Discr
with SPARK_Mode
is
   type T_Array is array(Positive range <>, Positive range <>) of Integer;

   type T_Record(Row_First : Positive;
                 Row_Last  : Positive;
                 Col_First : Positive;
                 Col_Last  : Positive)
   is
      record
         Data : T_Array(Row_First .. Row_Last, Col_First .. Col_Last);
      end record;

   procedure Test(Rec : in T_Record);
end Discr;
