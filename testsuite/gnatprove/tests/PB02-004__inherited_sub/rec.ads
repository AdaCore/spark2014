package Rec with SPARK_Mode is

   type Enum is (A, B, C);

   subtype Sub_Enum is Enum range A .. B;

   type My_Rec (E : Sub_Enum) is record
      case E is
         when A =>
            X : Integer;
         when B =>
            Y : Float;
      end case;
   end record;

   type Sub_Rec (Z : Enum) is record
      Plop : My_Rec (Z); --@RANGE_CHECK:FAIL
   end record;

   type Sub_Rec_OK (Z : Enum) is record
      case Z is
         when Sub_Enum =>
            Plop : My_Rec (Z);
         when others => null;
      end case;
   end record;

   type My_Array is array (Positive range <>) of Natural;

   type Sub_Arr (F, L : Natural) is record
      Content : My_Array (F .. L); --@RANGE_CHECK:FAIL
   end record;

   type Sub_Arr_OK (F : Positive; L : Natural) is record
      Content : My_Array (F .. L);
   end record;

end Rec;
