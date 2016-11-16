package Rec is

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
      Plop : My_Rec (Z);
   end record;

end Rec;
