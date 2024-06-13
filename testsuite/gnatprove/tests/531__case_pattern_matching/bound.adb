procedure Bound is
   pragma Assertion_Policy (Check);

   type Rec is record
      F1, F2 : Integer;
   end record;

   type Rec_Rec is record
     F3 : Integer;
     F4 : Rec;
     F5 : Natural;
   end record;

   type Enum is (Case1, Case2, Case3);

   function Classify (X : Rec) return Enum is
   begin
      case X is
         when (F1 => Natural, F2 => Natural is F2_Val) =>
            if F2_Val mod 2 = 0 then
               return Case1;
            else
               return Case2;
            end if;

         when others =>
            return Case3;
      end case;
   end Classify;

   function Classify (Y : Rec_Rec) return Enum is
   begin
      case Y is
         when (F3 => Positive,
               F4 => (F1 => Integer, F2 => Natural is Bound_Val),
               F5 => <>) |
              (F3 => 0,
               F4 => (F1 => Integer is Bound_Val, F2 => Natural),
               F5 => <>) =>
            if Bound_Val mod 2 = 0 then
               return Case1;
            else
               return Case2;
            end if;
         when others =>
            return Case3;
      end case;
   end Classify;
begin
   pragma Assert (Classify (Rec'(123, 456)) = Case1);
   pragma Assert (Classify (Rec'(123, 457)) = Case2);

   pragma Assert (Classify (Rec_Rec'(123, (456, 788), 321)) = Case1);
   pragma Assert (Classify (Rec_Rec'(123, (456, 789), 321)) = Case2);
   pragma Assert (Classify (Rec_Rec'(0, (456, 789), 321)) = Case1);
   pragma Assert (Classify (Rec_Rec'(0, (457, 789), 321)) = Case2);
   pragma Assert (Classify (Rec_Rec'(-1, (0, 0), 321)) = Case3);
end Bound;
