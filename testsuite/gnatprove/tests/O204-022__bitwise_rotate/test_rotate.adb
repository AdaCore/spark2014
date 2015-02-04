with Interfaces; use Interfaces;
with CommonTypes; use CommonTypes;

procedure Test_Rotate with
  SPARK_Mode
is

   function R (A, B : in CommonTypes.LongWord_t) return CommonTypes.LongWord_t
   with
     Pre => A <= CommonTypes.LongWord_t'Last
            and then A /= CommonTypes.NULLLongWord
            and then B <= CommonTypes.LongWord_t(Integer'Last),
     Post => R'Result /= CommonTypes.NULLLongWord,
     --  This function does not use global variables
     Global => null
   is
      use Interfaces;
   begin
      return Rotate_Left (A, Integer (B));
   end R;
   pragma inline (R);

   X : CommonTypes.LongWord_t;
begin
   X := R (1, 1);
end Test_Rotate;
