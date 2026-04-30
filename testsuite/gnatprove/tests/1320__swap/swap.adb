procedure Swap with SPARK_Mode is

   type Int_Acc is access Integer;
   type Ptr_Array is array (Positive range <>) of Int_Acc;

   function Logic_Eq (X, Y : Int_Acc) return Boolean
   is (if X = null then Y = null else Y /= null and then X.all = Y.all);

   function Deep_Copy (X : Int_Acc) return Int_Acc
   with
     Import,
     Global => null,
     Ghost  => Static,
     Post   => Logic_Eq (Deep_Copy'Result, X);

   procedure Swap (Source, Target : in out Int_Acc)
   with
     Post =>
       (Static =>
          Logic_Eq (Source, Deep_Copy (Target)'Old)
          and Logic_Eq (Target, Deep_Copy (Source)'Old));

   procedure Swap (Source, Target : in out Int_Acc) is
      Tmp : Int_Acc := Target;
   begin
      Target := Source;
      Source := Tmp;
   end Swap;

   procedure Swap_Pointers (Arr : in out Ptr_Array; I, J : Positive)
   with Pre => I /= J and then I in Arr'Range and then J in Arr'Range
   is
      X : Int_Acc := null;
   begin
      Swap (X, Arr (I));
      Swap (Arr (J), X);
      Swap (Arr (I), X);
      pragma Unreferenced (X);
   end Swap_Pointers;

begin
   null;
end Swap;
