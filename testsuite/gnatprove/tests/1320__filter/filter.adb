procedure Filter with SPARK_Mode is

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

   procedure Partition
     (Arr : in out Ptr_Array; Threshold : Integer; Part : out Integer)
   with
     Pre  =>
       Arr'Length > 1
       and then Arr'Last < Positive'Last
       and then (for all I in Arr'Range => Arr (I) /= null),
     Post =>
       (for all I in Arr'Range =>
          (if I <= Part
           then Arr (I).all <= Threshold
           else Arr (I).all >= Threshold));

   procedure Partition
     (Arr : in out Ptr_Array; Threshold : Integer; Part : out Integer)
   is
      I : Integer := Arr'First;
   begin
      Part := Arr'Last;
      while I <= Part loop
         pragma Loop_Invariant ((for all K in Arr'Range => Arr (K) /= null));
         pragma Loop_Invariant (I in Arr'First .. Arr'Last + 1);
         pragma Loop_Invariant (Part in Arr'First - 1 .. Arr'Last);
         pragma Loop_Invariant (I <= Part + 1);
         pragma
           Loop_Invariant
             ((for all K in Integer range Part + 1 .. Arr'Last =>
                 Arr (K).all > Threshold));
         pragma
           Loop_Invariant
             ((for all K in Integer range Arr'First .. I - 1 =>
                 Arr (K).all <= Threshold));
         pragma Assert (I in Arr'Range);
         pragma Assert (Part in Arr'Range);
         if Arr (I).all > Threshold then
            if I < Part then
               declare
                  Tmp : Int_Acc := null;
               begin
                  Swap (Tmp, Arr (I));
                  Swap (Arr (Part), Tmp);
                  Swap (Arr (I), Tmp);
               end;
            end if;
            Part := Part - 1;
         else
            I := I + 1;
         end if;
      end loop;
      pragma Assert (I = Part + 1);
      pragma Assert
        ((for all K in Arr'Range =>
            (if K <= Part
             then Arr (K).all <= Threshold
             else Arr (K).all >= Threshold)));
   end Partition;

begin
   null;
end Filter;
