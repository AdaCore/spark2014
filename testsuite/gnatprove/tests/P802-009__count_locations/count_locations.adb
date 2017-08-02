package body Count_Locations
  with SPARK_Mode
is
   pragma Warnings (GNATprove, Off, "info: function contract not available for proof",
                    Reason => "ignore info messages related to recursive ghost functions");

   function Check_Selected_Locations
     (Sel : Selected_Locations;
      Max : Max_Selected_Locations) return Boolean
   is
      St_Count   : Sum_Type := 0;
      Lowest_Max : Natural := Natural'Last;
   begin
      for St in Index_Type loop
         pragma Loop_Invariant (Count_Selected_Locations(Sel) = St_Count + Partial_Count_Selected_Locations (Sel, St));
         pragma Loop_Invariant (for all S in Index_Type'First .. St - 1 => (if Sel(S) then Max(S) >= Lowest_Max));
         pragma Loop_Invariant (((for all S in Index_Type'First .. St - 1 => not Sel(S)) and Lowest_Max = Natural'Last)
                                   or else
                                (for some S in Index_Type'First .. St - 1 => Sel(S) and Max(S) = Lowest_Max));
         pragma Loop_Invariant (St_Count < St);

         if Sel(St) then
            St_Count := St_Count + 1;

            if Max(St) < Lowest_Max then
               Lowest_Max := Max(St);
            end if;
         end if;
      end loop;

      pragma Assert (St_Count = Count_Selected_Locations(Sel));
      pragma Assert (for all S in Index_Type => (if Sel(S) then Max(S) >= Lowest_Max));

      return St_Count <= Lowest_Max;
   end Check_Selected_Locations;

end Count_Locations;
