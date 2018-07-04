with HW.GFX.DP_Aux_Ch;

private generic

   type T (<>) is limited private;

   with package Aux_Ch is new DP_Aux_Ch (T => T);

package HW.GFX.DP_Info is
   type Train_Set is record
      Voltage : Integer;
   end record;
end;
