with HW.GFX.DP_Aux_Ch;

private generic
   with package Aux_Ch is new DP_Aux_Ch (others => <>);
package HW.GFX.DP_Info is
   type Train_Set is record
      Voltage : Integer;
   end record;
end;
