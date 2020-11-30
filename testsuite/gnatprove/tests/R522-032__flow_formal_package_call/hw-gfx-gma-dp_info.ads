with HW.GFX.DP_Info;
with HW.GFX.GMA.DP_Aux_Ch;

private package HW.GFX.GMA.DP_Info
   is new HW.GFX.DP_Info
     (Aux_Ch => DP_Aux_Ch);
