with HW.GFX.DP_Aux_Ch;
with HW.GFX.GMA.DP_Aux_Request;

private package HW.GFX.GMA.DP_Aux_Ch
   is new HW.GFX.DP_Aux_Ch
     (Aux_Request => DP_Aux_Request.Do_Aux_Request);
