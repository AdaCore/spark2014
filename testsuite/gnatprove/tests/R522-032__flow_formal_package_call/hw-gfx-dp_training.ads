with HW.GFX.DP_Aux_Ch;
with HW.GFX.DP_Info;

private generic
   with package Aux_Ch is new DP_Aux_Ch (others => <>);
   with package DP_Info is new GFX.DP_Info (Aux_Ch => Aux_Ch);
package HW.GFX.DP_Training
is

   procedure Train_DP;

end HW.GFX.DP_Training;
