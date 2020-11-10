with HW.GFX.DP_Training;
with HW.GFX.GMA.DP_Aux_Ch;
with HW.GFX.GMA.DP_Info;

package body HW.GFX.GMA.PCH.DP is

   procedure On
   is
      package Training is new DP_Training
        (Aux_Ch  => DP_Aux_Ch,
         DP_Info => DP_Info);
   begin
      null;
   end On;

end HW.GFX.GMA.PCH.DP;
