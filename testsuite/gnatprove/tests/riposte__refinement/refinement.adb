package body Refinement
  with Refined_State => (State => High_Reading)
is
   High_Reading : Reading := 0;

   function Get_Highest_Reading return Reading is (High_Reading)
     with Refined_Global => High_Reading;

   procedure Add_Reading (R : in Reading)
     with Refined_Global  => (In_Out => High_Reading),
          Refined_Depends => (High_Reading =>+ R),
          Refined_Post    => Get_Highest_Reading > Reading'First  --  @REFINED_POST:PASS
   is
   begin
      if R > High_Reading then
         High_Reading := R;
      end if;
   end Add_Reading;

end Refinement;
