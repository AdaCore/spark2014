package Broken is
   generic
      with function Is_Empty return Boolean;
   package External_Generic is
      procedure Fill_Empty_Slots with
        Post => Is_Empty;
   end External_Generic;
end Broken;
