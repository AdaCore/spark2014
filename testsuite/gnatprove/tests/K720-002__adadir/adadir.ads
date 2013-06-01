with Ada.Finalization;

package Adadir is
   type Search_Type is private;

private

   type Search_Data;
   type Search_Ptr is access Search_Data;
   type Search_Type is new Ada.Finalization.Controlled with record
      Value : Search_Ptr;
   end record;

end Adadir;
