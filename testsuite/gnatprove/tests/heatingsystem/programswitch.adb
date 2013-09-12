with System.Storage_Elements;

package body ProgramSwitch is  

   Inputs : Positions;

   Input_Ext : Positions;
   for Input_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   procedure Read( Value : out Positions) is
   begin
      Inputs := Input_Ext;
      Value  := Inputs;
   end Read;

end ProgramSwitch;
