with System.Storage_Elements;

package body ModeSwitch is  

   Inputs : Modes;

   Input_Ext : Modes;
   for Input_Ext'Address use System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   function PF_Read return Modes is
      (Inputs);

   procedure Read( Value : out Modes) is
   begin
      Inputs := Input_Ext;
      Value  := Inputs;
   end Read;

end ModeSwitch;
