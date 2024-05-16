pragma SPARK_Mode (Off);

package body Random is

   Is_Init : Boolean := False
   with Ghost;

   function Is_Initialised return Boolean
   is (Is_Init);

   procedure Initialise
   is
      procedure Init
      with Import => True,
           Convention => C,
           External_Name => "init";
   begin
      Init;
      Is_Init := True;
   end Initialise;

   procedure Get (Data : out Random_Bits)
   is
      procedure Get_Random (Data : access Random_Bits)
      with Import => True,
           Convention => C,
           External_Name => "get_random";

      Value : aliased Random_Bits;
   begin
      Get_Random (Value'Access);
      Data := Value;
   end Get;

end Random;
