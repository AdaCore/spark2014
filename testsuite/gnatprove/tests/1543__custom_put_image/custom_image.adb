with Ada.Strings.Text_Buffers;

procedure Custom_Image with SPARK_Mode is
   type Number is new Integer with Put_Image => Put;
   procedure Put
     (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
      Value  : Number)
   with SPARK_Mode => Off;

   procedure Put
     (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
      Value  : Number)
   with SPARK_Mode => Off
   is
      pragma Unreferenced (Value);
   begin
      Buffer.Put ("abcdefghijklmnopqrst");
   end Put;

   --  A custom image can exceed the bound of the default image model

   Image : constant String := Number'Image (0);
begin
   pragma Assert (Image'Length <= 12);
end Custom_Image;
