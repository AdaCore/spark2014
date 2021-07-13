package body GF is

   procedure Read_Fi (Buff_All : out String) is
   begin
      null;
   end Read_Fi;

   procedure R_Generic (Data : out Float) is
      generic
         type PAYLOAD_TYPE_In is private;
      procedure Inialize (Unused_Data : out Float) with
         Global => null;

      procedure Inialize (Unused_Data : out Float) with
         SPARK_Mode => Off
      is
      begin
         null;
      end Inialize;

      procedure In_Data is new Inialize (PAYLOAD_TYPE_In => Float);

      subtype Payload_As_Arr_Type is String (1 .. 10);

      Data_As_Array : Payload_As_Arr_Type with
         Import,
         Address => Data'Address;
   begin
      pragma Warnings (Off, "statement has no effect");

      In_Data (Unused_Data => Data);

      Read_Fi (Buff_All => Data_As_Array);

      pragma Warnings (On, "statement has no effect");
   end R_Generic;

end GF;
