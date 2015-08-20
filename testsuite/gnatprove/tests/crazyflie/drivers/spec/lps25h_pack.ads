--  Package wrapping functions from the lps25h pressure sensor driver

package LPS25h_pack
  with SPARK_Mode
is

   --  Types

   subtype T_Pressure is Float range 450.0 .. 1100.0;  --  in mBar
   subtype T_Temperature is Float range -20.0 .. 80.0; --  in degree Celcius
   subtype T_Altitude is Float range -8000.0 .. 8000.0;

   --  Procedures and functions

   procedure LPS25h_Get_Data
     (Pressure    : out T_Pressure;
      Temperature : out T_Temperature;
      Asl         : out T_Altitude;
      Status      : out Boolean)
     with
       Global => null;

end LPS25h_pack;
