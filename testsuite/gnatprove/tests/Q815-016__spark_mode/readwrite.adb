with System;

with Interfaces;

package body Readwrite
is

   type Byte   is new Interfaces.Unsigned_8;
   type Word16 is new Interfaces.Unsigned_16;
   type Word32 is new Interfaces.Unsigned_32;
   type Word64 is new Interfaces.Unsigned_64;

   generic
      type Element_Type is mod <>;
   function Read_Config (Addr : Word64) return Word64;

   generic
      type Element_Type is mod <>;
   procedure Write_Config
     (GPA   : Word64;
      Value : Element_Type);

   -------------------------------------------------------------------------

   function Read_Config (Addr : Word64) return Word64
   with
      SPARK_Mode => Off
   is
      Val : Element_Type
      with
         Import,
         Address => System'To_Address (Addr);
   begin
      return Word64 (Val);
   end Read_Config;

   function Read_Config8  is new Read_Config (Element_Type => Byte);
   function Read_Config16 is new Read_Config (Element_Type => Word16);
   function Read_Config32 is new Read_Config (Element_Type => Word32);

   -------------------------------------------------------------------------

   procedure Write_Config
     (GPA   : Word64;
      Value : Element_Type)
   with
      SPARK_Mode => Off
   is
      Val : Element_Type
      with
         Import,
         Address => System'To_Address (GPA);
   begin
      Val := Value;
   end Write_Config;

   procedure Write_Config8  is new Write_Config (Element_Type => Byte);
   procedure Write_Config16 is new Write_Config (Element_Type => Word16);
   procedure Write_Config32 is new Write_Config (Element_Type => Word32);

   -------------------------------------------------------------------------

   procedure Init
   with
      SPARK_Mode => Off
      --  In the real code this would be SPARK.
   is
   begin
      null;
   end Init;

end Readwrite;
