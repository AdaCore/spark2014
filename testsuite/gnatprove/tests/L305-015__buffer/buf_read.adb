package body Buf_Read is

   Buf_Size : constant := 1000;

   type Index_Type is new Integer;
   subtype Real_Index_Type is Index_Type range 1 .. Buf_Size;

   type Buffer_Type is array (Index_Type range <>) of Character;

   Buffer : Buffer_Type (Real_Index_Type);

   Pointer : Real_Index_Type;

   Max_Read : Real_Index_Type;

   function Valid (C : Character) return Boolean is
      pragma SPARK_Mode (Off);
      type Non_Alfa is access Integer;
   begin
      return True;
   end Valid;

   function Valid_State return Boolean is
      (Pointer <= Max_Read and then
         (for all Index in Buffer'First .. Max_Read =>
             Valid (Buffer (Index))));

   procedure Read (B : out Buffer_Type; Count : out Index_Type)
      with Post =>
         (Count in B'Range and then
            (for all Index in B'First .. (B'First + Count) - 1 =>
             Valid (B (Index))));

   procedure Read (B : out Buffer_Type; Count : out Index_Type)
   is
      pragma SPARK_Mode (Off);
      type Non_Alfa is access Integer;
   begin
      Count := 1;
   end Read;

   procedure Next_Char (C : out Character) is
   begin
      C := Buffer (Pointer);
      if Pointer = Max_Read then
         --  We read the last character, fetch more
         Read (Buffer, Max_Read);
         Pointer := Buffer'First;
      else
         Pointer := Pointer + 1;
      end if;

   end Next_Char;

end Buf_Read;
