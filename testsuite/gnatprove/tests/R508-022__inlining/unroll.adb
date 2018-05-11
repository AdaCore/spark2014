procedure Unroll with SPARK_Mode is
   type Channels_Type is range 1 .. 6;

   procedure Sum (Ch : Channels_Type; Res : out Natural)
     with Post => Res = Natural (Ch)
   is
   begin
      Res := 0;
      for X in 1 .. Ch loop
         Res := Res + 1;
      end loop;
   end Sum;

   procedure Sum_Unrolled (Ch : Channels_Type; Res : out Natural)
     with Post => Res = Natural (Ch)
   is
   begin
      Res := 0;
      for X in Channels_Type'Range loop
         Res := Res + 1;
         exit when X = Ch;
      end loop;
   end Sum_Unrolled;

   Value : Natural;
begin
   Sum (4, Value);
   pragma Assert (Value = 4);
   Sum_Unrolled (4, Value);
   pragma Assert (Value = 4);
end Unroll;
