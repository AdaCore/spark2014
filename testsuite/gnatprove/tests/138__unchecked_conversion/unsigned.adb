with Ada.Unchecked_Conversion;

procedure Unsigned is

   type M32 is mod 2**32 with Size => 32;
   type U32 is range 0 .. 2**32-1 with Size => 32;
   type S32 is range -2**31 .. 2**31-1 with Size => 32;

   function M32_To_U32 is new Ada.Unchecked_Conversion (Source => M32, Target => U32);
   function U32_To_M32 is new Ada.Unchecked_Conversion (Source => U32, Target => M32);

   function M32_To_S32 is new Ada.Unchecked_Conversion (Source => M32, Target => S32);
   function S32_To_M32 is new Ada.Unchecked_Conversion (Source => S32, Target => M32);

   function S32_To_U32 is new Ada.Unchecked_Conversion (Source => S32, Target => U32);
   function U32_To_S32 is new Ada.Unchecked_Conversion (Source => U32, Target => S32);

   procedure Test_M32_U32 (X : M32; Y : U32)
     with Global => null
   is
      Conv_X : constant U32 := M32_To_U32 (X);
      Conv_Y : constant M32 := U32_To_M32 (Y);
   begin
      pragma Assert (if X = 2**31 then Conv_X = 2**31);
      pragma Assert (if Conv_X = 2**31 then X = 2**31);

      pragma Assert (if X = 2**32-1 then Conv_X = 2**32-1);
      pragma Assert (if Conv_X = 2**32-1 then X = 2**32-1);

      pragma Assert (if Y = 2**31 then Conv_Y = 2**31);
      pragma Assert (if Conv_Y = 2**31 then Y = 2**31);

      pragma Assert (if Y = 2**32-1 then Conv_Y = 2**32-1);
      pragma Assert (if Conv_Y = 2**32-1 then Y = 2**32-1);
   end;

   procedure Test_M32_S32 (X : M32; Y : S32)
     with Global => null
   is
      Conv_X : constant S32 := M32_To_S32 (X);
      Conv_Y : constant M32 := S32_To_M32 (Y);
   begin
      pragma Assert (if X = 2**31 then Conv_X = -2**31);
      pragma Assert (if Conv_X = -2**31 then X = 2**31);

      pragma Assert (if X = 2**32-1 then Conv_X = -1);
      pragma Assert (if Conv_X = -1 then X = 2**32-1);

      pragma Assert (if Y = -1 then Conv_Y = 2**32-1);
      pragma Assert (if Conv_Y = 2**32-1 then Y = -1);
   end;

   procedure Test_S32_U32 (X : S32; Y : U32)
     with Global => null
   is
      Conv_X : constant U32 := S32_To_U32 (X);
      Conv_Y : constant S32 := U32_To_S32 (Y);
   begin
      pragma Assert (if X = -2**31 then Conv_X = 2**31);
      pragma Assert (if Conv_X = 2**31 then X = -2**31);

      pragma Assert (if X = -1 then Conv_X = 2**32-1);
      pragma Assert (if Conv_X = 2**32-1 then X = -1);

      pragma Assert (if Y = 2**32-1 then Conv_Y = -1);
      pragma Assert (if Conv_Y = -1 then Y = 2**32-1);
   end;

begin
   Test_M32_U32 (2**31, 2**31);
   Test_M32_U32 (2**32-1, 2**32-1);
   Test_M32_S32 (2**31, -2**31);
   Test_M32_S32 (2**32-1, -1);
   Test_S32_U32 (-2**31, 2**31);
   Test_S32_U32 (-1, 2**32-1);
end;
