procedure P
  with SPARK_Mode
is
   type U is record
      D : Integer;
   end record;
   type T is array (1 .. 2) of U;

   X : T := (others => (D => 42));

   --  Specified Object_Size

   type U2 is record
      D2 : Integer;
   end record with Object_Size => 64;
   type T2 is array (1 .. 2) of U2 with Object_Size => 128;

   X2 : T2 := (others => (D2 => 42));

   --  Specified Value_Size

   type U3 is record
      D3 : Integer;
   end record with Value_Size => 64;
   type T3 is array (1 .. 2) of U3 with Value_Size => 128;

   X3 : T3 := (others => (D3 => 42));

begin
   pragma Assert (U'Size = 32);
   pragma Assert (U'Value_Size = 32);
   pragma Assert (U'Object_Size = 32);

   pragma Assert (T'Size = 64);
   pragma Assert (T'Value_Size = 64);
   pragma Assert (T'Object_Size = 64);

   pragma Assert (X'Size = 64);

   --  Specified Object_Size

   pragma Assert (U2'Size = 32);
   pragma Assert (U2'Value_Size = 32);
   pragma Assert (U2'Object_Size = 64);

   pragma Assert (T2'Size = 128);
   pragma Assert (T2'Value_Size = 128);
   pragma Assert (T2'Object_Size = 128);

   pragma Assert (X2'Size = 128);

   --  Specified Value_Size

   pragma Assert (U3'Size = 64);
   pragma Assert (U3'Value_Size = 64);
   pragma Assert (U3'Object_Size = 64);

   pragma Assert (T3'Size = 128);
   pragma Assert (T3'Value_Size = 128);
   pragma Assert (T3'Object_Size = 128);

   pragma Assert (X3'Size = 128);
end P;
