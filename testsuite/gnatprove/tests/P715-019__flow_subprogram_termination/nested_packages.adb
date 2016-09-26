package body Nested_Packages is

   -- Nested packages whitin a procedure
   procedure Contains_Packages is
      -- First nested package definition
      package Pck is
         procedure Null_Pck;
         -- Second nested package definition
         package Pck2 is
            procedure Null_Pck2;
         end Pck2;
      end Pck;

      package body Pck is
         procedure Null_Pck is
         begin
            null;
         end Null_Pck;

         package body Pck2 is
            procedure Null_Pck2 is
            begin
               null;
            end Null_Pck2;
         begin
            while True loop
               null;
            end loop;
         end Pck2;
      begin
         --while True loop
         null;
         --end loop;
      end Pck;

   -- Start of procedure
   begin
      --  while True loop
      null;
      --  end loop;
   end Contains_Packages;

   -- Just nested packages
   package body Nested is
      procedure Do_Nothing is
      begin
         null;
      end Do_Nothing;
      package body Nested2 is
         procedure Do_Nothing2 is
         begin
            null;
         end Do_Nothing2;
      begin
         while True loop
            null;
         end loop;
      end Nested2;

   begin
      while True loop
         null;
      end loop;
   end Nested;

begin
   null;
end Nested_Packages;
