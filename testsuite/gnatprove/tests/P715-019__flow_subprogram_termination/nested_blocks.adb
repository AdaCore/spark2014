package body Nested_Blocks is

begin
B1 : declare
     begin
       B2 : declare
            begin
              B3 : declare
                   begin
                     L : while True loop
                            null;
                         end loop L;
                   end B3;
            end B2;
     end B1;
end Nested_Blocks;
