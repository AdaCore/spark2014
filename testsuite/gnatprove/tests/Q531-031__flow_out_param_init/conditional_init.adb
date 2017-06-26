package body Conditional_Init is

   type T_1 is record
      Value : Integer;
   end record;

   type T_2 is record
      Value : Integer := 0;
   end record;

   procedure Test_01 (X    : out T_1;
                      Y    : out T_2;
                      Flag : Boolean)
   with Global => null
   is
   begin
      if Flag then
         X.Value := 1;
         Y.Value := 1;
      end if;
   end Test_01;

end Conditional_Init;
