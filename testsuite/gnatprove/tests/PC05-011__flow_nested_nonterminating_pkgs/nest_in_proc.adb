procedure Nest_In_Proc is

   package Inner1 is
      procedure Dummy;
   end;

   package Inner2 is
      procedure Dummy;
   end;

   package body Inner1 is
      procedure Dummy is null;
   begin
      while True loop
         null;
      end loop;
   end;

   package body Inner2 is
      procedure Dummy is null;
   begin
      while True loop
         null;
      end loop;
   end;

begin
   null;
end Nest_In_Proc;
