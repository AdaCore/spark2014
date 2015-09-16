package body Bar
is

   G : Boolean := False;

   task type T1 (B : Boolean);

   task body T1 is
   begin
      loop
         G := not G;
      end loop;
   end T1;

   --  We should get a check here!
   Task_1 : T1 (False);
   Task_2 : T1 (True);

end Bar;
