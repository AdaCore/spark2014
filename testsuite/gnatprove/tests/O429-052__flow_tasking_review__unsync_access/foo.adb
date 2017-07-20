package body Foo
is

   task T1;

   task T2;

   protected P1 is
      procedure Flip_G;
   end P1;

   --  I think this is an acceptable use of G.
   G : Boolean := False with Part_Of => P1;

   task body T1 is
   begin
      loop
         P1.Flip_G;
      end loop;
   end T1;

   task body T2 is
   begin
      loop
         P1.Flip_G;
      end loop;
   end T2;

   protected body P1 is
      procedure Flip_G is
      begin
         G := not G;
      end Flip_G;
   end P1;

end Foo;
