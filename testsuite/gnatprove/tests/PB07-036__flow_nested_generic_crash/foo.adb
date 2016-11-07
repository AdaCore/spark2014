procedure Foo is

   generic
   procedure factorialp (ip1 : in Integer; ip2 : in out Integer);

   procedure factorialp (ip1 : in Integer; ip2 : in out Integer) is
   begin
      if ip1 = 1 then
         ip2 := 1;
         return;
      else
         factorialp (ip1 - 1, ip2);
         ip2 := ip1 * ip2;
         return;
      end if;

      ip2 := 0;

   end factorialp;

   procedure factp is new factorialp;

begin

   null;

end foo;
