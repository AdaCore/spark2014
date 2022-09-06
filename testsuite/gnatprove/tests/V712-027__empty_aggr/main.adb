procedure Main with
   SPARK_Mode
is
   type Arr is array (Natural range <>) of Integer;

   Empty : constant Arr := (1 .. 0 => 0);

   procedure Test
     with Pre => [] = Empty
   is
   begin
      if [] /= Empty then
         raise Program_Error;
      end if;
   end Test;

begin
   Test;
end Main;
