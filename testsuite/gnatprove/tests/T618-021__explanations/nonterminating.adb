procedure Nonterminating (I : Natural) with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, Nonterminating);

   procedure Infinite_Loop is
      X : Integer := 1;
   begin
      while X /= 0 loop
         X := -X;
      end loop;
   end Infinite_Loop;

   function Infinite_Recursion (I : Integer) return Boolean is
   begin
      return Infinite_Recursion (0);
   end Infinite_Recursion;

begin
   while Infinite_Recursion (I) loop
      null;
   end loop;
   Infinite_Loop;
   if I = 0 then
      return;
   else
      Nonterminating (I - 1);
   end if;
end Nonterminating;
