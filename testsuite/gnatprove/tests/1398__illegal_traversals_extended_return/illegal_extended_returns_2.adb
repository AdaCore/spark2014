procedure Illegal_Extended_Returns_2 with SPARK_Mode is

   --  No need to traverse such extended returns to havoc borrowed objects,
   --  as borrowers in traversal functions are observes.

   function Illegal_Write (X : aliased in out Integer) return not null access Integer with Global => null is
   begin
      return B : not null access Integer := X'Access do
         B.all := 2;
      end return;
   end Illegal_Write;

begin
   null;
end;
