package body Repro.B
is

   procedure Foo (Word : A.Word64) is
   begin
      if not A.Is_Undefined (Word) then
         return;
      else
         null;
      end if;
   end;

end Repro.B;
