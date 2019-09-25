package body Repro is

   procedure Foo (Low : in Some_Type; High : in Some_Type) is
   begin
      for I in Low .. High loop
         null;
      end loop;
   end Foo;

end Repro;
