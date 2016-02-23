procedure Main is

   generic
      type T is private;
   package Gen is
      Dummy : T;

      procedure Set (X : T)
      with
        Global => (Output => Dummy),
        Post   => Dummy = X;
   end;

   package body Gen is
      procedure Set (X : T) is
         Local : Integer := 0;
      begin
         Dummy := X;
         pragma Assert (Local = 0);
      end;
   end;

   package Inst is new Gen (Integer);

begin
   Inst.Set (0);
end;
