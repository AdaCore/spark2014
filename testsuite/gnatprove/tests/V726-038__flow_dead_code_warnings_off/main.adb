procedure Main is
   A   : constant Integer := 30 with Warnings => Off;
   B   : constant Integer := 30;

   Dummy : Integer := 0;

   function Foo return Integer is
      C : Integer := 0;
      procedure P (I : Integer) with
        Import,
        Global => (Input => Dummy),
        Annotate => (GNATprove, Always_Return);
   begin
      if A /= 30 then
         while C <= 3 loop
            C := C + 1;
            pragma Assert (C >= C'Loop_Entry);
         end loop;
         P (C);
         return C;
      else
         return 1;
      end if;
   end Foo;

   function Bar return Integer is
      C : Integer := 0;
      procedure P (I : Integer) with
        Import,
        Global => (Input => Dummy),
        Annotate => (GNATprove, Always_Return);
   begin
      if B /= 30 then
         while C <= 3 loop
            C := C + 1;
            pragma Assert (C >= C'Loop_Entry);
         end loop;
         P (C);
         return C;
      else
         return 1;
      end if;
   end Bar;
begin
   null;
end Main;
