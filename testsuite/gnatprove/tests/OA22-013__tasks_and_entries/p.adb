package body P is

   procedure Wrapper
      with Global => (In_Out => PO)
   is
   begin
      PO.Dummy;
   end;

   task body T1 is
   begin
      loop
         PO.Dummy;
      end loop;
   end;

   task body T2 is
   begin
      loop
         Wrapper; A;
      end loop;
   end;

   protected body PO is
      entry Dummy when True is
      begin
         X := not X;
      end;
   end;

   X : Integer := 0;

   procedure A is
   begin
      X := X + 1;
   end;

   procedure B is
   begin
      X := X + 1; A;
   end;

   procedure C is
   begin
      A; B; Wrapper;
   end;
end;
