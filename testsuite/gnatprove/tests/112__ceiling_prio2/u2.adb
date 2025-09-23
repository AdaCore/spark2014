package body U2 is

   protected body PO is
      procedure PP1 is
      begin
         null;
      end;
   end;

   procedure P8 is
      --  Private procedure without a contract. Likely to be inlined.
   begin
      PO.PP1;
   end;

   procedure P7
   with Pre => True;
   --  Private procedure with a contract. Not inlined.

   procedure P7 is
   begin
      P8;
   end;

   procedure P6;
   --  Private procedure without a contract. Likely to be inlined.

   procedure P6 is
   begin
      P7;
   end;

   procedure P5 is
      --  Body of a public procedure.
   begin
      P6;
   end;

   procedure P4 is
      --  Body of a public procedure.
   begin
      P5;
   end;

   procedure PA is
      --  Body of a public procedure.
   begin
      P6; --  Inlined call to P7
      P7; --  Direct call to P7
   end;

end U2;
