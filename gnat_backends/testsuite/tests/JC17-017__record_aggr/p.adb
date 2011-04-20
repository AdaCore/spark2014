package body P is
   type T is record
      Y, Z, T, U, V : Integer;
   end record;

   procedure Proc is
      X : T;
   begin
      X := (others => 0);
   end;

   procedure Proc2 is
      X : T;
   begin
      X := T'(others => 0);
   end;

   procedure Proc3 is
      X : T;
   begin
      X := T'(1, 2, 3, 4, 5);
   end;

   procedure Proc4 is
      X : T;
   begin
      X := (1, 2, 3, 4, 5);
   end;

   procedure Proc5 is
      X : T;
   begin
      X := (1, 2, 3, others => 0);
   end;

   procedure Proc6 is
      X : T;
   begin
      X := (Z => 2, V => 5, others => 0);
   end;

   procedure Proc7 is
      function Zero return Integer is (0);
      X : T;
   begin
      X := (1, 2, 3, others => Zero);
   end;

   procedure Proc8 is
      function Zero return Integer is (0);
      X : T;
   begin
      X := (others => Zero);
   end;

end;
