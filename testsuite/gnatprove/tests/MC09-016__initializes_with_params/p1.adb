package body P1
  with SPARK_Mode => On
is

   procedure A (X : in     Integer;
                Y :    out Integer) is
      -- Case 1 - initializes depends on "in" parameter
      -- Should be legal
      package N
        with Initializes => (S => X) -- legal, but rejected by FE 7.2.1
      is
         S : Integer := X;
      end N;
   begin
      Y := X + N.S;
   end A;

   procedure B (X : in out Integer;
                Y :    out Integer) is

      -- Case 2 - initializes depends on "in out" parameter
      -- Should be legal
      package N
        with Initializes => (S => X) -- legal, but rejected by FE 7.2.1
      is
         S : Integer := X;
      end N;
   begin
      Y := X + N.S;
      X := X + 1;
   end B;

   procedure C (X : out Integer;
                Y : out Integer) is
   begin
      X := 1;
      declare
         -- Case 3 - initializes depends on "out" parameter
         -- which has been initialized. Should be legal
         package N
           with Initializes => (S => X) -- legal, but rejected by FE 7.2.1
         is
            S : Integer := X;
         end N;
      begin
         Y := N.S;
      end ;
   end C;

   procedure D (X : out Integer;
                Y : out Integer) is
   begin
      declare
         -- Case 4 - initializes depends on "out" parameter
         -- which has NOT been initialized. Should be legal,
         -- but flow analysis will report data-flow error
         package N
           with Initializes => (S => X) -- legal, but rejected by FE 7.2.1
         is
            S : Integer := X; -- flow error here
         end N;
      begin
         Y := N.S;
      end ;
   end D;

end P1;
