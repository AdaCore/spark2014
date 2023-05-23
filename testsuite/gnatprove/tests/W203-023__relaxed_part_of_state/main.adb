procedure Main
  with
    SPARK_Mode => On
is

   package N1 with Abstract_State => S is
      function F return Integer;
      function G return Integer;
      function H return Integer;
   private
      X : Integer with Relaxed_Initialization, Part_Of => S; -- ok
      function F return Integer is (X);  --@INIT_BY_PROOF:FAIL
      function G return Integer is (if X'Initialized then X else 0);
   end N1;

   package body N1 with SPARK_Mode => Off is
      function H return Integer is (X);
   end N1;

   package N2 with Abstract_State => S, Initializes => S is
      function F return Integer;
      function G return Integer;
      function H return Integer;
   private
      X : Integer with Relaxed_Initialization, Part_Of => S; -- ok
      function F return Integer is (X);  --@INIT_BY_PROOF:FAIL
      function G return Integer is (if X'Initialized then X else 0);
   end N2;

   package body N2 with SPARK_Mode => Off is
      function H return Integer is (X);
   end N2;

   package N3 with Abstract_State => S, Initializes => S is
      function H return Integer;
   private
      X : Integer with Relaxed_Initialization, Part_Of => S; -- ok
      Y : Integer with Part_Of => S; -- failed initialization check in flow expected
   end N3;

   package body N3 with SPARK_Mode => Off is
      function H return Integer is (X);
   end N3;

   X1 : constant Integer := N1.H; -- failed initialization check in flow expected
   X2 : constant Integer := N2.H; -- ok
   X3 : constant Integer := N3.H; -- ok

begin
   null;
end Main;
