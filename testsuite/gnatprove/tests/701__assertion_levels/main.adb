pragma Assertion_Level (Silver);
pragma Assertion_Level (Gold, Depends => Silver);

procedure Main  with spark_mode is

   --  Preconditions

   procedure Test_Precondition is

      procedure P1 (X : Integer) with
        Pre => (Silver => X >= 0, Gold => X <= 100),
        Post => X in 0 .. 100, -- @POSTCONDITION:PASS
        Global => null;

      procedure P1 (X : Integer) is null;

      procedure P2 (X : Integer) with
        Pre => X >= 0,
        Global => null;

      procedure P2 (X : Integer) is
      begin
         P1 (X); -- @PRECONDITION:FAIL
      end P2;

      procedure P3 (X : Integer) with
        Pre => X <= 100,
        Global => null;

      procedure P3 (X : Integer) is
      begin
         P1 (X); -- @PRECONDITION:FAIL
      end P3;

   begin
      null;
   end Test_Precondition;

   --  Postconditions

   procedure Test_Postcondition is

      procedure P1 (X : Integer) with
        Pre  => X >= 0,
        Post => (Silver => X >= 0,
                 Gold   => X <= 100), -- @POSTCONDITION:FAIL
        Global => null;

      procedure P1 (X : Integer) is null;

      procedure P2 (X : Integer) with
        Pre  => X <= 100,
        Post => (Silver => X >= 0, -- @POSTCONDITION:FAIL
                 Gold   => X <= 100),
        Global => null;

      procedure P2 (X : Integer) is null;

      procedure P3 (X : in out Integer) with
        Post => (Silver => X >= 0, Gold => X <= 100),
        Global => null,
        Always_Terminates,
        Import;

      procedure P4 (X : in out Integer) with
        Post => X in 0 .. 100,  -- @POSTCONDITION:PASS
        Global => null;

      procedure P4 (X : in out Integer) is
      begin
         P3 (X);
      end P4;

   begin
      null;
   end Test_Postcondition;

   --  Contract_Cases

   procedure Test_Contract_Cases is

      procedure P1 (B : Boolean; X : Integer) with
        Pre  => X >= 0,
        Contract_Cases =>
          (Silver => (B => X >= 0, others => True),
           Gold   => (B => X <= 100, others => True)), -- @CONTRACT_CASE:FAIL
        Global => null;

      procedure P1 (B : Boolean; X : Integer) is null;

      procedure P2 (B : Boolean; X : Integer) with
        Pre  => X <= 100,
        Contract_Cases =>
          (Silver => (B => X >= 0, others => True), -- @CONTRACT_CASE:FAIL
           Gold   => (B => X <= 100, others => True)),
        Global => null;

      procedure P2 (B : Boolean; X : Integer) is null;

      procedure P3 (B : Boolean; X : in out Integer) with
        Contract_Cases =>
          (Silver => (B => X >= 0, others => True),
           Gold   => (B => X <= 100, others => True)),
        Global => null,
        Always_Terminates,
        Import;

      procedure P4 (X : in out Integer) with
        Post => X in 0 .. 100,  -- @POSTCONDITION:PASS
        Global => null;

      procedure P4 (X : in out Integer) is
      begin
         P3 (True, X);
      end P4;

   begin
      null;
   end Test_Contract_Cases;

   --  Predicate

   procedure Test_Predicate is

      subtype T is Integer with
        Dynamic_Predicate =>
          (Silver => T >= 0,
           Gold   => T <= 100);

      procedure P1 (X : Integer; Y : out T) with
        Pre => X >= 0;

      procedure P1 (X : Integer; Y : out T) is
      begin
         Y := X; -- @PREDICATE_CHECK:FAIL
      end P1;

      procedure P2 (X : Integer; Y : out T) with
        Pre => X <= 100;

      procedure P2 (X : Integer; Y : out T) is
      begin
         Y := X; -- @PREDICATE_CHECK:FAIL
      end P2;

      procedure P3 (X : T; Y : in out Integer) with
        Post => Y in 0 .. 100;  -- @POSTCONDITION:PASS

      procedure P3 (X : T; Y : in out Integer) is
      begin
         Y := X;
      end P3;

   begin
      null;
   end Test_Predicate;

   --  Invariant

   procedure Test_Invariant is

      package Nested is
         type T is private;

         procedure P1 (X : Integer; Y : out T) with
           Pre => X >= 0;

         procedure P2 (X : Integer; Y : out T) with
           Pre => X <= 100;

         procedure P3 (X : T; Y : in out Integer) with
           Post => Y in 0 .. 100;  -- @POSTCONDITION:PASS
      private

         type T is new Integer with
           Type_Invariant =>
             (Silver => T >= 0,
              Gold   => T <= 100),
           Default_Value => 0;
      end Nested;

      package body Nested is

         procedure P1 (X : Integer; Y : out T) is
         begin
            Y := T'Base (X); -- @INVARIANT_CHECK:FAIL
         end P1;

         procedure P2 (X : Integer; Y : out T) is
         begin
            Y := T'Base (X); -- @INVARIANT_CHECK:FAIL
         end P2;

         procedure P3 (X : T; Y : in out Integer) is
         begin
            Y := Integer (X);
         end P3;
      end Nested;

   begin
      null;
   end Test_Invariant;

   --  DIC

   procedure Test_DIC is

      package Nested_1 is
         type T is private with
           Default_Initial_Condition =>
             (Silver => F1 (T), --  @DEFAULT_INITIAL_CONDITION:FAIL
              Gold   => F2 (T));

         function F1 (X : T) return Boolean;
         function F2 (X : T) return Boolean;
      private

         type T is new Integer with
           Default_Value => -1;

         function F1 (X : T) return Boolean is (X >= 0);
         function F2 (X : T) return Boolean is (X <= 100);
      end Nested_1;

      package Nested_2 is
         type T is private with
           Default_Initial_Condition =>
             (Silver => F1 (T),
              Gold   => F2 (T)); --  @DEFAULT_INITIAL_CONDITION:FAIL

         function F1 (X : T) return Boolean;
         function F2 (X : T) return Boolean;
      private

         type T is new Integer with
           Default_Value => 200;

         function F1 (X : T) return Boolean is (X >= 0);
         function F2 (X : T) return Boolean is (X <= 100);
      end Nested_2;

      package Nested_3 is
         type T is private with
           Default_Initial_Condition =>
             (Silver => F1 (T),
              Gold   => F2 (T));

         function F1 (X : T) return Boolean;
         function F2 (X : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type T is new Integer;

         function F1 (X : T) return Boolean is (X >= 0);
         function F2 (X : T) return Boolean is (X <= 100);
      end Nested_3;
      use Nested_3;

      procedure P (X : out T) with
        Post => F1 (X) and F2 (X); --  @POSTCONDITION:PASS

      procedure P (X : out T) is
         Y : T;
      begin
         X := Y;
      end P;

   begin
      null;
   end Test_DIC;

   --  Initial_Condition

   procedure Test_Initial_Condition is

      package Nested_1 with Initial_Condition =>
        (Silver => X >= 0, --  @INITIAL_CONDITION:FAIL
         Gold   => X <= 100)
      is

         X : Integer := -10;
      end Nested_1;

      package Nested_2 with Initial_Condition =>
        (Silver => X >= 0,
         Gold   => X <= 100) --  @INITIAL_CONDITION:FAIL
      is

         X : Integer := 200;
      end Nested_2;

      package Nested_3 with Initial_Condition =>
        (Silver => X >= 0,
         Gold   => X <= 100)
      is
         X : Integer;
         procedure P;
      end Nested_3;

      package body Nested_3 is
         procedure P is null;
      begin
         X := 50;
      end Nested_3;
      use Nested_3;

      Y : constant Integer := X;
      pragma Assert (Y in 0 .. 100); --  @ASSERT:PASS
   begin
      null;
   end Test_Initial_Condition;

   --  Subprogram_Variant

   procedure Subprogram_Variant is

      procedure Do_Smthg (X, Y : Natural) with
        Subprogram_Variant =>
          (Silver => (Decreases => X));

      procedure Do_Smthg (X, Y : Natural) is
      begin
         if X > 0 and Y > 0 then
            Do_Smthg (X, Y - 1); --@SUBPROGRAM_VARIANT:FAIL
         end if;
      end Do_Smthg;


   begin
      null;
   end Subprogram_Variant;

begin
   null;
end Main;
