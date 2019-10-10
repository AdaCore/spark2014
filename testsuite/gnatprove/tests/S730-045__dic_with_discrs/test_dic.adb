procedure Test_DIC with SPARK_Mode is
   package Nested is
      type P1 (X : Boolean) is private with --@DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => X;
      type P2 (X : Boolean) is private with --@DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P2.X;
      type P3 (X : Boolean) is private with --@DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => S3'(P3).X;
      function F3 (X : P3) return Boolean;
      subtype S3 is P3 with
        Predicate => F3 (P3'(S3));
      type P4 (X : Boolean) is private with --@DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => S4 (P4).X;
      function F4 (X : P4) return Boolean;
      subtype S4 is P4 with
        Predicate => F4 (P4'(S4));
      type P5 (X : Boolean) is private with --@DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => Id (P5).X;
      function Id (X : P5) return P5;
   private
      type P1 (X : Boolean) is record
         C : Integer := 0;
      end record;
      type P2 (X : Boolean) is record
         C : Integer := 0;
      end record;
      type P3 (X : Boolean) is record
         C : Integer := 0;
      end record;
      type P4 (X : Boolean) is record
         C : Integer := 0;
      end record;
      type P5 (X : Boolean) is record
         C : Integer := 0;
      end record;
      function Id (X : P5) return P5 is
        (if X.X and then X.C = 0 then (True, X.C) else (False, X.C));
      function F3 (X : P3) return Boolean is (X.C = 0);
      function F4 (X : P4) return Boolean is (X.C = 0);
   end Nested;
   use Nested;

   X1 : P1 (True); --@DEFAULT_INITIAL_CONDITION:PASS
   X2 : P2 (True); --@DEFAULT_INITIAL_CONDITION:PASS
   X3 : P3 (True); --@DEFAULT_INITIAL_CONDITION:NONE
   X4 : P4 (True); --@DEFAULT_INITIAL_CONDITION:NONE
   X5 : P5 (True); --@DEFAULT_INITIAL_CONDITION:NONE
begin
   null;
end Test_DIC;
