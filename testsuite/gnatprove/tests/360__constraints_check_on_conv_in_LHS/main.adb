procedure Main with SPARK_Mode is

   function Id (X : Integer) return Integer is (X);

   procedure Test_Record with Global => null is
      type R (D : Integer) is tagged record
         F : Integer;
      end record;

      subtype S_R is R (Id (12));

      type C is new S_R with null record;

      V_R : R := R'(1, 2);

      procedure P_R_OK (V_R : out R) with
        Pre => V_R.D = 12;

      procedure P_R_OK (V_R : out R) is
      begin
         S_R (V_R) := (12, 4); --@DISCRIMINANT_CHECK:PASS
      end P_R_OK;

      procedure P_R_Bad_1 (V_R : out R) with
        Pre => V_R.D = 1;

      procedure P_R_Bad_1 (V_R : out R) is
      begin
         S_R (V_R) := (12, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_1;

      procedure P_R_Bad_2 (V_R : out R) with
        Pre => V_R.D = 1;

      procedure P_R_Bad_2 (V_R : out R) is
      begin
         S_R (V_R) := (1, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_2;

      procedure P_R_Bad_3 (V_R : out R) with
        Pre => V_R.D = 1;

      procedure P_R_Bad_3 (V_R : out R) is
      begin
         S_R (V_R).F := 4; --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_3;

   begin
      P_R_Bad_1 (V_R);
   end Test_Record;

   procedure Test_Array with Global => null is
      type A is array (Positive range <>) of Integer;

      subtype S_A is A (1 .. Id (12));

      V_A : A := A'(1 .. 2 => 0);

      procedure P_A_OK (V_A : out A) with
        Pre => V_A'First = 1 and V_A'Last = 12;

      procedure P_A_OK (V_A : out A)  is
         procedure Assign (X : out S_A) is
         begin
            X := (1 .. 12 => 0); --@LENGTH_CHECK:PASS
         end Assign;
      begin
         Assign (V_A);
      end P_A_OK;

      procedure P_A_Bad_1 (V_A : out A) with
        Pre => V_A'First = 1 and V_A'Last = 2;

      procedure P_A_Bad_1 (V_A : out A)  is
         procedure Assign (X : out S_A) is
         begin
            X := (1 .. 12 => 0); --@LENGTH_CHECK:FAIL
         end Assign;
      begin
         Assign (V_A);
      end P_A_Bad_1;

      procedure P_A_Bad_2 (V_A : out A) with
        Pre => V_A'First = 1 and V_A'Last = 2;

      procedure P_A_Bad_2 (V_A : out A)  is
         procedure Assign (X : out S_A) is
         begin
            X := (1 .. 2 => 0); --@LENGTH_CHECK:FAIL
         end Assign;
      begin
         Assign (V_A);
      end P_A_Bad_2;

      procedure P_A_Bad_3 (V_A : in out A) with
        Pre => V_A'First = 1 and V_A'Last = 2;

      procedure P_A_Bad_3 (V_A : in out A)  is
         procedure Assign (X : in out S_A) is
         begin
            X (1) := 0;
         end Assign;
      begin
         Assign (V_A); --@LENGTH_CHECK:FAIL
      end P_A_Bad_3;

   begin
      P_A_Bad_1 (V_A);
   end Test_Array;

   procedure Test_Access_Record with Global => null is
      type R (D : Integer) is record
         F : Integer;
      end record;

      type R_Access is access R;
      subtype S_R is R_Access (Id (12));

      V_R : R_Access := new R'(1, 2);

      procedure P_R_OK (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 12;

      procedure P_R_OK (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (12, 4); --@DISCRIMINANT_CHECK:PASS
      end P_R_OK;

      procedure P_R_Bad_1 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_1 (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (12, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_1;

      procedure P_R_Bad_2 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_2 (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (1, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_2;

      procedure P_R_Bad_3 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_3 (V_R : in out R_Access) is
      begin
         S_R (V_R).F := 4; --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_3;
   begin
      P_R_Bad_1 (V_R);
   end Test_Access_Record;

   procedure Test_Access_Mut_Disc with Global => null is
       type R (D : Integer := 1) is record
         F : Integer;
      end record;

      type R_Access is access R;
      subtype S_R is R_Access (Id (12));

      V_R : R_Access := new R'(1, 2);

      procedure P_R_OK (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 12;

      procedure P_R_OK (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (12, 4); --@DISCRIMINANT_CHECK:PASS
      end P_R_OK;

      procedure P_R_Bad_1 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_1 (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (12, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_1;

      procedure P_R_Bad_2 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_2 (V_R : in out R_Access) is
      begin
         S_R (V_R).all := (1, 4); --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_2;

      procedure P_R_Bad_3 (V_R : in out R_Access) with
        Pre => V_R /= null and then V_R.D = 1;

      procedure P_R_Bad_3 (V_R : in out R_Access) is
      begin
         S_R (V_R).F := 4; --@DISCRIMINANT_CHECK:FAIL
      end P_R_Bad_3;
   begin
      P_R_Bad_1 (V_R);
   end Test_Access_Mut_Disc;

   procedure Test_Access_Array with Global => null is

      type A is array (Positive range <>) of Integer;

      type A_Access is access A;
      subtype S_A is A_Access (1 .. Id (12));

      V_A : A_Access := new A'(1 .. 2 => 0);

      procedure P_A_OK (V_A : in out A_Access) with
        Pre => V_A /= null and then V_A'First = 1 and then V_A'Last = 12;

      procedure P_A_OK (V_A : in out A_Access) is
      begin
         S_A (V_A).all := (1 .. 12 => 0); --@LENGTH_CHECK:PASS
      end P_A_OK;

      procedure P_A_Bad_1 (V_A : in out A_Access) with
        Pre => V_A /= null and then V_A'First = 1 and then V_A'Last = 2;

      procedure P_A_Bad_1 (V_A : in out A_Access) is
      begin
         S_A (V_A).all := (others => 0); --@LENGTH_CHECK:FAIL
      end P_A_Bad_1;

      procedure P_A_Bad_2 (V_A : in out A_Access) with
        Pre => V_A /= null and then V_A'First = 1 and then V_A'Last = 2;

      procedure P_A_Bad_2 (V_A : in out A_Access) is
      begin
         S_A (V_A).all := (1 .. 2 => 0); --@LENGTH_CHECK:FAIL
      end P_A_Bad_2;

      procedure P_A_Bad_3 (V_A : in out A_Access) with
        Pre => V_A /= null and then V_A'First = 1 and then V_A'Last = 2;

      procedure P_A_Bad_3 (V_A : in out A_Access) is
      begin
         S_A (V_A) (1) := 0; --@RANGE_CHECK:FAIL
      end P_A_Bad_3;
   begin
      P_A_Bad_1 (V_A);
   end Test_Access_Array;
begin
   Test_Record;
end Main;
