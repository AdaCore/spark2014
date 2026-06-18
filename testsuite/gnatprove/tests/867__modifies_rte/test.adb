procedure Test with SPARK_Mode is
   A : array (Positive range 1 .. 10) of Integer;

   function P return Boolean with Import, Global => null;
   function F return Integer with Import, Global => null,
     Pre => P, Post => F'Result in 1 .. 10;

   --  RTE in guard

   procedure Reset_RTE_Guard with
     Import,
     Global => (In_Out => A),
     Modifies => (A when F in A'Range); --  @PRECONDITION:FAIL

   --  RTE in index

   procedure Reset_RTE_Index with
     Import,
     Global => (In_Out => A),
     Modifies => A (F); --  @PRECONDITION:FAIL

   procedure Reset_RTE_OK with
     Import,
     Global => (In_Out => A),
     Modifies => (A (F) when  --  @PRECONDITION:PASS
                    P and then F in A'Range); --  @PRECONDITION:PASS

   --  Component checks on entry

   procedure Reset_Array (I : Positive) with
     Import,
     Global => (In_Out => A),
     Modifies => A (I); --  @INDEX_CHECK:FAIL

   procedure Reset_Array_2 (I : Positive) with
     Import,
     Global => (In_Out => A),
     Modifies => (A (I) when I in 1 .. 10, --  @INDEX_CHECK:PASS
                  A (2));  --  @INDEX_CHECK:NONE

   procedure Reset_Array_3 (I, J : Positive) with
     Import,
     Global => (In_Out => A),
     Pre => I in 1 .. 10,
     Modifies => (A (I), --  @INDEX_CHECK:PASS
                  A (J) when J in A'Range); --  @INDEX_CHECK:PASS

   type R (D : Boolean := False) is record
      case D is
         when True =>
            F : Integer;
         when False =>
            null;
      end case;
   end record;

   procedure Reset_Record (B : in out R) with
     Import,
     Modifies => B.F; --  @DISCRIMINANT_CHECK:FAIL

   procedure Reset_Record_2 (B : in out R) with
     Import,
     Modifies => (B.F when B.D); --  @DISCRIMINANT_CHECK:PASS

   procedure Reset_Record_3 (B : in out R) with
     Import,
     Pre => B.D,
     Modifies => B.F; --  @DISCRIMINANT_CHECK:PASS

   type Int_Acc is access Integer;

   procedure Reset_Access (B : in out Int_Acc) with
     Import,
     Modifies => B.all; --  @DEREFERENCE_CHECK:FAIL

   procedure Reset_Access_2 (B : in out Int_Acc) with
     Import,
     Modifies => (B.all when B /= null); --  @DEREFERENCE_CHECK:PASS

   procedure Reset_Access_3 (B : in out Int_Acc) with
     Import,
     Pre => B /= null,
     Modifies => B.all; --  @DEREFERENCE_CHECK:PASS

   procedure Reset_Access_4 (B : in out not null Int_Acc) with
     Import,
     Modifies => B.all; --  @DEREFERENCE_CHECK:NONE

   --  Component checks on normal return

   procedure Reset_Return_Record (B : in out R) with
     Modifies => (B.F when B.D) --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      if B.D then
         B.F := 13;
      end if;
   end Reset_Return_Record;

   procedure Reset_Return_Record_2 (B : in out R) with
     Pre => B.D,
     Modifies => B.F --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      B.F := 13;
   end Reset_Return_Record_2;

   procedure Reset_Return_Record_3 (B : in out R) with
     Pre => B.D and not B'Constrained,
     Modifies => B.F --  @DISCRIMINANT_CHECK:FAIL
   is
   begin
      B := (D => False);
   end Reset_Return_Record_3;

   --  Component checks on exception propagation

   procedure Reset_Exception_Record (B : aliased in out R) with
     Exceptional_Cases => (Program_Error => True),
     No_Return,
     Modifies => (B.F when B.D) --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      if B.D then
         B.F := 13;
      end if;
      raise Program_Error;
   end Reset_Exception_Record;

   procedure Reset_Exception_Record_2 (B : aliased in out R) with
     Exceptional_Cases => (Program_Error => True),
     No_Return,
     Pre => B.D,
     Modifies => B.F --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      B.F := 13;
      raise Program_Error;
   end Reset_Exception_Record_2;

   procedure Reset_Exception_Record_3 (B : aliased in out R) with
     Exceptional_Cases => (Program_Error => True),
     No_Return,
     Pre => B.D and not B'Constrained,
     Modifies => B.F --  @DISCRIMINANT_CHECK:FAIL
   is
   begin
      B := (D => False);
      raise Program_Error;
   end Reset_Exception_Record_3;

   procedure Reset_Exception_Record_4 (B : in out R) with
     Exceptional_Cases => (Program_Error => True),
     No_Return,
     Pre => B.D and not B'Constrained,
     Modifies => B.F --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      B := (D => False);
      raise Program_Error;
   end Reset_Exception_Record_4;

   --  Component checks on program exit

   B : R;

   procedure Do_Exit with Program_Exit, Global => null, No_Return, Import;

   procedure Reset_Exit_Record with
     Global => (In_Out => B),
     Program_Exit => (if B.D then B.F = 13),
     No_Return,
     Modifies => (B.F when B.D) --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      if B.D then
         B.F := 13;
      end if;
      Do_Exit;
   end Reset_Exit_Record;

   procedure Reset_Exit_Record_2 with
     Global => (In_Out => B),
     Program_Exit => B.F = 13,
     No_Return,
     Pre => B.D,
     Modifies => B.F --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      B.F := 13;
      Do_Exit;
   end Reset_Exit_Record_2;

   procedure Reset_Exit_Record_3 with
     Global => (In_Out => B),
     Program_Exit => not B.D,
     No_Return,
     Pre => B.D and not B'Constrained,
     Modifies => B.F --  @DISCRIMINANT_CHECK:FAIL
   is
   begin
      B := (D => False);
      Do_Exit;
   end Reset_Exit_Record_3;

   procedure Reset_Exit_Record_4 with
     Global => (In_Out => B),
     Program_Exit,
     No_Return,
     Pre => B.D and not B'Constrained,
     Modifies => B.F --  @DISCRIMINANT_CHECK:PASS
   is
   begin
      B := (D => False);
      Do_Exit;
   end Reset_Exit_Record_4;
begin
   null;
end;
