procedure Test_Get_Variables with SPARK_Mode is
   package Nested is
      type Root is tagged record
         C1 : Integer;
      end record;
      function Read_D (R : Root) return Integer is (R.C1);

      type Child is new Root with record
         C2 : Integer;
      end record;
      function Read_D (R : Child) return Integer is (R.C2);
   end Nested;
   use Nested;

   --  Test that view conversions are correctly handled in function calls

   function Read1 (R : Root) return Integer;
   function Read1 (R : Root) return Integer is (R.C1);
   function Read2 (R : Root'Class) return Integer;
   function Read2 (R : Root'Class) return Integer is
   begin
      if R in Child'Class then
         return Child (R).C2;
      else
         return R.C1;
      end if;
   end Read2;
   function Read3 (R : Root) return Integer with Extensions_Visible;
   function Read3 (R : Root) return Integer is
   begin
      return Read2 (Root'Class (R));
   end Read3;

   procedure Test1 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test1 (A, B : Integer; C : out Integer) is
      R : Root'Class := Child'(C1 => A, C2 => B);
   begin
      C := Read1 (Root (R));
   end Test1;

   procedure Test2 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));
   procedure Test2 (A, B : Integer; C : out Integer) is
      R : Root'Class := Child'(C1 => A, C2 => B);
   begin
      C := Read2 (Root (R));
   end Test2;

   procedure Test3 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));
   procedure Test3 (A, B : Integer; C : out Integer) is
      R : Root'Class := Child'(C1 => A, C2 => B);
   begin
      C := Read3 (Root (R));
   end Test3;

   procedure Test4 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));
   procedure Test4 (A, B : Integer; C : out Integer) is
      R : Root'Class := Child'(C1 => A, C2 => B);
   begin
      C := Read_D (Root'Class (R));
   end Test4;

   procedure Test5 (A, B : Integer; C : out Integer; R : out Root) with
     Extensions_Visible,
     Pre => Root'Class (R) in Child,
     Depends => (R => (A, B), C => A);

   procedure Test5 (A, B : Integer; C : out Integer; R : out Root) is
   begin
      Root'Class (R) := Root'Class (Child'(C1 => A, C2 => B));
      C := Read1 (Root (R));
   end Test5;

   procedure Test6 (A, B : Integer; C : out Integer; R : out Root) with
     Extensions_Visible,
     Pre => Root'Class (R) in Child,
     Depends => (R => (A, B), C => (A, B));

   procedure Test6 (A, B : Integer; C : out Integer; R : out Root) is
   begin
      Root'Class (R) := Root'Class (Child'(C1 => A, C2 => B));
      C := Read2 (Root (R));
   end Test6;

   procedure Test7 (A, B : Integer; C : out Integer; R : out Root) with
     Extensions_Visible,
     Pre => Root'Class (R) in Child,
     Depends => (R => (A, B), C => (A, B));

   procedure Test7 (A, B : Integer; C : out Integer; R : out Root) is
   begin
      Root'Class (R) := Root'Class (Child'(C1 => A, C2 => B));
      C := Read3 (Root (R));
   end Test7;

   procedure Test8 (A, B : Integer; C : out Integer; R : out Root) with
     Extensions_Visible,
     Pre => Root'Class (R) in Child,
     Depends => (R => (A, B), C => (A, B));

   procedure Test8 (A, B : Integer; C : out Integer; R : out Root) is
   begin
      Root'Class (R) := Root'Class (Child'(C1 => A, C2 => B));
      C := Read_D (Root'Class (R));
   end Test8;

begin
   null;
end;
