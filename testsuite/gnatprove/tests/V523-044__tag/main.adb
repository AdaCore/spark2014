--  Test that compatibility between tags is handled correctly.

procedure Main with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
      end record;

      type Child1 is new Root with record
         G1 : Integer;
      end record;

      type Child2 is new Root with record
         G2 : Integer;
      end record;

      type Grand_Child1 is new Child1 with record
         H1 : Integer;
      end record;

   end Nested;
   use Nested;

   --  Check the general rules:
   --    * Compatibility is transitive,
   --    * Incompatible tags lead to disjoint derivation trees.

   procedure Test_Transitive (R : Root'Class) with
     Ghost,
     Global => null,
     Pre  => R in Grand_Child1'Class,
     Post => R in Child1'Class;

   procedure Test_Transitive (R : Root'Class) is null;

   procedure Test_Transitive_Bad (R : Root'Class) with
     Ghost,
     Global => null,
     Pre  => R in Child1'Class,
     Post => R in Grand_Child1'Class; -- @POSTCONDITION:FAIL

   procedure Test_Transitive_Bad (R : Root'Class) is null;

   procedure Test_Separate_Trees (R : Root'Class) with
     Ghost,
     Global => null,
     Pre  => R in Grand_Child1'Class,
     Post => R not in Child2'Class;

   procedure Test_Separate_Trees (R : Root'Class) is null;

   procedure Test_Separate_Trees_Bad (R : Root'Class) with
     Ghost,
     Global => null,
     Pre  => R in Child1'Class,
     Post => R not in Grand_Child1'Class; -- @POSTCONDITION:FAIL

   procedure Test_Separate_Trees_Bad (R : Root'Class) is null;

   --  Check that the tags are handled precisely when they are known exactly

   procedure Test_Root_OK with
     Global => null
   is
      R  : Root := (F => 1);
      RR : Root'Class := R;
   begin
      pragma Assert (RR in Root);
      pragma Assert (RR in Root'Class);
      pragma Assert (RR not in Child1);
      pragma Assert (RR not in Child1'Class);
      pragma Assert (RR not in Child2);
      pragma Assert (RR not in Child2'Class);
      pragma Assert (RR not in Grand_Child1);
      pragma Assert (RR not in Grand_Child1'Class);
   end;

   procedure Test_Root_Bad (X : Integer) with
     Global => null
   is
      R  : Root := (F => 1);
      RR : Root'Class := R;
   begin
      case X is
         when 1 =>
            pragma Assert (RR not in Root); -- @ASSERT:FAIL
         when 2 =>
            pragma Assert (RR not in Root'Class); -- @ASSERT:FAIL
         when 3 =>
            pragma Assert (RR in Child1); -- @ASSERT:FAIL
         when 4 =>
            pragma Assert (RR in Child1'Class); -- @ASSERT:FAIL
         when 5 =>
            pragma Assert (RR in Child2); -- @ASSERT:FAIL
         when 6 =>
            pragma Assert (RR in Child2'Class); -- @ASSERT:FAIL
         when 7 =>
            pragma Assert (RR in Grand_Child1); -- @ASSERT:FAIL
         when others =>
            pragma Assert (RR in Grand_Child1'Class); -- @ASSERT:FAIL
      end case;
   end;

   procedure Test_Child_OK with
     Global => null
   is
      C  : Child1 := (1, 2);
      RC : Root'Class := C;
   begin
      pragma Assert (RC not in Root);
      pragma Assert (RC in Root'Class);
      pragma Assert (RC in Child1);
      pragma Assert (RC in Child1'Class);
      pragma Assert (RC not in Child2);
      pragma Assert (RC not in Child2'Class);
      pragma Assert (RC not in Grand_Child1);
      pragma Assert (RC not in Grand_Child1'Class);
   end;

   procedure Test_Child_Bad (X : Integer) with
     Global => null
   is
      C  : Child1 := (1, 2);
      RC : Root'Class := C;
   begin
      case X is
         when 1 =>
            pragma Assert (RC in Root); -- @ASSERT:FAIL
         when 2 =>
            pragma Assert (RC not in Root'Class); -- @ASSERT:FAIL
         when 3 =>
            pragma Assert (RC not in Child1); -- @ASSERT:FAIL
         when 4 =>
            pragma Assert (RC not in Child1'Class); -- @ASSERT:FAIL
         when 5 =>
            pragma Assert (RC in Child2); -- @ASSERT:FAIL
         when 6 =>
            pragma Assert (RC in Child2'Class); -- @ASSERT:FAIL
         when 7 =>
            pragma Assert (RC in Grand_Child1); -- @ASSERT:FAIL
         when others =>
            pragma Assert (RC in Grand_Child1'Class); -- @ASSERT:FAIL
      end case;
   end;

   procedure Test_Grand_Child_OK with
     Global => null
   is
      G  : Grand_Child1 := (1, 2, 3);
      RG : Root'Class := G;
   begin
      pragma Assert (RG not in Root);
      pragma Assert (RG in Root'Class);
      pragma Assert (RG not in Child1);
      pragma Assert (RG in Child1'Class);
      pragma Assert (RG not in Child2);
      pragma Assert (RG not in Child2'Class);
      pragma Assert (RG in Grand_Child1);
      pragma Assert (RG in Grand_Child1'Class);
   end;

   procedure Test_Grand_Child_Bad (X : Integer) with
     Global => null
   is
      G  : Grand_Child1 := (1, 2, 3);
      RG : Root'Class := G;
   begin
      case X is
         when 1 =>
            pragma Assert (RG in Root); -- @ASSERT:FAIL
         when 2 =>
            pragma Assert (RG not in Root'Class); -- @ASSERT:FAIL
         when 3 =>
            pragma Assert (RG in Child1); -- @ASSERT:FAIL
         when 4 =>
            pragma Assert (RG not in Child1'Class); -- @ASSERT:FAIL
         when 5 =>
            pragma Assert (RG in Child2); -- @ASSERT:FAIL
         when 6 =>
            pragma Assert (RG in Child2'Class); -- @ASSERT:FAIL
         when 7 =>
            pragma Assert (RG not in Grand_Child1); -- @ASSERT:FAIL
         when others =>
            pragma Assert (RG not in Grand_Child1'Class); -- @ASSERT:FAIL
      end case;
   end;

begin
   null;
end Main;
