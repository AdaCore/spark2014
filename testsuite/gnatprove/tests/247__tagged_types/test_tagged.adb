with SPARK.Containers.Types; use SPARK.Containers.Types;
with SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists;
with SPARK.Containers.Formal.Unbounded_Ordered_Maps;

procedure Test_Tagged with SPARK_Mode is

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;

      type Child is new Root with record
         G : Integer;
      end record;
   end Nested;
   use Nested;

   procedure Test_Lists with Global => null is
      package My_Lists is new SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists (Root);
      use My_Lists;
      R : Root := (F => 3);
      C : Child := (F => 3, G => 4);
      X : My_Lists.List;
      procedure Create (R : Root; C : in out Root) with
        Post => First_Element (X) = R
        and then Element (X, Next (X, First (X))) = C;
      procedure Create (R : Root; C : in out Root) is
      begin
         X := [R, C];
      end Create;
      procedure Create_Bad (R : Root; C : in out Root) with
        Extensions_Visible => True,
        Post => First_Element (X) = R
        and then Root'Class (Element (X, Next (X, First (X)))) = Root'Class (C); --  POSTCONDITION:FAIL
      procedure Create_Bad (R : Root; C : in out Root) is
      begin
         X := [R, C];
      end Create_Bad;
   begin
      Create (R, Root (C));
      Create_Bad (R, Root (C));
   end Test_Lists;

   procedure Test_Lists_Classwide with Global => null is
      package My_Lists is new SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists (Root'Class);
      use My_Lists;
      R : Root := (F => 3);
      C : Child := (F => 3, G => 4);
      X : My_Lists.List := [R, Root'Class (C)];
   begin
      pragma Assert (Length (X) = 2);
      pragma Assert (First_Element (X) = Root'Class (R));
      pragma Assert (Element (X, Next (X, First (X))) = Root'Class (C));
      pragma Assert (False); --@ASSERT:FAIL
   end Test_Lists_Classwide;

   procedure Test_Maps with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps (Integer, Root);
      use My_Maps;
      R : Root := (F => 3);
      C : Child := (F => 3, G => 4);
      X : My_Maps.Map;
      procedure Create (R : Root; C : in out Root) with
        Post => First_Element (X) = R
        and then Element (X, Next (X, First (X))) = C;
      procedure Create (R : Root; C : in out Root) is
      begin
         X := [1 => R, 2 => C];
      end Create;
      procedure Create_Bad (R : Root; C : in out Root) with
        Extensions_Visible => True,
        Post => First_Element (X) = R
        and then Root'Class (Element (X, Next (X, First (X)))) = Root'Class (C); --  POSTCONDITION:FAIL
      procedure Create_Bad (R : Root; C : in out Root) is
      begin
         X := [1 => R, 2 => C];
      end Create_Bad;
   begin
      Create (R, Root (C));
      Create_Bad (R, Root (C));
   end Test_Maps;

   procedure Test_Maps_Classwide with Global => null is
      package My_Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps (Integer, Root'Class);
      use My_Maps;
      R : Root := (F => 3);
      C : Child := (F => 3, G => 4);
      X : My_Maps.Map := [1 => R, 2 => Root'Class (C)];
   begin
      pragma Assert (Length (X) = 2);
      pragma Assert (First_Element (X) = Root'Class (R));
      pragma Assert (Element (X, Next (X, First (X))) = Root'Class (C));
      pragma Assert (False); --@ASSERT:FAIL
   end Test_Maps_Classwide;

begin
   null;
end Test_Tagged;
