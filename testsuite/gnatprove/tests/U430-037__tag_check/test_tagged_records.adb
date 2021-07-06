procedure Test_Tagged_Records with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
   end record;
   type GrandChild is new Child with record
      H : Integer;
   end record;
   type Child2 is new Root with record
      H : Integer;
   end record;
   type Root_Acc is access Root'Class;

   function Rand (X : Integer) return Boolean with Import;

   C : Root'Class := Root'Class (GrandChild'(1, 2, 3));
   P : Root_Acc := new Root'Class'(C);
begin
   if Rand (0) then
      Child2 (C) := (1, 2); --@TAG_CHECK:FAIL
   elsif Rand (1) then
      Child2 (P.all) := (1, 2); --@TAG_CHECK:FAIL
   elsif Rand (3) then
      Child2 (C).F := 1; --@TAG_CHECK:FAIL
   elsif Rand (4) then
      Child (C).F := 1; -- OK
   elsif Rand (5) then
      Child'Class (C).F := 1; -- OK
   elsif Rand (6) then
      GrandChild'Class (C).F := 1; -- OK
   end if;
end Test_Tagged_Records;
