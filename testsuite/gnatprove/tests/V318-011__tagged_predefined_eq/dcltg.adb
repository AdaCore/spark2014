procedure Dcltg with SPARK_Mode is
   function Never return Boolean is (False);
   package StopDispatchWarning is
      type Parent is tagged null record;
      type Child is new Parent with record
         V : Natural;
      end record;
   end StopDispatchWarning;
   use StopDispatchWarning;
   function FakeUse(Y : Child) return Boolean
   is (Never or else FakeUse(Y));
   function TestExpanded(X : Parent'Class) return Boolean
   is (FakeUse(Child(X)))
   with Pre => X in Child;
   function Test(X : Parent'Class) return Boolean
   is (declare Y : constant Child := Child(X); begin FakeUse(Y))
   with Pre => X in Child;
begin
   null;
end;
