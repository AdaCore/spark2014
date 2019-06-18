procedure Borrow_With_Variables with SPARK_Mode is
   type Tree;
   type Tree_Access is access Tree;
   type Tree_Access_Array is array (Positive range 1 .. 3) of Tree_Access;
   type Tree is record
      Value : Integer;
      Nexts : Tree_Access_Array;
   end record;

   X11 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
   X12 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
   X13 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
   X1 : Tree_Access := new Tree'(Value => 1, Nexts => (X11, X12, X13));
   X2 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
   X3 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
   X  : Tree_Access := new Tree'(Value => 1, Nexts => (X1, X2, X3));
begin
   declare
      I : Integer := 1;
      Y : access Tree := X.Nexts (1);
   begin
      Y := Y.Nexts (I);
      Y.Value := 2;
      I := 2;
   end;
   pragma Assert (X.Nexts (1).Nexts (2).Value = 1); --@ASSERT:PASS
   declare
      I : Integer := 1;
      Y : access Tree := X.Nexts (I);
   begin
      Y.Value := 2;
      I := 2;
   end;
   pragma Assert (X.Nexts (2).Value = 2);--@ASSERT:FAIL
end Borrow_With_Variables;
