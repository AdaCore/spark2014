procedure Counterex is
   type Rec is record
      A, B : Integer;
   end record;
   type Arr is array (1 .. 10) of Rec;

   procedure Check (Tab : Arr) with Pre => True is
   begin
      pragma Assert (Tab(1).A = Tab(2).B); -- @COUNTEREXAMPLE
   end;
begin
   null;
end Counterex;
