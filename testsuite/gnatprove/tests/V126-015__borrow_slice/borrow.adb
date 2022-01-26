procedure Borrow is

   type Ptr is access Integer;
   type Rec is record
     C : Ptr;
   end record;
   type Arr is array (1 .. 10) of Rec;
   type Acc is access Arr;

   function F (Arg : access Arr) return access Integer is
      (Arg(1..5)(4).C);

   X : Acc := new Arr'(others => (C => new Integer'(0)));
begin
   declare
      Y : access Integer := F(X);
   begin
      Y.all := 42;
   end;

   pragma Assert (X(1..5)(4).C.all = 42);

end Borrow;
