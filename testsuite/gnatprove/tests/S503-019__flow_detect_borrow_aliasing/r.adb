procedure R with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   type Outer_Rec is record
       X_Ptr : Int_Ptr;
   end record;

   O : Outer_Rec;

   procedure Proc (X, Y : in out Integer)
   is
   begin
       X := Y + 1;
       Y := X + 1;
   end Proc;

begin
   O.X_Ptr := new Integer'(1);
   Proc (O.X_Ptr.all, O.X_Ptr.all);  --  illegal
end R;
