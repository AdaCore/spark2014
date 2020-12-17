procedure R with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   type Int_Ptr_Arr is array (Boolean) of Int_Ptr;
   type Outer_Rec is record
       X_Ptr : Int_Ptr_Arr;
   end record;

   O : Outer_Rec;

   procedure Proc (X, Y : in out Integer)
   is
   begin
       X := Y + 1;
       Y := X + 1;
   end Proc;

   V : Boolean := False;

begin
   O.X_Ptr(False) := new Integer'(1);
   O.X_Ptr(True) := new Integer'(1);
   Proc (O.X_Ptr(False).all, O.X_Ptr(V).all);  --  illegal
end R;
