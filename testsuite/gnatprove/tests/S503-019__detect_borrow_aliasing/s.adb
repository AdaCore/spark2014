procedure S with
  SPARK_Mode
is
   type Rec is record
       X : Integer;
       Y : Integer;
   end record;
   type Rec_Ptr is access Rec;

   Ptr : Rec_Ptr;

   procedure Proc (X, Y : in out Integer)
   is
   begin
       X := Y + 1;
       Y := X + 1;
   end Proc;

begin
   Ptr := new Rec'(X => 1, Y => 2);
   Proc (Ptr.all.X, Ptr.all.Y); -- legal
end S;
