procedure Flow_Logical_Eq with SPARK_Mode is
   G : Boolean;
   function My_Eq (X, Y : Integer) return Boolean with
     Annotate => (GNATprove, Logical_Equal);
   function My_Eq (X, Y : Integer) return Boolean is (G and then X = Y)
     with SPARK_Mode => Off;
begin
   null;
end;
