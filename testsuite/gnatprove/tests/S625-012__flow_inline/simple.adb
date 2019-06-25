procedure Simple with SPARK_Mode is
   procedure Proc (X : in out Integer)
   is
   begin
       X := X + 1;
   end Proc;
   type Arr is array (Boolean) of Integer;
   X : Arr := (0, 1);
begin
   Proc (X((for all K in Boolean => K)));
end Simple;
