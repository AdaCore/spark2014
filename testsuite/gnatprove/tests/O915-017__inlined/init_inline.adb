procedure Init_Inline (Y : out Integer)
  with SPARK_Mode
is
   type R is record
      C : Integer;
   end record;
   X : R;
   procedure Local (Param : R) is
   begin
      Y := Param.C;
   end Local;
begin
   Local (X);
end Init_Inline;
