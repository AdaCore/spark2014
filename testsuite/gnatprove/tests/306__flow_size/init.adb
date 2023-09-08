procedure Init
  with SPARK_Mode
is
   type T is record
      D : Integer;
   end record;
   X : T;
begin
   pragma Assert (X'Size = 32);
end Init;
