pragma Extensions_Allowed (On);

procedure Test with SPARK_Mode
is
   generic
      type T is private;
      with function Is_Reclaimed (X : T) return Boolean is (True);
   package G is
   end G;

   package I is new G (Integer);
begin
   null;
end;
