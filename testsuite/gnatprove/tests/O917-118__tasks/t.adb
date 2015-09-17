package body T
  with SPARK_Mode
is
   X : Integer;
   procedure Update (X : in out Integer) is
   begin
      X := 0;
   end Update;
   task body TT is
   begin
      loop
         Update (X);
      end loop;
   end TT;
end T;
