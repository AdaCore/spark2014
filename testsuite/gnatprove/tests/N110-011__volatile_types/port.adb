package body Port
   with SPARK_Mode => On
is
   procedure Read (X : out Integer) is
      Tmp : R0;
   begin
      Tmp := V; -- OK - whole record assignment from volatile object
      X := Tmp.F1;
   end Read;

end Port;

