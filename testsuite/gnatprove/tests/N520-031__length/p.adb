package body P
   with SPARK_Mode
is

   procedure Swap(V: in out Vect; I, J : Natural) is
      Aux: Integer;
   begin
      Aux := V(I);
      V(I) := V(J);
      V(J) := Aux;
   end Swap;

end P;
