procedure Test_Dynamic_Property with SPARK_Mode is
   procedure P (C : Positive) is
      subtype Pos_Dynamic_Discrete is Integer range -C .. C with
        Static_Predicate => Pos_Dynamic_Discrete /= 0;
      S : Pos_Dynamic_Discrete := 1;
      T : Pos_Dynamic_Discrete := C - 1;
   begin
      null;
   end P;
begin
   P (5);
   P (1);
end Test_Dynamic_Property;
