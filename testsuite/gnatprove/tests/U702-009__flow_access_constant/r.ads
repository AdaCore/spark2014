package R with SPARK_Mode, Abstract_State => State, Initializes => State is
   procedure Dummy;
private
   type T is access Integer;
   C : constant T := new Integer'(0) with Part_Of => State;
end;
