package P with SPARK_Mode, Abstract_State => State, Initializes => State is
   procedure Dummy;
private
   X : constant Integer := 0 with Part_Of => State;    --  Error
   package Q with SPARK_Mode => Off is
     Y : constant Integer := 0 with Part_Of => State;  --  OK (as not in SPARK)
   end;
end;
