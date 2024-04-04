procedure Main2 with SPARK_Mode is
   type Small is record
      A : Integer;
   end record;
   type Large is record
      X : Integer;
      Y : Integer;
      Z : Integer;
      T : Integer;
      U : Integer;
      V : Integer;
      W : Integer;
   end record;
   X : Small;
   Y : Large with Import, Address => X'Address;
   Z : Large := (others => 0);
begin
   --  Y.W := 0; -- Program_Error Main @ 44 : X.W
   Y := (others => 0); -- Constraint_Error Flow_Types.Flow_Id_Sets.Delete: attempt to delete element not in set
   --  Y := Z; -- Assert_Failure flow-control_flow_graph.adb:1791
end;
