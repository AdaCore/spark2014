Package imports with
  Spark_Mode,
  Abstract_State => imp_state
is
   pragma Elaborate_Body;

   Function get( A : integer ) return float;
   Pragma import(Convention => Ada,
                 Entity => get,
                 Link_Name=>"imports__get");

   procedure put( A : integer; v : float );
   Pragma import(Convention => Ada,
                 Entity => put,
                 Link_Name=>"imports__put");
end imports;
