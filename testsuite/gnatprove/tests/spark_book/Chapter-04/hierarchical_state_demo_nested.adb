package body Hierarchical_State_Demo_Nested
   with SPARK_Mode    => On,
        Refined_State => (Top_State => (Count, A_Pack.State))
is
   Count : Natural := 0;

   package A_Pack
      with Abstract_State => State,
           Initializes    => State
   is
      procedure A_Proc (Test : in out Natural)
         with Global   => (In_Out =>  State),
              Depends  => (Test   =>+ State,
                           State  =>+ Test);
   end A_Pack;
   -------------------------------------------
   package body A_Pack
      with Refined_State => (State => Total)
   is
      Total : Natural := 0;

      procedure A_Proc (Test : in out Natural)
         with Refined_Global  => (In_Out => Total),
              Refined_Depends => ((Test  =>+ Total,
                                   Total =>+ Test)) is
      begin
         if Total > Natural'Last - Test   then
            Total := abs (Total - Test);
         else
            Total := Total + Test;
         end if;
         Test := Total;
      end A_Proc;
   end A_Pack;
   -------------------------------------------

   procedure Do_Something (Value   : in out Natural;
                           Success :    out Boolean)
      with Refined_Global  => (In_Out  =>  (Count, A_Pack.State)),
           Refined_Depends => (Value        =>+ (Count, A_Pack.State),
                               Success      =>  (Value, Count, A_Pack.State),
                               Count        =>+ null,
                               A_Pack.State =>+ (Count, Value)) is
   begin
      Count := Count rem 128;
      if Count <= Value then
         Value := Count + (Value - Count) / 2;
      else
         Value := Value + (Count - Value) / 2;
      end if;
      A_Pack.A_Proc (Value);
      Success := Value /= 0;
   end Do_Something;
end Hierarchical_State_Demo_Nested;
