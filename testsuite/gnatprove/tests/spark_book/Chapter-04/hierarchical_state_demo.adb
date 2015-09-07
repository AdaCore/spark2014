with Hierarchical_State_Demo.A_Pack;
package body Hierarchical_State_Demo
   with SPARK_Mode    => On,
        Refined_State => (Top_State => (Count, A_Pack.State))
is
   Count : Natural := 0;

   procedure Do_Something (Value   : in out Natural;
                           Success :    out Boolean)
      with Refined_Global  => (In_Out  =>  (Count, A_Pack.State)),
           Refined_Depends => (Value        =>+ (Count, A_Pack.State),
                               Success      =>  (Value, Count, A_Pack.State),
                               Count        =>+ null,
                               A_Pack.State =>+ (Count, Value)) is
   begin
      Count := Count rem 128 + 1;
      if Count <= Value then
         Value := Count + (Value - Count) / 2;
      else
         Value := Value + (Count - Value) / 2;
      end if;
      A_Pack.A_Proc (Value);
      Success := Value /= 0;
   end Do_Something;
end Hierarchical_State_Demo;
