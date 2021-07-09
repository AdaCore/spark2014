generic
package Gen_State with SPARK_Mode, Abstract_State => State is
   procedure Run with Global  => (Output => State),
                      Depends => (State => null);
private
   Error : Boolean with Part_Of => State;
end Gen_State;
