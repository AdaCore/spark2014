pragma SPARK_Mode (Off);
package Pack
with Abstract_State => State
is
   procedure P (X : out Integer)
     with Global => State,
       Depends => (X => State);
end Pack;
