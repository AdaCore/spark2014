with Interfaces; use Interfaces;

package U
with SPARK_Mode => On
is

   type Sequence is array (Natural range <>) of Unsigned_8
     with Dynamic_Predicate => Sequence'First = 0;

   procedure Loop_Test (Sq : in out Sequence);

end U;
