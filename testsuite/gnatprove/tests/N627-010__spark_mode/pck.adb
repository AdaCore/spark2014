with Ada.Numerics.Discrete_Random;
package body Pck is
  use Ada;

  package Integer_Random is new Numerics.Discrete_Random
(Random_Integer);

  Random_Generator : Integer_Random.Generator;

  ------------
  -- Random --
  ------------

  function Random return Random_Integer is
  begin
     return Integer_Random.Random (Random_Generator);
  end Random;

end Pck;
