with Ada.Containers.Formal_Vectors;
package FVectors is
   type Index is range 1 .. 100;
   package Vec is new Ada.Containers.Formal_Vectors (Index, Integer);
end FVectors;
