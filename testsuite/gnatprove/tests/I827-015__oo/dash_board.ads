--  Making this unit SPARK requires use of container of indefinite values.
--  See N317-021
pragma SPARK_Mode(Off);

with Ada.Containers.Indefinite_Vectors;
with Instr; use Instr;
package Dash_Board is
  new Ada.Containers.Indefinite_Vectors (Positive, Instrument'Class);
