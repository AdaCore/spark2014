--  Case 4 - NO Elaborate pragma for Trouble
--           DOES have an Initializes aspect

with Trouble;
package Client4
  with SPARK_Mode => On,
       Initializes => (C => Trouble.V)
is
   C : constant Integer := (Trouble.V + 1);
end Client4;
