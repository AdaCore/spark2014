--  Case 2 - Elaborate pragma for Trouble
--           NO Initializes aspect

with Trouble;
pragma Elaborate (Trouble);
package Client2
  with SPARK_Mode => On
is
   C : constant Integer := (Trouble.V + 1);
end Client2;
