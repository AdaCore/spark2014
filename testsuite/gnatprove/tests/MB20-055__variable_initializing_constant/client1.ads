--  Case 1 - NO Elaborate pragma for Trouble
--           NO Initializes aspect

with Trouble;
package Client1
  with SPARK_Mode => On
is
   C : constant Integer := (Trouble.V + 1);
end Client1;
