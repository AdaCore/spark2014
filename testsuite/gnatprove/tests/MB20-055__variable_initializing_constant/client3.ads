--  Case 3 - Elaborate pragma for Trouble
--           DOES have an Initializes aspect

with Trouble;
pragma Elaborate (Trouble);
package Client3
  with SPARK_Mode => On,
       Initializes => (null => Trouble.V)
is
   C : constant Integer := (Trouble.V + 1);   
end Client3;
