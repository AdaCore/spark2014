--  Values (such as integers, reals, complex numbers, strings, etc.)
--  manipulated by SDC.

with Stack; use Stack;
with Types; use Types;

package Values
with SPARK_Mode => On
is

   function To_String (V : Value) return String;
   --  Returns a String representation of the Value.

   function Read (Word : String) return Value;
   --  If Word contains a value, the value is returned, otherwise
   --  Except.User_Error is raised.

   procedure Process (V : Value)
   with Pre => not Stack.Full;
   --  Processes a Value.

end Values;
