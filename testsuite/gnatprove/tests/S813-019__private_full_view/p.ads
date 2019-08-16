with Ada.Strings.Unbounded;

package P with SPARK_Mode is

   type T is new Ada.Strings.Unbounded.Unbounded_String;

   type My_A is array (Positive range <>) of T;
end P;
