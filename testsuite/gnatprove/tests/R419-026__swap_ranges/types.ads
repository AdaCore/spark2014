-- a simple package to hold all needed types for SPARK by example

package Types is
   type T is new Integer;
   type T_Arr is array (Positive range <>) of T;

end Types;
