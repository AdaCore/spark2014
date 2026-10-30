generic
   type Real is digits <>;
   Sign : Real;
package Zero_Powers with SPARK_Mode is
   procedure Minus_One (Y : out Real);
   procedure Minus_Two (Y : out Real);
   procedure Minus_Three (Y : out Real);
end Zero_Powers;
