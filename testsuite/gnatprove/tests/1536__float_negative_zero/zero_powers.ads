generic
   type Real is digits <>;
   Sign : Real;
package Zero_Powers with SPARK_Mode is
   procedure Minus_One (Y : out Real);
   procedure Minus_Two (Y : out Real);
   procedure Minus_Three (Y : out Real);
   procedure Minus_Four (Y : out Real);
   procedure Named_Exponent (Y : out Real);
   procedure Dynamic_Exponent (N : Integer; Y : out Real)
     with Pre => N < 0;
   procedure Zero_Exponent (Y : out Real);
   procedure Plus_One (Y : out Real);
   procedure Plus_Two (Y : out Real);
   procedure Plus_Three (Y : out Real);
   procedure Divide (Y : out Real);
   procedure Remainder (Y : out Real);
   procedure Nonzero (Y : out Real);
   procedure Underflow (Y : out Real);
end Zero_Powers;
