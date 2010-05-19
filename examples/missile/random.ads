-- Random number generator
--
-- $Log: random.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/20 21:06:56  adi
-- Added null seed for init purposes
--
-- Revision 1.1  2003/08/20 20:28:24  adi
-- Initial revision
--
--
package Random is

   Max_Val : constant := 63001;
   type Value is range 0..Max_val;
   type Number is private;
   Null_Seed : constant Number;

   function Seed(V : Value) return Number;

   procedure Get(N : in out Number;
                 V : out Value);
   --# derives V, N from N;

private
   Max_Seed : constant := 971;
   type Seed_Range is range 0..Max_seed;
   --# assert Seed_Range'base is Integer;

   type Number is record
     S : Seed_Range;
     Last_V : Value;
   end record;

   Null_Seed : constant Number :=
     Number'(S => 0, Last_V => 0);

end Random;
