with Types;

package Usefoo
is

   procedure Do_Something (B : in out Types.Buffer;
                           R : out Integer)
   with
      Pre => B'Last <= Natural'Last and then B'Length > 1 and then B'First <= B'Last;

end Usefoo;
