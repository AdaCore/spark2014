with Interfaces; use Interfaces;

package Array_Conv is
   type M is mod 142;

   type A1 is array (Unsigned_8 range 0 .. 100) of Integer;
   type A2 is array (Unsigned_8 range 1 .. 101) of Integer;
   type A3 is array (Unsigned_16 range 0 .. 100) of Integer;
   type A4 is array (Unsigned_16 range 1 .. 101) of Integer;
   type A5 is array (M range 0 .. 100) of Integer;
   type A6 is array (M range 1 .. 101) of Integer;

   procedure Convert (X1 : in out A1; X2 : in out A2;
                      X3 : in out A3; X4 : in out A4;
                      X5 : in out A5; X6 : in out A6);
end Array_Conv;
