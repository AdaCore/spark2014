with P1;
package Q is
   Other : Integer := 0;
   task type TT with Global => (In_Out => (P1.State1, Other));
   --  The desired result is to emit separate reports of possible data
   --  races when accessing P1.State1 and Other.
   T1, T2 : TT;
end;
