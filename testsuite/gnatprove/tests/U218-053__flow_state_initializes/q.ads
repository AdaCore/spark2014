with P1;
package Q is
   task type TT with Global => (In_Out => P1.State1);
   T1, T2 : TT;
end;
