with P;

package Q is
   task type TT with Global => (In_Out => P.State);
end;
