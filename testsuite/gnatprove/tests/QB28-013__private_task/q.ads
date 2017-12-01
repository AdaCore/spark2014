with P;
package Q is
   type DT is new P.TT;
   type DP is new P.PT;

   TTX : P.TT;
   PTX : P.PT;
   TTY : DT;
   PTY : DP;
end;
