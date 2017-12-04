with P;
package Q is
   type DT is limited private;
   type DP is limited private;
private
   type DT is new P.TT;
   type DP is new P.PT;
end;
