with P1;
with P3;
package P2 is
   type L_Cell;
   type List is access constant L_Cell;
   type L_Cell is record
      V1 : P1.I;
      V2 : P3.I;
      N  : List;
   end record;
end P2;
