with Ext; use Ext;

procedure Test with SPARK_Mode is

   X1 : P1.R;
   Y1 : P1.R := P1.F (X1);

   X2 : P2.R;
   Y2 : P2.R := P2.F (X2);

   X3 : P3.R;
   Y3 : P3.R := P3.F (X3);

begin
   null;
end Test;
