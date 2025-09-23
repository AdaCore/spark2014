with P;

package body Tasks1 is

   task body TA is
   begin
      loop
         P.X.C1.Proc1;
         P.X.C2.Proc2;
         P.X.C3.Proc3;
         P.X.C4.Proc1;
      end loop;
   end;

   task body TB is
   begin
      loop
         P.X.C1.Proc1;
         P.X.C2.Proc2;
         P.X.C3.Proc3;
         P.X.C4.Proc1;
      end loop;
   end;

end Tasks1;
