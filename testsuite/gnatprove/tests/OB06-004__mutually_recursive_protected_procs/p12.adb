package body P12 is
   package body P1 with
     Refined_State => (State1 => PO1)
   is

      protected PO1 is
         procedure Dummy1 with
           Global => (In_Out => P2.State2);
      end;

      protected body PO1 is
         procedure Dummy1 is
         begin
            P2.Proxy2;
         end;
      end;

      procedure Proxy1 is
      begin
         PO1.Dummy1;
      end;

   end;

   package body P2 with
     Refined_State => (State2 => PO2)
   is

      protected PO2 is
         procedure Dummy2;
      end;

      protected body PO2 is
         procedure Dummy2 is
         begin
            P1.Proxy1;
         end;
      end;

      procedure Proxy2 is
      begin
         PO2.Dummy2;
      end;

   end;
end P12;
