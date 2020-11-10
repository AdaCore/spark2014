package body P is
   protected body PO is
      procedure Swap (X : in T1; Y : in out T1) is
      begin
         null;
      end;
   end;

   procedure Dummy is
      A3 : T3 := (C => (C => (C => 0)));
      A2 : T2 renames A3.C;
      A1 : T1 renames A2.C;
   begin
      PO.Swap (A1, A3.C.C);
   end;
end;
