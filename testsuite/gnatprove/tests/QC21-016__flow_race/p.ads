package P is

   protected PO is
      procedure Dummy (Arg : Integer) with Pre => Arg = 0;
   end;

   task type TT;
   T1, T2 : TT;
end;
