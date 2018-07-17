package P is

   type T1 is record
      C : Integer;
   end record;

   type T2 is record
      C : T1;
   end record;

   type T3 is record
      C : T2;
   end record;

   protected PO is
      procedure Swap (X : in T1; Y : in out T1) with Pre => True;
   end;

   procedure Dummy;
end;
