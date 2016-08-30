procedure Invariant_Test is
  type T1 is tagged record
     Aaa : Natural := 0;
     Bbb : Natural := 100;
  end record;

  procedure Swap_T1 (X1 : in out T1) is
  begin
     X1 := (Aaa => X1.Bbb, Bbb => X1. Aaa);
  end;

  generic
     type D is new T1 with private;
  procedure Swap_View_Conversion (X : in out D);
  procedure Swap_View_Conversion (X : in out D) is
  begin
     Swap_T1 (T1 (X)); -- a view conversion -- no type invariant check here
  end;

  package Pkg is
     type T2 is private;
  private
     type T2 is new T1 with null record
       with Type_Invariant => T2.Aaa < T2.Bbb;

     package Nested is
        procedure Swap_T2 is new Swap_View_Conversion (T2);
     end;
   end;

   package body pkg is
      Y : T2;
   begin
      Nested.Swap_T2 (Y);
      pragma Assert (Y.Aaa = 100);
   end;
begin null; end;
