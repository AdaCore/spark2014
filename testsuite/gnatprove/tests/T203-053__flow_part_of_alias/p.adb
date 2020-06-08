package body P is

   procedure Swap (A, B : in out T) is
      Tmp : T := A;
   begin
      A := B;
      B := Tmp;
   end;

   protected body PT is
      procedure Proc is
      begin
         Swap (Part, Part);
      end;
   end;
end;
