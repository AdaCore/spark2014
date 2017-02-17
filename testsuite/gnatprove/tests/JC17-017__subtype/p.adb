package body P is
   -- pragma Annotate (gnatprove, Force);

   procedure Proc (X, Y : Integer)
     with Pre => X <= Y;

   procedure Proc (X, Y : Integer) is
      subtype S is Integer range X .. Y;
      Tmp_S : S;

      procedure Proc_Loop (X, Y : Integer) is
         Tmp_S : Integer;
      begin
         Tmp_S := X;

         for V in S range 1 .. Y - X loop
            Tmp_S := Tmp_S + 1;
         end loop;
      end;
   begin
      Tmp_S := X;

      for V in Integer range 1 .. Y - X loop
         Tmp_S := Tmp_S + 1;
      end loop;
   end;

   procedure Proc_Loop (X, Y : Integer) is
      Tmp_S : Integer;
   begin
      Tmp_S := X;

      for V in Integer range 1 .. Y - X loop
         Tmp_S := Tmp_S + 1;
      end loop;
   end;


end;
