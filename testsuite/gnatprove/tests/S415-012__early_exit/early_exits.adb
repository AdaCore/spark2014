procedure Early_Exits with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Acc is not null access Integer;
   type Two_Acc is record
      F, G : Int_Acc;
   end record;

   procedure P1 (X : in out Two_Acc) with
     Pre  => X.F.all = X.G.all,
     Post => (X.F.all = - 1 and X.G.all = Integer'Last) or X.F.all = X.G.all
   is
   begin
      declare
         Y : access Integer := X.F;
      begin
         L1: for I in 1 .. 10 loop
            declare
               Z : access Integer := X.G;
            begin
               for I in 1 .. 15 loop
                  if Z.all = Integer'Last then
                     Y.all := -1;
                     exit L1;
                  end if;
                  exit when Z.all = 0;
                  Z.all := Z.all + 1;
               end loop;
            end;
            Y.all := X.G.all;
         end loop L1;
      end;
   end P1;

   procedure P2 (X : in out Two_Acc) with
     Post => X.F.all = X.G.all and
     (if X.F.all'Old in - 1 .. 1 then X.F.all = 0 else X.F.all = X.G.all'Old)
   is
   begin
      declare
         Y : access Integer := X.F;
      begin
         Y.all := Y.all / 2;
         declare
            Z : access Integer := X.G;
         begin
            if Y.all = 0 then
               Z.all := 0;
               return;
            end if;
         end;
         Y.all := X.G.all;
         if Y.all < 0 then
            return;
         end if;
      end;
   end P2;
begin
   null;
end Early_Exits;
